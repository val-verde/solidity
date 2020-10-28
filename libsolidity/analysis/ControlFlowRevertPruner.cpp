/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libsolidity/analysis/ControlFlowRevertPruner.h>

#include <libsolutil/Algorithms.h>

namespace solidity::frontend
{

void ControlFlowRevertPruner::run()
{
	m_cfg.iterateFunctionFlows([&](FunctionDefinition const& _function, ContractDefinition const* _contract, FunctionFlow const&) {
			collectCalls(_function, _contract);
	});

	// In the second iteration we process anything left pending
	removeRevertingNodes();
}

FunctionDefinition const* ControlFlowRevertPruner::resolveCall(FunctionCall const& _functionCall, ContractDefinition const* _contract)
{
	auto const& functionType = dynamic_cast<FunctionType const&>(
		*_functionCall.expression().annotation().type
	);

	if (!functionType.hasDeclaration())
		return nullptr;

	auto const& unresolvedFunctionDefinition =
		dynamic_cast<FunctionDefinition const&>(functionType.declaration());

	if (auto const* memberAccess = dynamic_cast<MemberAccess const*>(&_functionCall.expression()))
	{
		if (*memberAccess->annotation().requiredLookup == VirtualLookup::Super)
		{
			if (auto const typeType = dynamic_cast<TypeType const*>(memberAccess->expression().annotation().type))
				if (auto const contractType = dynamic_cast<ContractType const*>(typeType->actualType()))
				{
					solAssert(contractType->isSuper(), "");
					ContractDefinition const* superContract = contractType->contractDefinition().superContract(*_contract);

					return &unresolvedFunctionDefinition.resolveVirtual(
						*_contract,
						superContract
					);
				}
		}
		else
		{
			solAssert(*memberAccess->annotation().requiredLookup == VirtualLookup::Static, "");
			return &unresolvedFunctionDefinition;
		}
	}
	else if (auto const* identifier = dynamic_cast<Identifier const*>(&_functionCall.expression()))
	{
		solAssert(*identifier->annotation().requiredLookup == VirtualLookup::Virtual, "");
		return &unresolvedFunctionDefinition.resolveVirtual(*_contract);
	}

	return &unresolvedFunctionDefinition;
}

void ControlFlowRevertPruner::removeRevertingNodes()
{
	std::set<CFG::FunctionContractTuple> pending_functions = keys(m_functions);

	while (!pending_functions.empty())
	{
		CFG::FunctionContractTuple item = *pending_functions.begin();
		pending_functions.erase(pending_functions.begin());

		auto& revertState = m_functions[item];

		auto previousState = revertState;
		revertState = RevertState::AllPathsRevert;

		FunctionFlow const& functionFlow = m_cfg.functionFlow(*item.function, item.contract);

		solidity::util::BreadthFirstSearch<CFGNode*>{{functionFlow.entry}}.run(
			[&](CFGNode* _node, auto&& _addChild) {
				if (_node == functionFlow.exit)
					revertState = RevertState::HasNonRevertingPath;

				for (auto const* functionCall: _node->functionCalls)
				{
					auto const* resolvedFunction = resolveCall(*functionCall, item.contract);

					if (
						resolvedFunction == nullptr ||
						resolvedFunction == item.function ||
						!resolvedFunction->isImplemented()
					)
						continue;

					auto const* mostDerivedContract = item.contract;
					if (resolvedFunction->isFree())
						mostDerivedContract = nullptr;
					else if (resolvedFunction->annotation().contract->isLibrary())
						mostDerivedContract = resolvedFunction->annotation().contract;

					if (m_functions.at({mostDerivedContract, resolvedFunction}) == RevertState::AllPathsRevert)
						_node->exits = {functionFlow.revert};
				}

				for (CFGNode* exit: _node->exits)
					_addChild(exit);
		});

		// Mark all functions depending on this one as modified again
		if (previousState != revertState)
			for (auto& nextItem: m_calledBy[item.function])
				// Ignore different most derived contracts in dependent callees
				if (
					item.contract == nullptr ||
					nextItem.contract == nullptr ||
					nextItem.contract == item.contract
				)
					pending_functions.insert(nextItem);
	}
}

void ControlFlowRevertPruner::collectCalls(FunctionDefinition const& _function, ContractDefinition const* _mostDerivedContract)
{
	FunctionFlow const& functionFlow = m_cfg.functionFlow(_function, _mostDerivedContract);

	CFG::FunctionContractTuple pair{_mostDerivedContract, &_function};

	solAssert(m_functions.count(pair) == 0, "");
	m_functions[pair] = RevertState::HasNonRevertingPath;

	solidity::util::BreadthFirstSearch<CFGNode*>{{functionFlow.entry}}.run(
		[&](CFGNode* _node, auto&& _addChild) {
			for (auto const* functionCall: _node->functionCalls)
				m_calledBy[resolveCall(*functionCall, _mostDerivedContract)].insert(pair);

			for (CFGNode* exit: _node->exits)
				_addChild(exit);
	});
}

}
