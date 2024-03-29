/*

****************************************************************************

QED: A Calculator for Atomic Actions
Copyright (C) 2008  Koç University, İstanbul, Turkey

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

****************************************************************************

*/

namespace QED {

using System;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using Microsoft.Boogie;
using BoogiePL;
using System.Diagnostics;
  

public class ReachCommand : ProofCommand
{
	string procname;
	
	public ReachCommand(string name)
		: base("reach")
	{
		this.procname = name;
		desc = "reach " + name;
	}
	
	override public bool Run(ProofState proofState) {
		ProcedureState procState = proofState.GetProcedureState(procname);
		
		if(!procState.IsReduced) {
			DoRun(proofState, procState);
		}
		
		return false;
	}
	
	protected void DoRun(ProofState proofState, ProcedureState procState) {
		Debug.Assert(!procState.IsReduced);
		
		RelyGuarantee rg = new RelyGuarantee(proofState.Invariant, proofState.Rely, proofState.Guar);
		
		GlobalVariable errVar = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "errx", BasicType.Bool));
		IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
		proofState.AddAuxVar(errVar);
		IdentifierExpr perrExpr = proofState.GetPrimedExpr(errVar);
		
		rg.Rely = Expr.And(rg.Rely, Expr.Eq(errExpr, perrExpr));
		
		Output.LogLine("Reach: Checking procedure dead blocks: " + procState.impl.Name);
	
		Hashtable labelToBlock = new Hashtable();
		foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
			labelToBlock.Add(atomicBlock.Label, atomicBlock);
		}
	
		bool done = false;
		while(!done) {
			procState.ClearTransitionPredicates();
			
			foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
				if(labelToBlock.Contains(atomicBlock.Label)) {
                    Expr labeledAssertAux = LabeledExprHelper.NegAuxAssert(atomicBlock, Expr.Eq(perrExpr, Expr.False));
					atomicBlock.TransitionPredicate = Expr.And(atomicBlock.TransitionPredicate, labeledAssertAux);
				} else {
					atomicBlock.TransitionPredicate = Expr.And(atomicBlock.TransitionPredicate, Expr.Iff(perrExpr, errExpr));
				}
			}
			
			// now check
			if(!rg.CheckProcedure(proofState, procState, Expr.Not(errExpr), Expr.Not(perrExpr))) {
				// remove the failed assertions
				foreach(string label in Prover.GetInstance().GetErrorLabels()) {
					// label may not point to an atomic block
					if(labelToBlock.Contains(label)) {
						AtomicBlock atomicBlock = (AtomicBlock)labelToBlock[label];
						// Output.LogLine("Unlabeled block " + atomicBlock.startBlock.Label);
						labelToBlock.Remove(label);
					}
				}
			} else {
				// now do code annotation
				done = true;
				
				Output.LogLine("The following blocks are unreachable!");
				foreach(AtomicBlock atomicBlock in labelToBlock.Values) {
					Output.LogLine("\t Unreachable atomic block: " + atomicBlock.Label);
				}
			}
		} // end while
		
		proofState.RemoveAuxVar(errVar);
	}
	
} // end class ReachCommand


} // end namespace QED