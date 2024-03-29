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
  

public class ThreadLocalCommand : ProofCommand
{
	public string procname;
	public string varname;
	
	private static int nextConstId;

	public ThreadLocalCommand(string pname, string vname)
		: base("thrlocal")
	{
		this.procname = pname;
		this.varname = vname;
		
		desc = "thrlocal" + " " + this.procname + " " + this.varname;
	}
	
	override public bool Run(ProofState proofState) {
	
		ProcedureState procState = proofState.GetProcedureState(procname);
		Debug.Assert(!procState.IsReduced || procState.IsPublic);

		GlobalVariable errVar = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "errx", BasicType.Bool));
		IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
		proofState.AddAuxVar((GlobalVariable)errVar);
		IdentifierExpr perrExpr = proofState.GetPrimedExpr(errExpr.Decl);
		
		//-----------------------------------------------		
		Variable var = (Variable) procState.localVars[varname];
		
		procState.thrLocalVars.Add(var);
		
		IdentifierExpr varExpr = new IdentifierExpr(Token.NoToken, var);
        Expr assertAux = Expr.Eq(Expr.Select(proofState.ownerMapExpr, varExpr),
								  ProofState.GetInstance().tidExpr);
		
		// add to requires
		procState.impl.Proc.Requires.Add(new Requires(false, assertAux));
		// add assume to the enter block
		APLBlock enterAtomicBlock = (APLBlock) procState.LookupAPLBlockStarts(procState.impl.Blocks[0]);
		Debug.Assert(enterAtomicBlock.startBlock.Label == "EnterBlock");
		enterAtomicBlock.InstrumentEntry(new CmdSeq(new AssumeCmd(Token.NoToken, assertAux)));

        Expr thisRely = Expr.Imp(Expr.Eq(Expr.Select(proofState.ownerMapExpr, varExpr), ProofState.GetInstance().tidExpr),
                                  Expr.Eq(Expr.Select(proofState.GetPrimedExpr(proofState.ownerMapExpr.Decl), varExpr), ProofState.GetInstance().tidExpr));
	
		procState.RecomputeTransitionPredicates();
		
		RelyGuarantee rg = new RelyGuarantee(proofState.Invariant,
											  Expr.And(Expr.And(proofState.Rely, thisRely), Expr.Eq(errExpr, perrExpr)),
											  proofState.Guar);
		// now annotate the procedure
		Hashtable labelToBlock = new Hashtable();
		foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
			labelToBlock.Add(atomicBlock.Label, atomicBlock);
		}
	
		bool done = false;
		while(!done) {
			procState.ClearTransitionPredicates();
			
			foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
				if(labelToBlock.Contains(atomicBlock.Label)) {
                    Expr labeledAssertAux = LabeledExprHelper.NegAuxAssert(atomicBlock, assertAux);
					Expr labeledAnnot = Expr.Or(Expr.And(assertAux, Expr.Eq(errExpr, perrExpr)),
												 Expr.And(labeledAssertAux, Expr.Eq(perrExpr, Expr.True)));
					atomicBlock.TransitionPredicate = Expr.And(atomicBlock.TransitionPredicate, labeledAnnot);
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
				
				foreach(AtomicBlock atomicBlock in labelToBlock.Values) {
					Output.LogLine("Annotating atomic block " + atomicBlock.startBlock.Label);
					
					AssumeCmd assumeCmd = new AssumeCmd(Token.NoToken, assertAux);
					atomicBlock.InstrumentEntry(new CmdSeq(assumeCmd));
				}
			} // end if
		} // end while

		//----------------------------------------------------------
		
		// done. clean up
		procState.ClearTransitionPredicates();
		proofState.rely.Add(thisRely);
		
		//----------------------------------------------------------
		proofState.RemoveAuxVar(errVar);
		
		return false;		
	}
	
} // end class ThreadLocalCommand


} // end namespace QED