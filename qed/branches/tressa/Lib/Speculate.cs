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
using Type = Microsoft.Boogie.Type;
  

public class SpeculateCommand : ProofCommand
{
	List<Expr> predicates;
	Expr rely;
	Expr guar;
	
	public SpeculateCommand(Expr r, Expr g, List<Expr> preds)
		: base("speculate")
	{
		this.predicates = preds;
		this.rely = r;
		this.guar = g;
		
		desc = "speculate ";
		desc += Output.ToString(preds[0]);
		for(int i = 1, n = preds.Count; i < n; ++i) {
			desc += Output.ToString(preds[i]);
		}
	}
	
	override public bool Run(ProofState proofState) {
		
		DoRun(proofState);
		
		return false;
	}
	
	public Set<ProcedureState> DoRun(ProofState proofState) {
	
		foreach(Expr pred in predicates) {
			proofState.ResolveTypeCheckExpr(pred, false);
		}
		
		Set<ProcedureState> annotatedProcedures = new Set<ProcedureState>();
		
		GlobalVariable errVar = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "errx", BasicType.Bool));
		proofState.AddAuxVar((GlobalVariable)errVar);
		IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
		IdentifierExpr perrExpr = ProofState.GetInstance().GetPrimedExpr(errVar);
		
		RelyGuarantee rg = new RelyGuarantee(proofState.Invariant,
											 Expr.And(Expr.And(proofState.Rely, this.rely), Expr.Eq(errExpr, perrExpr)),
											 Expr.And(proofState.Guar, this.guar));
		
		SpeculationSet speculationSet = new SpeculationSet(errExpr, perrExpr);
		foreach(ProcedureState procState in proofState.procedureStates.Values) {
		
			if((!procState.IsReduced) || procState.IsPublic) {
			
				Output.LogLine("Speculating for procedure: " + procState.impl.Name);
				
				foreach(Expr pred in predicates) {
					speculationSet.AddForEntry(pred, procState);
					speculationSet.AddForExit(pred, procState);
				}
				
			}
		} // end foreach procedure
		
		annotatedProcedures = AnnotateProcedures(proofState, speculationSet, rg, errExpr, perrExpr);
		
		proofState.RemoveAuxVar(errVar);
		
		return annotatedProcedures;
	}
	
	public Set<ProcedureState> AnnotateProcedures(ProofState proofState, SpeculationSet speculationSet, RelyGuarantee rg, IdentifierExpr errExpr, IdentifierExpr perrExpr) {
		
		bool done = false;
		
		while(!done) {
		
			foreach(ProcedureState procState in proofState.procedureStates.Values) {
		
				if((!procState.IsReduced) || procState.IsPublic) {
				
					procState.ClearTransitionPredicates();
			
					speculationSet.AnnotateTransitions();
			
					Expr precond = Expr.And(Expr.Not(errExpr), speculationSet.GetAnnotatedPrecond(procState));
					Expr postcond = Expr.And(Expr.Not(perrExpr), speculationSet.GetAnnotatedPostcond(procState));
					
					// now check			
					if(!rg.CheckProcedure(proofState, procState, precond, postcond)) {
						// remove the failed assertions
						speculationSet.Disable(Prover.GetInstance().GetErrorLabels());
					} else {
						done = true;
						// now do code annotation
						speculationSet.AnnotateCodes();
					} // end if
				}//end if
			} // end foreach procedure
			
		} // end while
		
		return speculationSet.GetAnnotatedProcs();
	}
	
} // end class SpeculateCommand


} // end namespace QED
