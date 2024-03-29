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
  

public class RefineProgressCommand : RefineCommand
{
	public List<Expr> syncPredicates;
	
	public Variable auxVar;
	
	public string auxVarName;
	
	private Expr inv;
	
	private Expr rely;
	
	private Expr guar;
	
	public RefineProgressCommand(List<Expr> predicates, string auxname)
		: base()
	{
		this.syncPredicates = new List<Expr>(predicates);
		this.auxVarName = auxname;
		
		desc = "refine progress " + auxVarName + " ";
		
		for(int i = 0, n = this.syncPredicates.Count; i < n; ++i) {
			desc += Output.ToString(syncPredicates[i]) + "#";
		}
	}	
	
	override protected void AnnotateProgram(ProofState proofState) {
		
		IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
		IdentifierExpr perrExpr = ProofState.GetInstance().GetPrimedExpr(errVar);
		
		IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVar);
		IdentifierExpr auxPrimeExp = ProofState.GetInstance().GetPrimedExpr(auxVar);
		
		AnnotationSet annotationSet;
		Set<AtomicBlock> annotatedAuxBlocks;
		Set<AtomicBlock> annotatedZeroBlocks;
		
		for(int i = 0, n = this.syncPredicates.Count; i < n; ++i) {
			Expr syncPredicate = this.syncPredicates[i];
		
			Expr assertAux = Expr.Eq(auxExp, Expr.Literal(i));
			Expr assertAuxPrime = Expr.Eq(auxPrimeExp, Expr.Literal(i));
			
			rg.Rely = Expr.And(rg.Rely,
							   Expr.Eq(errExpr, perrExpr));
		
			foreach(ProcedureState procState in proofState.procedureStates.Values) {
			
				if((!procState.IsReduced) || procState.IsPublic) {
				
					Output.LogLine("Refine: Annotating procedure: " + procState.impl.Name);
					//----------------------------------------------------------------------
					annotationSet = new AnnotationSet(errExpr, perrExpr);
					
					// entry assume aux = tid
					foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
						annotationSet.AddForEntry(assertAux, new AssumeCmd(Token.NoToken, assertAux), atomicBlock);				
					}
					
					annotatedAuxBlocks = AnnotateProcedure(proofState, procState, annotationSet);
					
					//----------------------------------------------------------------------
					annotationSet = new AnnotationSet(errExpr, perrExpr);
					
					// exit assign aux = tid
					foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
						annotationSet.AddForExit(assertAuxPrime, AssignCmd.SimpleAssign(Token.NoToken, auxExp, Expr.Literal(i)), atomicBlock);
					}
					annotationSet.Disable(annotatedAuxBlocks);
					
					AnnotateProcedure(proofState, procState, annotationSet);
							
				}
			} // end foreach procedure
		}
	}
	
	override protected void StartRefine(ProofState proofState) {
		for(int i = 0, n = this.syncPredicates.Count; i < n; ++i) {
			proofState.ResolveTypeCheckExpr(this.syncPredicates[i], false);
		}
		
		foreach(ProcedureState procState in proofState.procedureStates.Values) {
			procState.RecomputeTransitionPredicates();
		}
		
		// create the auxiliary variable
		auxVar = proofState.AddOrGetAuxVar(auxVarName, BasicType.Int);
		IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVar);

		IdentifierExpr auxPrimeExp = proofState.GetPrimedExpr(auxVar);
		
		this.errVar = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "errx", BasicType.Bool));
		IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
		proofState.AddAuxVar((GlobalVariable)errVar);
		IdentifierExpr perrExpr = proofState.GetPrimedExpr(errExpr.Decl);
		
		this.inv = Expr.And(Expr.Ge(auxExp, Expr.Literal(0)),
							Expr.Le(auxExp, Expr.Literal(this.syncPredicates.Count-1)));
		
		for(int i = 0, n = this.syncPredicates.Count; i < n; ++i) {
			this.inv = Expr.And(this.inv,
								Expr.Iff(syncPredicates[i], Expr.Eq(auxExp, Expr.Literal(i))));
		}
		
		this.guar = this.rely = Expr.Ge(auxPrimeExp, auxExp);
		
		this.rg = new RelyGuarantee(Expr.And(proofState.Invariant, this.inv),
									Expr.And(Expr.And(proofState.Rely, this.rely), Expr.Eq(errExpr, perrExpr)),
									Expr.And(proofState.Guar, guar));
	}
	
	override protected Expr ComputeTransitionAnnotation() {
		
		return Expr.True; // no need for extra annotation for transitions
	}
	
	override protected bool CheckValidity(ProofState proofState) {
	
		IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
		IdentifierExpr perrExpr = ProofState.GetInstance().GetPrimedExpr(errVar);
		
		Expr annotExpr = ComputeTransitionAnnotation();		
		IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVar);
		
		// first add regular annotations
		foreach(ProcedureState procState in proofState.procedureStates.Values) {
			if((!procState.IsReduced) || procState.IsPublic) {
				Output.LogLine("Refine: Checking procedure: " + procState.impl.Name);
				procState.ClearTransitionPredicates();
				
				foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
					atomicBlock.TransitionPredicate = Expr.And(Expr.And(atomicBlock.TransitionPredicate, annotExpr), Expr.Iff(perrExpr, errExpr));
				}
			}
		}
		
		for(int i = 0, n = this.syncPredicates.Count; i < n; ++i) {
			Expr syncPredicate = this.syncPredicates[i];
		
			// now add annotations for preconditions
			Expr assertAux = Expr.Eq(auxExp, Expr.Literal(i));
			
			foreach(ProcedureState procState in proofState.procedureStates.Values) {
				if((!procState.IsReduced) || procState.IsPublic) {
					if(Prover.GetInstance().CheckValid(Expr.Imp(Expr.And(proofState.Invariant, procState.Requires), syncPredicate))) {
						
						AddPreCondForProc(procState, assertAux);
						
						// add assertion to call blocks
						foreach(CallBlock callBlock in procState.callerBlocks) {
                            Expr labeledAssertAux = LabeledExprHelper.NegAuxAssert(callBlock, assertAux);
							Expr labeledAnnot = Expr.Or(Expr.And(assertAux, Expr.Eq(errExpr, perrExpr)),
														 Expr.And(labeledAssertAux, Expr.Eq(perrExpr, Expr.True)));
							callBlock.TransitionPredicate = Expr.And(Expr.And(callBlock.RecomputeTransitionPredicate(), annotExpr), labeledAnnot);
						}
					}
				}
			}
		}
		
		bool result = true;
		
		// finally check
		foreach(ProcedureState procState in proofState.procedureStates.Values) {
			if((!procState.IsReduced) || procState.IsPublic) {
				// now check
				Expr precond = Expr.And(PreCondForProc(procState), Expr.Not(errExpr));
				Expr postcond = Expr.Not(perrExpr);
				if(!rg.CheckProcedure(proofState, procState, precond, postcond)) {
					result = false;
					break;
				}
			}
		}
		
		return result;
	}
	
	override protected void EndRefineSuccess(ProofState proofState) {
		
		Expr annotExpr = ComputeTransitionAnnotation();
	
		foreach(ProcedureState procState in proofState.procedureStates.Values) {
			foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
				atomicBlock.PushAnnotation(annotExpr);
			}
		}
		
		proofState.invs.Add(this.inv);
		// proofState.rely.Add(this.rely);
		// proofState.guar.Add(this.guar);
		
		proofState.RemoveAuxVar((GlobalVariable)errVar);
	}
	
	override protected void EndRefineFail(ProofState proofState) {
		foreach(ProcedureState procState in proofState.procedureStates.Values) {
			procState.ClearTransitionPredicates();
		}
		
		proofState.RemoveAuxVar((GlobalVariable)auxVar);
		
		proofState.RemoveAuxVar((GlobalVariable)errVar);
	}
	
} // end class RefineCommand


} // end namespace QED


/**
protected void AnnotateProgram(ProofState! proofState) {
		IdentifierExpr! errExpr = new IdentifierExpr(Token.NoToken, errVar);
		IdentifierExpr! perrExpr = ProofState.GetInstance().GetPrimedExpr(errVar);
		
		IdentifierExpr! auxExp = new IdentifierExpr(Token.NoToken, auxVar);
		IdentifierExpr! auxPrimeExp = ProofState.GetInstance().GetPrimedExpr(auxVar);
		
		Expr! annotExpr = ComputeTransitionAnnotation();
		
		for(int i = 0, n = this.syncPredicates.Count; i < n; ++i) {
			Expr! syncPredicate = this.syncPredicates[i];
		
			Expr! assertAux = Expr.Eq(auxExp, Expr.Literal(i));
			Expr! assertAuxPrime = Expr.Eq(auxPrimeExp, Expr.Literal(i));
			
			rg.Rely = Expr.And(rg.Rely,
							   Expr.Eq(errExpr, perrExpr));
							   
			foreach(ProcedureState! procState in proofState.procedureStates.Values) {
				if((!procState.IsVerified) || procState.IsPublic) {
					
					Output.LogLine("Refine: Annotating procedure: " + procState.impl.Name);
				
					bool addmodify = false;
				
					Hashtable labelToBlock = new Hashtable();
					foreach(AtomicBlock! atomicBlock in procState.atomicBlocks) {
						labelToBlock.Add(atomicBlock.UniqueLabel, atomicBlock);
					}
				
					bool done = false;
					while(!done) {
						procState.ResetTransitionPredicates();
						
						foreach(AtomicBlock! atomicBlock in procState.atomicBlocks) {
							atomicBlock.TransitionPredicate = Expr.And(atomicBlock.TransitionPredicate, annotExpr);
							if(labelToBlock.Contains(atomicBlock.UniqueLabel)) {
								Expr! labeledAssertAux = LabeledExpr.NegAuxAssert(atomicBlock, assertAux);
								Expr! labeledAnnot = Expr.Or(Expr.And(assertAux, Expr.Eq(errExpr, perrExpr)),
															 Expr.And(labeledAssertAux, Expr.Eq(perrExpr, Expr.True)));
								atomicBlock.TransitionPredicate = Expr.And(atomicBlock.TransitionPredicate, labeledAnnot);
							} else {
								atomicBlock.TransitionPredicate = Expr.And(atomicBlock.TransitionPredicate, Expr.Iff(perrExpr, errExpr));
							}
						}
						
						Expr! precond = Expr.Not(errExpr);
						if(Prover.GetInstance().CheckValid(Expr.Imp(Expr.And(proofState.Invariant, procState.Requires), syncPredicate))) {
							precond = Expr.And(precond, assertAux);
						}
							
						// now check
						if(!rg.CheckProcedure(proofState, procState, precond, Expr.Not(errExpr))) {
							// remove the failed assertions
							foreach(string! label in Prover.GetInstance().GetErrorLabels()) {
								// label may not point to an atomic block
								if(labelToBlock.Contains(label)) {
									AtomicBlock! atomicBlock = (AtomicBlock!)labelToBlock[label];
									// Output.LogLine("Unlabeled block " + atomicBlock.startBlock.Label);
									labelToBlock.Remove(label);
								}
							}
						} else {
							// now do code annotation
							done = true;
							
							foreach(AtomicBlock! atomicBlock in labelToBlock.Values) {
								Output.LogLine("Annotating atomic block " + atomicBlock.startBlock.Label);
								
								AssumeCmd! assumeCmd = new AssumeCmd(Token.NoToken, assertAux);
								atomicBlock.AnnotateEntry(assumeCmd);
							}
						} // end if
					} // end while
					
					Hashtable enterAuxLabels = new Hashtable(labelToBlock);
			
					//----------------------------------------------------------
					
					labelToBlock = new Hashtable();
					foreach(AtomicBlock! atomicBlock in procState.atomicBlocks) {
						if(!enterAuxLabels.ContainsKey(atomicBlock.UniqueLabel)) {
							labelToBlock.Add(atomicBlock.UniqueLabel, atomicBlock);
						}
					}
				
					done = false;
					while(!done) {
						procState.ResetTransitionPredicates();
						
						foreach(AtomicBlock! atomicBlock in procState.atomicBlocks) {
							atomicBlock.TransitionPredicate = Expr.And(atomicBlock.TransitionPredicate, annotExpr);
							if(labelToBlock.Contains(atomicBlock.UniqueLabel)) {
								Expr! labeledAssertAuxPrime = LabeledExpr.NegAuxAssert(atomicBlock, assertAuxPrime);
								Expr! labeledAnnot = Expr.Or(Expr.And(assertAuxPrime, Expr.Eq(errExpr, perrExpr)),
															 Expr.And(labeledAssertAuxPrime, Expr.Eq(perrExpr, Expr.True)));
								atomicBlock.TransitionPredicate = Expr.And(atomicBlock.TransitionPredicate, labeledAnnot);
							} else {
								atomicBlock.TransitionPredicate = Expr.And(atomicBlock.TransitionPredicate, Expr.Iff(perrExpr, errExpr));
							}
						}
						
						Expr! precond = Expr.Not(errExpr);
						if(Prover.GetInstance().CheckValid(Expr.Imp(Expr.And(proofState.Invariant, procState.Requires), syncPredicate))) {
							precond = Expr.And(precond, assertAux);
						}
						
						// now check
						if(!rg.CheckProcedure(proofState, procState, precond, Expr.Not(errExpr))) {
							// remove the failed assertions
							foreach(string! label in Prover.GetInstance().GetErrorLabels()) {
								// label may not point to an atomic block
								if(labelToBlock.Contains(label)) {
									AtomicBlock! atomicBlock = (AtomicBlock!)labelToBlock[label];
									// Output.LogLine("Unlabeled block " + atomicBlock.startBlock.Label);
									labelToBlock.Remove(label);
								}
							}
						} else {
							// now do code annotation
							done = true;
							
							foreach(AtomicBlock! atomicBlock in labelToBlock.Values) {
								if(!enterAuxLabels.ContainsKey(atomicBlock.UniqueLabel)) {
									Output.LogLine("Annotating atomic block " + atomicBlock.startBlock.Label);
									
									SimpleAssignCmd assignCmd = AssignCmd.SimpleAssign(Token.NoToken, auxExp, Expr.Literal(i));
									atomicBlock.AnnotateExit(assignCmd);
								
									addmodify = true;
								}
							}
						} // end if
					} // end while
					
					//----------------------------------------------------------
					
					if(addmodify) {
						if(! procState.modifiesMap.ContainsKey(auxVar)) {
							procState.impl.Proc.Modifies.Add(auxExp);
							procState.modifiesMap.Add(auxVar, null);
						}
					}
					
				} // if not verified
					
			} // end foreach procedure
			
		} // end for syncPredicates[i]
	}
**/