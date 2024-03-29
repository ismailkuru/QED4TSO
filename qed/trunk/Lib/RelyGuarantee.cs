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
using Microsoft.Boogie.AbstractInterpretation;
using AI = Microsoft.AbstractInterpretationFramework;
using Microsoft.Contracts;


public class RelyGuarantee {

	protected Expr rely;
	
	protected Expr guar;
	
	protected Expr invs;
	
	public Expr Rely {
		get {
			return rely;
		}
		set {
			rely = value;
		}
	}
	
	public Expr Guar {
		get {
			return guar;
		}
		set {
			guar = value;
		}
	}
	
	public Expr Invariant {
		get {
			return invs;
		}
		set {
			invs = value;
		}
	}
	
	protected ErrorTrace errorTrace;
	
	public ErrorTrace LastErrorTrace {
		get {
			return errorTrace;
		}
	}
	
	public RelyGuarantee(Expr i, Expr r, Expr g) {
		this.invs = i;
		this.rely = r;
		this.guar = g;
	}

	virtual public bool CheckProcedure(ProofState proofState, ProcedureState procState) {
		return CheckProcedure(proofState, procState, Expr.True, Expr.True);
	}
	
	virtual public bool CheckProcedure(ProofState proofState, ProcedureState procState, Expr precond, Expr postcond) {
		
		Expr oldRely = this.rely;
		this.rely = Expr.And(oldRely, procState.RelyForLocals);
		
		Expr oldInvs = this.invs;
		this.invs = Expr.And(oldInvs, procState.LocalInvariant);
		//------------------
		
		precond = Logic.And(procState.Pre, precond);
        //postcond = Logic.And(procState.Post, postcond);		
		//------------------
		
		bool result = false;

        procState.ComputeAtomicBlocks();

		Expr wp = ComputeWP(proofState, procState, procState.InitialAPLBlock, postcond, new Set<APLBlock>());			
		
		// now construct the entire formula
		Expr cond = Expr.Imp(Expr.And(precond, this.invs), wp);
		
		// check the wp...
		result = Prover.GetInstance().CheckValid(cond);
		
		if(!result) {
			this.errorTrace = new ErrorTrace(Prover.GetInstance().GetErrorLabels(), procState);
		}
		
		//------------------
		this.rely = oldRely;
		this.invs = oldInvs;
		
		return result;
	}
		
	protected Expr ComputeWP(ProofState proofState, ProcedureState procState, APLBlock aplBlock, Expr postcond, Set<APLBlock> visitedBlocks) {
		Expr wp;

        //-----------------------
        // This is for sanity check that the CFG is acyclic
        Debug.Assert(!visitedBlocks.Contains(aplBlock));
        visitedBlocks.Add(aplBlock);

        if (aplBlock.Successors.Count > 0)
        {
			wp = Expr.True;
            Set<APLBlock> successors = aplBlock.Successors;
			foreach(APLBlock successor in successors) {
                wp = Expr.And(wp, ComputeWP(proofState, procState, successor, postcond, new Set<APLBlock>(visitedBlocks)));
			}
			// now inject the environment transition	
			Expr envtrans = ComputeEnvironmentTransition(proofState, procState);	
			wp = ComputeWPEnv(proofState, procState, envtrans, wp);
		} else {
            Expr labeledPost = LabeledExprHelper.PostCond(aplBlock, postcond);
			wp = labeledPost;
		}
		
		// compute the final 
        wp = ComputeWPLocal(proofState, procState, aplBlock, wp);
		
		// insert label
        Expr labeledWp = LabeledExprHelper.APLBlock(aplBlock, wp);
		return labeledWp;
	}
	
	protected Expr ComputeWPLocal(ProofState proofState, ProcedureState procState, APLBlock aplBlock, Expr Q) {

        Expr T = aplBlock.TransitionPredicate;
        Expr A = aplBlock.AnnotAssertions;

        Expr labeledInvs = LabeledExprHelper.Invariant(aplBlock, this.invs);
	
		Expr Qprime = procState.MakePrime(Expr.And(labeledInvs, Q));
		
		VariableSeq dummies = new VariableSeq();
		dummies.AddRange(proofState.primes);
		dummies.AddRange(procState.primes);

        Expr labeledGuar = LabeledExprHelper.Guar(aplBlock, this.guar);
		
		Expr wp = Expr.And(A, Logic.ForallExpr(dummies, Expr.Imp(T, Expr.And(labeledGuar, Qprime))));
		
		return wp;	
	}
	
	protected Expr ComputeWPEnv(ProofState proofState, ProcedureState procState, Expr T, Expr Q) {
		Expr Qprime = procState.MakePrime(Q);
		
		VariableSeq dummies = new VariableSeq();
		dummies.AddRange(proofState.primes);
		dummies.AddRange(procState.primes);

        Expr wp = Logic.ForallExpr(dummies, Expr.Imp(T, Qprime));
		
		return wp;	
	}
	
	protected Expr ComputeEnvironmentTransition(ProofState proofState, ProcedureState procState) {
		return Expr.And(this.rely, procState.MakePrime(this.invs));
	}
	
} // end class RelyGuarantee
  
} // end namespace QED