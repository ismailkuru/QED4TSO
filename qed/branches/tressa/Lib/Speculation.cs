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

#if false
public class Speculation
{
	public string UniqueId;
	public bool IsEnabled;	
	public Expr Assertion;
	public ProcedureState ProcState;
	public bool IsEntry;
	public Expr ErrorExpr;
	public Expr PErrorExpr;
	
	public Speculation (string i, Expr a, ProcedureState p, bool e, Expr err, Expr perr) {
		this.IsEnabled = true;
		this.UniqueId = i;
		this.Assertion = a;
		this.IsEntry = e;
		this.ErrorExpr = err;
		this.PErrorExpr = perr;
		this.ProcState = p;
	}
	
	public void AnnotateTransition() {
		
		foreach(AtomicBlock atomicBlock in ProofState.GetInstance().GetAllAtomicBlocks()) {
			CallBlock callBlock = atomicBlock as CallBlock;
			
			if(IsEnabled && callBlock != null && this.ProcState.callerBlocks.Contains(callBlock)) {
				Debug.Assert(callBlock.Callee == this.ProcState); // sanity check
				
				Expr assertion;
				if(IsEntry) {
					assertion = this.ProcState.PreAtCall(callBlock.procState, callBlock.CallCmd, this.Assertion);
				} else {
					assertion = this.ProcState.PostAtCall(callBlock.procState, callBlock.CallCmd, this.Assertion);
				}

                Expr labeledAssertAux = LabeledExprHelper.NegAuxAssert(UniqueId, callBlock, assertion);
				Expr labeledAnnot = Expr.Or(Expr.And(Assertion, Expr.Eq(ErrorExpr, PErrorExpr)),
											 Expr.And(labeledAssertAux, Expr.Eq(PErrorExpr, Expr.True)));
				callBlock.AnnotateTransitionPredicate(labeledAnnot);
			
			} else {
				
				atomicBlock.AnnotateTransitionPredicate(Expr.Eq(ErrorExpr, PErrorExpr));
			
			}
		}
	}
	
	public void AnnotateCode() {
		if(this.IsEnabled) {
			Output.LogLine("Annotating procedure " + ProcState.impl.Name);
			if(this.IsEntry) {
				this.ProcState.AddRequires(this.Assertion);
			} else {
				this.ProcState.AddEnsures(this.Assertion);
			}
		}
	}	
}

public class SpeculationSet {
	private Dictionary<string,Speculation> map;
	private int nextId;
	private Expr errExpr;
	private Expr perrExpr;
	
	public SpeculationSet(Expr err, Expr perr) {
		this.nextId = 0;
		this.map = new Dictionary<string,Speculation>();
		this.errExpr = err;
		this.perrExpr = perr;
	}
	
	public void AddForEntry(Expr a, ProcedureState p) {
		Add(a, p, true);
	}
	
	public void AddForExit(Expr a, ProcedureState p) {
		Add(a, p, false);
	}
	
	public void Add(Expr a, ProcedureState p, bool e) {
		string id = "Specu" + nextId.ToString();
		Speculation specu = new Speculation(id, a, p, e, errExpr, perrExpr);
		map.Add(id, specu);
		++nextId;
	}
	
	public void Disable(string id) {
		if(map.ContainsKey(id)) {
			Speculation annot = map[id];
			annot.IsEnabled = false;
		}
	}
	
	public void Disable(Set<string> idset) {
		foreach(string id in idset) {
			Disable(id);
		}
	}
	
	public void Disable(Set<ProcedureState> procs) {
		foreach(Speculation specu in map.Values) {
			if(procs.Contains(specu.ProcState)) {
				specu.IsEnabled = false;
			}
		}
	}
	
	public void AnnotateCodes() {
		foreach(Speculation specu in map.Values) {
			specu.AnnotateCode();
		}
	}
	
	public void AnnotateTransitions() {
		foreach(Speculation specu in map.Values) {
			specu.AnnotateTransition();
		}
	}
	
	public Expr GetAnnotatedPrecond(ProcedureState procState) {
		Expr pre = Expr.True;
		foreach(Speculation specu in map.Values) {
			if(specu.IsEnabled && specu.IsEntry && specu.ProcState == procState) {
				pre = Expr.And(pre, specu.Assertion);
			}
		}
		return pre;
	}
	
	public Expr GetAnnotatedPostcond(ProcedureState procState) {
		Expr pre = Expr.True;
		foreach(Speculation specu in map.Values) {
			if(specu.IsEnabled && (! specu.IsEntry) && specu.ProcState == procState) {
				pre = Expr.And(pre, specu.Assertion);
			}
		}
		return pre;
	}
	
	public Set<ProcedureState> GetAnnotatedProcs() {
		Set<ProcedureState> procs = new Set<ProcedureState>();
		
		foreach(Speculation specu in map.Values) {
			if(specu.IsEnabled) {
				procs.Add(specu.ProcState);
			}
		}
		
		return procs;
	}
	
	
}
#endif

} // end namespace QED