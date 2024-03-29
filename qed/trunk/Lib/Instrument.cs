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
  
  
abstract public class InstrumentCommand : ProofCommand
{
	protected List<Expr> predicates;
	protected Expr rely;
	protected Expr guar;
	
	public InstrumentCommand(Expr r, Expr g, List<Expr> preds)
		: base("instrument")
	{
		this.predicates = preds;
		this.rely = r;
		this.guar = g;
	}
	
	override public bool Run(ProofState proofState) {
		
		DoRun(proofState);
		
		return false;
	}

    abstract public Set<AtomicBlock> DoRun(ProofState proofState);

    virtual public Set<AtomicBlock> AnnotateProcedure(ProofState proofState, ProcedureState procState, AnnotationSet annotationSet, RelyGuarantee rg, IdentifierExpr errExpr, IdentifierExpr perrExpr)
    {
		
		bool done = false;

        procState.ComputeAtomicBlocks();

        annotationSet.AnnotatePreds();

		while(!done) {
		
			// now check
			Expr precond = Expr.Not(errExpr);
			Expr postcond = Expr.Not(perrExpr);
			if(!rg.CheckProcedure(proofState, procState, precond, postcond)) {
				// remove the failed assertions
				annotationSet.Disable(Prover.GetInstance().GetErrorLabels());
			} else {
				done = true;
				// now do code annotation
				annotationSet.AnnotateCodes();
			} // end if
		} // end while

        VariableSeq modifiedVars = annotationSet.GetModifiedVars();
		
		foreach(Variable modVar in modifiedVars) {
			procState.CheckAddModifies(modVar, true);
		}
		
		return annotationSet.GetAnnotatedBlocks();
	}
	
} // end class InstrumentCommand

public class InstrumentEntryCommand : InstrumentCommand
{
	public InstrumentEntryCommand(Expr r, Expr g, List<Expr> preds)
		: base(r, g, preds)
	{
		desc = "instrument entry ";
		desc += Output.ToString(preds[0]);
		for(int i = 1, n = preds.Count; i < n; ++i) {
			desc += Output.ToString(preds[i]);
		}
	}

    public static string Usage()
    {
        return "instrument entry predicateFormulas relyFormula guaranteeFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("instrument"))
        {
            if (parser.NextAsString().Equals("entry"))
            {
                List<Expr> exprlist = parser.RestAsExprList('#');
                Expr rely = exprlist[0];
                Expr guar = exprlist[1];
                return new InstrumentEntryCommand(rely, guar, exprlist.GetRange(2, exprlist.Count));
            }
        }
        return null;
    }

    override public Set<AtomicBlock> DoRun(ProofState proofState)
    {
	
		foreach(Expr pred in predicates) {
			proofState.ResolveTypeCheckExpr(pred, false);
		}

        Set<AtomicBlock> annotatedBlocks = new Set<AtomicBlock>();
		
        Variable errVar = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "errx", BasicType.Bool));
		proofState.AddAuxVar((GlobalVariable)errVar);
		IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
		IdentifierExpr perrExpr = ProofState.GetInstance().GetPrimedExpr(errVar);
		
		RelyGuarantee rg = new RelyGuarantee(proofState.Invariant,
											 Expr.And(Expr.And(proofState.Rely, this.rely), Expr.Eq(errExpr, perrExpr)),
											 Expr.And(proofState.Guar, this.guar));
		
		foreach(ProcedureState procState in proofState.procedureStates.Values) {
		
			if((!procState.IsReduced) || procState.IsPublic) {
			
				Output.LogLine("Instrumenting procedure: " + procState.impl.Name);

                procState.ComputeAtomicBlocks();
                List<AtomicBlock> atomicBlocks = procState.AtomicBlocks;

				//----------------------------------------------------------------------
                AnnotationSet annotationSet = new AnnotationSet(errExpr, perrExpr);
				
				// entry assume aux = tid
                foreach (AtomicBlock atomicBlock in atomicBlocks)
                {
					foreach(Expr pred in predicates) {
						annotationSet.AddForEntry(pred, new AssumeCmd(Token.NoToken, pred), atomicBlock); // TODO: make this assert
					}
				}
				
				annotatedBlocks.AddRange(AnnotateProcedure(proofState, procState, annotationSet, rg, errExpr, perrExpr));	
			}
		} // end foreach procedure
		
		return annotatedBlocks;
	}
	
} // end class InstrumentEntryCommand


public class InstrumentExitCommand : InstrumentCommand
{
    public InstrumentExitCommand(Expr r, Expr g, List<Expr> preds)
        : base(r, g, preds)
    {
        desc = "instrument exit ";
        desc += Output.ToString(preds[0]);
        for (int i = 1, n = preds.Count; i < n; ++i)
        {
            desc += Output.ToString(preds[i]);
        }
    }

    public static string Usage()
    {
        return "instrument exit predicateFormulas relyFormula guaranteeFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("instrument"))
        {
            if (parser.NextAsString().Equals("exit"))
            {
                List<Expr> exprlist = parser.RestAsExprList('#');
                Expr rely = exprlist[0];
                Expr guar = exprlist[1];
                return new InstrumentExitCommand(rely, guar, exprlist.GetRange(2, exprlist.Count));
            }
        }
        return null;
    }

    override public Set<AtomicBlock> DoRun(ProofState proofState)
    {

        foreach (Expr pred in predicates)
        {
            proofState.ResolveTypeCheckExpr(pred, false);
        }

        Set<AtomicBlock> annotatedBlocks = new Set<AtomicBlock>();

        GlobalVariable errVar = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "errx", BasicType.Bool));
        proofState.AddAuxVar((GlobalVariable)errVar);
        IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
        IdentifierExpr perrExpr = ProofState.GetInstance().GetPrimedExpr(errVar);

        RelyGuarantee rg = new RelyGuarantee(proofState.Invariant,
                                             Expr.And(Expr.And(proofState.Rely, this.rely), Expr.Eq(errExpr, perrExpr)),
                                             Expr.And(proofState.Guar, this.guar));

        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {

            if ((!procState.IsReduced) || procState.IsPublic)
            {

                Output.LogLine("Instrumenting procedure: " + procState.impl.Name);

                //----------------------------------------------------------------------
                AnnotationSet annotationSet = new AnnotationSet(errExpr, perrExpr);

                // entry assume aux = tid
                foreach (AtomicBlock atomicBlock in procState.AtomicBlocks)
                {
                    foreach (Expr pred in predicates)
                    {

                        NAryExpr equalsExpr = pred as NAryExpr;
                        Debug.Assert(equalsExpr.Fun.FunctionName == new BinaryOperator(Token.NoToken, BinaryOperator.Opcode.Eq).FunctionName);

                        if (equalsExpr.Args[0] is IdentifierExpr)
                        {
                            IdentifierExpr iexpr = (equalsExpr.Args[0] as IdentifierExpr);
                            IdentifierExpr pexpr = (procState.AllPrimesMap[iexpr.Decl] as IdentifierExpr);
                            AssignCmd assignCmd = AssignCmd.SimpleAssign(Token.NoToken, (equalsExpr.Args[0] as IdentifierExpr), equalsExpr.Args[1]);
                            annotationSet.AddForEntry(Expr.Eq(pexpr, equalsExpr.Args[1]), assignCmd, atomicBlock);
                        }
                        else
                        {
                            NAryExpr iexpr = (equalsExpr.Args[0] as NAryExpr);
                            Debug.Assert(iexpr != null && iexpr.Fun.FunctionName == "MapSelect");
                            IdentifierExpr pexpr = (procState.AllPrimesMap[iexpr.Args[0]] as IdentifierExpr);
                            AssignCmd assignCmd = AssignCmd.MapAssign(Token.NoToken, (iexpr.Args[0] as IdentifierExpr), equalsExpr.Args[1]); // TODO: may have arity more than one
                            annotationSet.AddForEntry(Expr.Eq(pexpr, equalsExpr.Args[1]), assignCmd, atomicBlock);
                        }
                    }
                }

                annotatedBlocks.AddRange(AnnotateProcedure(proofState, procState, annotationSet, rg, errExpr, perrExpr));
            }
        } // end foreach procedure

        proofState.RemoveAuxVar(errVar);

        return annotatedBlocks;
    }

} // end class InstrumentExitCommand



} // end namespace QED