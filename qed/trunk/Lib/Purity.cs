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
  

public class PurifyCommand : ProofCommand
{
	public PurifyCommand()
		: base("purify")
	{
		desc = "purify";
	}

    public static string Usage()
    {
        return "purify";
    }
    
    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("purify"))
        {
            return new PurifyCommand();
        }
        return null;
    }

	override public bool Run(ProofState proofState) {
		
		Expr spec = ComputePureSpec();
		
		Hashtable pureBlocks = new Hashtable();
		
		foreach(ProcedureState procState in proofState.procedureStates.Values) {
			if(!procState.IsReduced) {

                procState.ComputeAtomicBlocks();
                List<AtomicBlock> atomicBlocks = procState.AtomicBlocks;
                
                foreach (AtomicBlock atomicBlock in atomicBlocks)
                {
					Expr trp = atomicBlock.TransitionPredicate;
					
					if(Prover.GetInstance().CheckValid(Expr.Imp(trp, spec))) {
                        AtomicStmt pureStmt = CreatePureStmt(atomicBlock);
                        CodeTransformations.SwapAtoms(atomicBlock.parent, pureStmt);
                        procState.MarkAsTransformed();
					}
				}
			}
		}
		
		return false;
	}

    private AtomicStmt CreatePureStmt(AtomicBlock atomicBlock)
    {
        BigBlock bb = new BigBlock(atomicBlock.tok, null, new CmdSeq(new CommentCmd("SKIP", true)), null, null);
        List<BigBlock> bbs = new List<BigBlock>();
        bbs.Add(bb);
        StmtList stmt = new StmtList(bbs, Token.NoToken);

        AtomicStmt atom = new AtomicStmt(atomicBlock.tok, atomicBlock.Label, stmt, null);

        return atom;
    }
	
	protected Expr ComputePureSpec() {
		Expr predicate = Expr.True;
		
		foreach(Variable gvar in ProofState.GetInstance().ProgramVars) {
			IdentifierExpr primeexp = ProofState.GetInstance().GetPrimedExpr(gvar);
			
			predicate = Expr.And(predicate, Expr.Eq(primeexp, new IdentifierExpr(Token.NoToken, gvar)));
		}
		
		return predicate;
    }
	
} // end class ReduceCommand



} // end namespace QED