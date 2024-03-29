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
  

public class PreCommand : ProofCommand
{
	string label;
	Expr formula;
	
	public PreCommand(string l, Expr f)
		: base("pre")
	{
		this.label = l;
		this.formula = f;
		
		desc = "pre " + label + " " + Output.ToString(formula);
	}

    public static string Usage()
    {
        return "pre procedureName preconditionFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("pre"))
        {
            string label = parser.NextAsString();
            Expr formula = parser.RestAsExpr();
            return new PreCommand(label, formula);
        }
        return null;
    }
	
	override public bool Run(ProofState proofState) {
		
		DoRun(proofState);
		
		return false;
	}
	
	public void DoRun(ProofState proofState) {
		
		ProcedureState procState = proofState.GetProcedureState(label);
			
		procState.ResolveTypeCheckExpr(formula, false);
		
		procState.AddRequires(formula);	

        // add assume at the beginning
        CodeTransformations.InstrumentEntry(procState.Body, new CmdSeq(new AssumeCmd(Token.NoToken, formula)), false);

        procState.MarkAsTransformed();

		Output.AddLine("Added the precondition for the procedure");		
	
        //} else { // kind == "loop"
		
        //    LoopBlock loopBlock = (proofState.GetAtomicBlock(label) as LoopBlock);
			
        //    loopBlock.procState.ResolveTypeCheckExpr(formula, false);
			
        //    //Expr newPre = Expr.And(loopBlock.LoopInfo.Pre, formula);

        //    //Expr invs = proofState.InvariantForProc(loopBlock.procState);
        //    //GatedAction spec = loopBlock.LoopInfo.Spec;

        //    ////--------------------------

        //    //// check reflexivity of the spec

        //    //if (!Logic.IsReflexive(loopBlock.procState, Expr.Imp(Expr.And(invs, newPre), spec.action)))
        //    //{
        //    //    Output.LogLine("The new precondition makes the loop specification irreflexive.");
        //    //    return;
        //    //}

        //    //loopBlock.LoopInfo.Pre = newPre;
        //    //loopBlock.UpdateSpec();

        //    loopBlock.Add
			
        //    Output.AddLine("Added the precondition for the loop");		
        //}
		
	}
	
} // end class PreCommand


public class PostCommand : ProofCommand
{
	string label;
	Expr formula;
	
	public PostCommand(string l, Expr f)
		: base("post")
	{
		this.label = l;
		this.formula = f;
		
		desc = "post " + label + " " + Output.ToString(formula);
	}

    public static string Usage()
    {
        return "post procedureName postconditionFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("post"))
        {
            string label = parser.NextAsString();
            Expr formula = parser.RestAsExpr();
            return new PostCommand(label, formula);
        }
        return null;
    }
	
	
	override public bool Run(ProofState proofState) {
		
		DoRun(proofState);
		
		return false;
	}
	
	public void DoRun(ProofState proofState) {
		
		ProcedureState procState = proofState.GetProcedureState(label);

        bool hasOld = new MyOldFinder().HasAny(formula);
        if (!procState.ResolveTypeCheckExpr(formula, hasOld))
        {
            Output.AddError("Resolve-typecheck errors in the post condition!");
            return;
        }
        
		procState.AddEnsures(formula);

        // add assert at the end
        // TODO: what happens when the formula has "old" expressions?
        if (!hasOld)
        {
            CodeTransformations.InstrumentExit(procState.Body, new CmdSeq(new AssertCmd(Token.NoToken, formula)), false, null);
        }
        else
        {
            Output.AddError("Post condition could not be inserted an assertion since it had \"old\" epressions!");
        }
        procState.MarkAsTransformed();
		
		Output.AddLine("Added the postcondition for the procedure");		
			
        //} else { // kind == "loop"
		
        //    LoopBlock loopBlock = (proofState.GetAtomicBlock(label) as LoopBlock);
			
        //    loopBlock.procState.ResolveTypeCheckExpr(formula, true);

        //    GatedAction spec = loopBlock.LoopInfo.Spec;

        //    Expr newPost = Logic.ConvertFromOldToPrime(proofState, loopBlock.procState, Expr.And(spec.action, formula));

        //    Expr invs = proofState.InvariantForProc(loopBlock.procState);
            

        //    //--------------------------

        //    // check reflexivity of the spec

        //    if (!Logic.IsReflexive(loopBlock.procState, Expr.Imp(Expr.And(invs, spec.gate), newPost)))
        //    {
        //        Output.LogLine("The new postcondition makes the loop specification irreflexive.");
        //        return;
        //    }

        //    loopBlock.LoopInfo.Post = Expr.And(spec.action, formula);
        //    loopBlock.UpdateSpec();

        //    Output.AddLine("Added the postcondition for the loop");
        //}
		
	}
	
} // end class PreCommand

public class MTypeCommand : ProofCommand
{
    string label;
    MoverType mtype;

    public MTypeCommand(string l, MoverType m)
        : base("mtype ")
    {
        this.label = l;
        this.mtype = m;

        desc = "mtype " + label + " " + mtype.ToString();
    }

    public static string Usage()
    {
        return "mtype procedureName L|R|B|N";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("mtype"))
        {
            string label = parser.NextAsString();
            MoverType mtype = parser.NextAsMoverType();
            return new MTypeCommand(label, mtype);
        }
        return null;
    }


    override public bool Run(ProofState proofState)
    {

        DoRun(proofState);

        return false;
    }

    public void DoRun(ProofState proofState)
    {
        ProcedureState procState = proofState.GetProcedureState(label);

        if (procState.Mover != null)
        {
            Output.AddError("You are re-setting the mover type of the procedure, which is prohibited!");
            return;
        }

        procState.Mover = mtype;

        Output.AddLine("Set the mover type of the procedure.");
    }

} // end class MTypeCommand

public class LoopInvCommand : ProofCommand
{
    string label;
    Expr formula;

    public LoopInvCommand(string l, Expr f)
        : base("loopinv")
    {
        this.label = l;
        this.formula = f;

        desc = "loopinv " + label + " " + Output.ToString(formula);
    }

    public static string Usage()
    {
        return "loopinv atomicBlockLabel@procedureName invariantFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("loopinv"))
        {
            string label = parser.NextAsString();
            Expr formula = parser.RestAsExpr();
            return new LoopInvCommand(label, formula);
        }
        return null;
    }


    override public bool Run(ProofState proofState)
    {
        DoRun(proofState);

        return false;
    }

    public void DoRun(ProofState proofState)
    {
        AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(label);

        AtomicStmt atomicStmt = atomicBlock.parent;

        // Qoogie.ResolveStmt(atomicBlock.procState.Body); // TODO: this should have been needed

        BigBlock bb = atomicStmt.body.ParentContext.ParentBigBlock;

        if (!(bb.ec is WhileCmd))
        {
            Output.AddError("While statement could not been found!");
            return;
        }

        ProcedureState procState = atomicBlock.procState;
        procState.ResolveTypeCheckExpr(formula, false);

        WhileCmd whileCmd = bb.ec as WhileCmd;
        whileCmd.Invariants.Add(new AssertCmd(Token.NoToken, formula));

        procState.MarkAsTransformed();
    }

} // end class LoopInvCommand


} // end namespace QED