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
using System.Text;
  

public class ReduceCommand : ProofCommand
{
    bool isproc;
    string label;

	public ReduceCommand(string lbl, bool isproc)
		: base("mover")
	{
		this.label = lbl;
        this.isproc = isproc;
        desc = isproc ? ("reduce proc " + label) : ("reduce all");
	}

    public static string Usage()
    {
        return "reduce all|proc procName";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("reduce"))
        {
            string label = parser.NextAsString();
            if (label == "loop" || label == "loop2" || label == "skip") return null;

            if (label == "proc")
            {
                label = parser.NextAsString();
                return new ReduceCommand(label, true);
            }
            else if (label == "all")
            {
                return new ReduceCommand("all", false);
            }
            // else do for a particular block
            return new ReduceCommand(label, false);
        }
        return null;
    }
	
	override public bool Run(ProofState proofState) {
		
		bool iterative = proofState.config.GetBool("Reduction", "Iterative", true);

        List<ProcedureState> procStates = new List<ProcedureState>();

        if (isproc)
        {
            ProcedureState procState = proofState.GetProcedureState(label);
            procStates.Add(procState);
        }
        else
        {
            procStates.AddRange(proofState.ProcedureStates);
        }

        DoRun(proofState, procStates, iterative);
        
        // report atomic procedures
        foreach (ProcedureState procState in procStates)
        {
            // update the CFG
            procState.ComputeAtomicBlocks();
            if (procState.IsAtomic)
            {
                Output.AddLine("Procedure " + procState.Name + " become atomic!");
            }
        }

		return false;
	}

    public void DoRun(ProofState proofState, List<ProcedureState> procStates, bool iterative)
    {
        bool any = false;

        foreach (ProcedureState procState in procStates)
        {
            MergeCommand mergeCommand = new MergeCommand(procState.Name, true, true);
            mergeCommand.Run(proofState);
        }

        do
        {
            any = false;

            StringBuilder strb = new StringBuilder();
            List<MoverCheck> mcs = new List<MoverCheck>();

            MCache.Reset();
            foreach (ProcedureState procState in procStates)
            {
                if (!QKeyValue.FindBoolAttribute(procState.impl.Proc.Attributes, "skipmc"))
                {
                    MoverCommand moverCommand = new MoverCommand(procState.Name, true, false);
                    moverCommand.Run(proofState);
                    mcs.AddRange(moverCommand.mcs);
                }
            }
            // update global last mover checks list
            proofState.LastMoverChecks = mcs;
            mcs = new List<MoverCheck>();

            foreach (ProcedureState procState in procStates)
            {
                MergeCommand mergeCommand = new MergeCommand(procState.Name, true, true);
                mergeCommand.Run(proofState);

                any |= mergeCommand.MergedAny;
            }

        } while (iterative && any);
    }
	
} // end class ReduceCommand

    // 

    // TSO

public class RemoveDummySkipCommand : ProofCommand
{
    public RemoveDummySkipCommand()
        : base("rmskpd")
    {
        desc = "rmskpd";
    }

    public static string Usage()
    {
        return "rmskpd";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("rmskpd"))
        {
            return new RemoveDummySkipCommand();
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {

        List<ProcedureState> procs = new List<ProcedureState>();


        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            procs.Add(procState);
        }


        foreach (ProcedureState procState in procs)
        {
            if (DoRun(proofState, procState))
            {
                //    Output.AddLine("TSOify the procedure : " + procState.Name);
            }
            else
            {
                //  Output.AddLine("Did not TSOify the procedure: " + procState.Name);
            }
        }

        return false;
    }

    public bool DoRun(ProofState proofState, ProcedureState procState)
    {
        procState.RemoveSkipAtomic(proofState);

        return true;



    }
}
   

    //Tso
public class InsertDummySkipCommand : ProofCommand
{
    public InsertDummySkipCommand()
        : base("skpd")
    {
        desc = "skpd";
    }

    public static string Usage()
    {
        return "skpd";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("skpd"))
        {
            return new InsertDummySkipCommand();
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {

        List<ProcedureState> procs = new List<ProcedureState>();


        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            procs.Add(procState);
        }


        foreach (ProcedureState procState in procs)
        {
            if (DoRun(proofState, procState))
            {
                //    Output.AddLine("TSOify the procedure : " + procState.Name);
            }
            else
            {
                //  Output.AddLine("Did not TSOify the procedure: " + procState.Name);
            }
        }

        return false;
    }

    public bool DoRun(ProofState proofState, ProcedureState procState)
    {
        procState.InsertSkipAtomic(proofState);

        return true;



    }
 }

    //TSO

public class DestroyEmptyDrainCommand : ProofCommand {

    public DestroyEmptyDrainCommand()
        : base("destroyemptydrains")
    {
        desc = "destroyemptydrains";
    }

    public static string Usage()
    {
        return "destroyemptydrains";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("destroyemptydrains"))
        {
            return new DestroyEmptyDrainCommand();
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {

        List<ProcedureState> procs = new List<ProcedureState>();


        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            procs.Add(procState);
        }


        foreach (ProcedureState procState in procs)
        {
            if (DoRun(proofState, procState))
            {
                //    Output.AddLine("TSOify the procedure : " + procState.Name);
            }
            else
            {
                //  Output.AddLine("Did not TSOify the procedure: " + procState.Name);
            }
        }

        return false;
    }

    public bool DoRun(ProofState proofState, ProcedureState procState)
    {
        procState.DestroyEmptyDrains(proofState); 
        return true;
        
    }
}




    //TSO
public class UnifyWhileStarDrainsCommand : ProofCommand {
    public UnifyWhileStarDrainsCommand()
        : base("unifydrains")
    {
        desc = "unifydrains";
    }

    public static string Usage()
    {
        return "unifydrains";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("unifydrains"))
        {
            return new UnifyWhileStarDrainsCommand();
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {

        List<ProcedureState> procs = new List<ProcedureState>();

       
        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            procs.Add(procState);
        }
        
       
        foreach (ProcedureState procState in procs)
        {
            if (DoRun(proofState, procState))
            {
            //    Output.AddLine("TSOify the procedure : " + procState.Name);
            }
            else
            {
              //  Output.AddLine("Did not TSOify the procedure: " + procState.Name);
            }
        }

        return false;
    }

    public bool DoRun(ProofState proofState, ProcedureState procState)
    {
        procState.ReduceWhileStarDrains(proofState);
     
        return true;    

    }




}
    //TSO RenamLabels



// TSOify 

public class TSOifyCommand : ProofCommand { 
     public TSOifyCommand()
        : base("tsoify")
    {
        desc = "tsoify ";
    }

    public static string Usage()
    {
        return "tsoify";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("tsoify"))
        {
            return new TSOifyCommand();
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {

        List<ProcedureState> procs = new List<ProcedureState>();

       
        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            procs.Add(procState);
        }
        
       
        foreach (ProcedureState procState in procs)
        {
            if (DoRun(proofState, procState))
            {
            //    Output.AddLine("TSOify the procedure : " + procState.Name);
            }
            else
            {
              //  Output.AddLine("Did not TSOify the procedure: " + procState.Name);
            }
        }

        return false;
    }

    public bool DoRun(ProofState proofState, ProcedureState procState)
    {
        procState.TsoifyBefore(proofState);
   
       procState.TsoifyAfter(proofState);

     
        return true;

     

    }




}


public class InlineCommand : ProofCommand
{

    string procname;

    public InlineCommand(string name)
        : base("inline")
    {
        this.procname = name;
        desc = "inline " + procname;
    }

    public static string Usage()
    {
        return "inline all|procedureName";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("inline"))
        {
            string procname = parser.NextAsString();
            return new InlineCommand(procname);
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {

        List<ProcedureState> procs = new List<ProcedureState>();

        if (procname == "all")
        {
            foreach (ProcedureState procState in proofState.procedureStates.Values)
            {
                procs.Add(procState);
            }
        }
        else
        {
            
            ProcedureState procState = proofState.GetProcedureState(procname);
            if (procState == null)
            {
                Output.AddLine("Procedure not found : " + procname);
                return false;
            }
            procs.Add(procState);
        }

        foreach (ProcedureState procState in procs)
        {
            if (DoRun(proofState, procState))
            {
                Output.AddLine("Reduced the procedure : " + procState.Name);
            }
            else
            {
                Output.AddLine("Did not reduce the procedure: " + procState.Name);
            }
        }

        return false;
    }

    public bool DoRun(ProofState proofState, ProcedureState procState)
    {

        if (!procState.IsReduced)
        {
            // update the CFG
            procState.ComputeAtomicBlocks();

            if (procState.IsAtomic)
            {
                procState.Reduce(proofState);
                return true;
            }
            else
            {
                Output.AddError("Body of the procedure is not atomic!");
                return false;
            }
        }
        else
        {
            Output.AddError("Procedure was already reduced!");
            return false;
        }


        //    // procState.ClearTransitionPredicates();

        //    //procState.EnableCondAssumesForLoops();
        //    //procState.EnableCondAssertsToCheck();

        //    Expr invs = proofState.InvariantForProc(procState);

        //    GatedAction spec = procState.Spec;

        //    SeqAnalysis sa = new SeqAnalysis(invs);

        //    // check the wp...
        //    if(sa.CheckProcedure(proofState, procState, spec.gate, spec.action)) {
        //        // replace the blocks with spec block
        //        // and replace calls in other procs with call blocks
        //        procState.Reduce();

        //        if(! procState.IsPublic) {
        //            proofState.RemoveProcedureState(procState);

        //        } else {

        //            //procState.DisableCondAssumesForLoops();
        //            //procState.DisableCondAssertsToCheck();
        //        }

        //        done = true;

        //    } else {

        //        //procState.DisableCondAssumesForLoops();
        //        //procState.DisableCondAssertsToCheck();

        //        done = false;
        //    }

        //}

        //return done;
    }

} // end class ReduceCommand


public class SkipCommand : ProofCommand
{
    string blocklabel;
    
    public SkipCommand(string name)
        : base("skip")
    {
        this.blocklabel = name;
        desc = "skip " + blocklabel;
    }

    public static string Usage()
    {
        return "skip atomicBlockLabel@procedureName";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("skip"))
        {
                string blocklabel = parser.NextAsString();
                return new SkipCommand(blocklabel);
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {
        AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);
        if (atomicBlock == null)
        {
            Output.AddError("Atomic block does not exists: " + blocklabel);
            return false;
        }

        ProcedureState procState = atomicBlock.procState;

        //------------------------------------------------------
        // check if the atomic block is the body of a loop
        AtomicStmt atom = atomicBlock.parent;

        BigBlock bb = atom.body.ParentContext.ParentBigBlock;
        if (bb.ec == null || !(bb.ec is WhileCmd) || !((bb.ec as WhileCmd).Body.BigBlocks[0] == atom.body.ParentBigBlock))
        {
            Output.AddError("Given atomic block is not in the body of a while loop!");
            return false;
        }

        if (DoRun(proofState, procState, bb) == null)
        {
            Output.AddError("Could not insert skip!");
            return false;
        }

        Output.AddLine("Inserted skip!");

        return false;
    }

    static public AtomicStmt DoRun(ProofState proofState, ProcedureState procState, BigBlock parentBB)
    {
        AtomicStmt skipAtom = new AtomicStmt(Token.NoToken, AtomicStmt.GenerateLabel(), Qoogie.SkipStmt, null);
        BigBlock skipBB = new BigBlock(Token.NoToken, skipAtom.label, new CmdSeq(), skipAtom, null);

        CodeTransformations.InsertBefore(parentBB, skipBB);
        
        procState.MarkAsTransformed();

        return skipAtom;
    }

} // end class SkipCommand

public class ReduceSkipCommand : ProofCommand
{
    string blocklabel;
    string codeText;

    public ReduceSkipCommand(string name, string code)
        : base("reduce")
    {
        this.blocklabel = name;
        this.codeText = code;
        desc = "reduce skip " + blocklabel + " " + code;
    }

    public static string Usage()
    {
        return "reduce skip atomicBlockLabel@procedureName";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("reduce"))
        {
            if (parser.NextAsString().Equals("skip"))
            {
                string blocklabel = parser.NextAsString();
                string code = parser.RestAsString();
                return new ReduceSkipCommand(blocklabel, code);
            }
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {

        AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);
        if (atomicBlock == null)
        {
            Output.AddError("Atomic block does not exists: " + blocklabel);
            return false;
        }

        ProcedureState procState = atomicBlock.procState;

        //------------------------------------------------------
        // check if the atomic block is the body of a loop
        AtomicStmt atom = atomicBlock.parent;
        
        BigBlock bb = atom.body.ParentContext.ParentBigBlock;
        if (bb.ec == null || !(bb.ec is WhileCmd) || !((bb.ec as WhileCmd).Body.BigBlocks[0] == atom.body.ParentBigBlock))
        {
            Output.AddError("Given atomic block is not the body of a while loop!");
            return false;
        }

        //--------------------------------------------
        // parse, resolve and typecheck the new code
        VariableSeq localVars;
        StmtList codeStmt = Qoogie.ParseCode(codeText, out localVars);

        if (codeStmt == null)
        {
            Output.AddError("Could not parse the code: " + codeText);
            return false;
        }

        //------------------------------------------
        // now do the job
        if (DoRun(proofState, procState, bb, codeStmt, localVars) == null)
        {
            Output.AddError("Statement could not be inserted successfully!");
            return false;
        }

        Output.AddLine("Statement is inserted successfully!");

        return false;
    }

    static public AtomicStmt DoRun(ProofState proofState, ProcedureState procState, BigBlock bb, StmtList codeStmt, VariableSeq localVars)
    {
        //-----------------------------------------
        // insert skip
        AtomicStmt skipAtom = SkipCommand.DoRun(proofState, procState, bb);

        procState.ComputeAtomicBlocks();

        // now simulate
        if (!SimulateCommand.DoRun(proofState, procState, skipAtom, codeStmt, localVars))
        {
            Output.AddError("Statement is not reflexive!");

            // remove the skip atom
            CodeTransformations.RemoveBigBlock(Qoogie.GetParentBigBlock(skipAtom));

            return null;
        }

        procState.MarkAsTransformed();

        return skipAtom;
    }
} // end class ReduceSkipCommand


public class ReduceLoopCommand : ProofCommand
{
    string blocklabel;
    string codeText;

    public ReduceLoopCommand(string name, string code)
        : base("reduce")
    {
        this.blocklabel = name;
        this.codeText = code;
        desc = "reduce loop " + blocklabel + " " + code;
    }

    public static string Usage()
    {
        return "reduce loop atomicBlockLabel@procedureName";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("reduce"))
        {
            if (parser.NextAsString().Equals("loop"))
            {
                string blocklabel = parser.NextAsString();
                string code = parser.RestAsString();
                return new ReduceLoopCommand(blocklabel, code);
            }
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {

        AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);
        if (atomicBlock == null)
        {
            Output.AddError("Atomic block does not exists: " + blocklabel);
            return false;
        }

        ProcedureState procState = atomicBlock.procState;

        //------------------------------------------------------
        // check if the atomic block is the body of a loop
        AtomicStmt atom = atomicBlock.parent;
        BigBlock bb = atom.body.ParentContext.ParentBigBlock;
        if (bb.ec == null || !(bb.ec is WhileCmd) || !((bb.ec as WhileCmd).Body.BigBlocks.Count == 1) || !((bb.ec as WhileCmd).Body.BigBlocks[0] == atom.body.ParentBigBlock))
        {
            Output.AddError("Given atomic block is not the body of a while loop!");
            return false;
        }

        // parse, resolve and typecheck
        VariableSeq localVars;
        StmtList codeStmt = Qoogie.ParseCode(codeText, out localVars);

        if (codeStmt == null)
        {
            Output.AddError("Could not parse the code: " + codeText);
            return false;
        }

        if (!DoRun(proofState, atomicBlock, bb, codeStmt, localVars))
        {
            Output.AddError("Could not reduce the loop!");
            return false;
        }

        Output.AddLine("Reduce the while loop!");

        return false;
    }

    static public bool DoRun(ProofState proofState, AtomicBlock bodyBlock, BigBlock parentBB, StmtList abstStmt, VariableSeq newlocals)
    {
        bool result = true;
        ProcedureState procState = bodyBlock.procState;

        // run reduce skip
        AtomicStmt specAtom = ReduceSkipCommand.DoRun(proofState, procState, parentBB, abstStmt, newlocals);
        if (specAtom == null)
        {
            Output.AddError("Could not insert the spec before the while loop!");
            return false;
        }

        procState.ComputeAtomicBlocks();

        result = ReduceLoop2Command.DoRun(proofState, procState, specAtom, bodyBlock, parentBB);
        
        procState.MarkAsTransformed();

        return result;
    }

    //static public bool DoRun(ProofState proofState, AtomicBlock bodyBlock, BigBlock parentBB, StmtList abstStmt, VariableSeq newlocals)
    //{
    //    WhileCmd whileCmd = parentBB.ec as WhileCmd;
    //    Debug.Assert(whileCmd != null);

    //    //------------------------------------------------------
    //    // check mover type of the body
    //    MoverTypeChecker moverChecker = new MoverTypeChecker(proofState, bodyBlock);
    //    moverChecker.Run();
    //    if (moverChecker.Result.None)
    //    {
    //        Output.AddError("Body of the loop is not a mover!");
    //        return false;
    //    }

    //    //------------------------------------------------------
    //    // get the spec block        
    //    ProcedureState procState = bodyBlock.procState;
    //    AtomicStmt atom = bodyBlock.parent;
    //    BigBlock parent = atom.body.ParentBigBlock;

    //    AtomicStmt abstAtom;
    //    IdentifierExprSeq origModifies;
    //    CodeTransformations.MakeBranch(procState, parentBB, abstStmt, newlocals, out abstAtom, out origModifies);

    //    Expr inv = proofState.InvariantForProc(procState);

    //    //--------------------------------------------------
    //    AtomicBlock abstBlock = procState.GetAtomicBlock(abstAtom.label);

    //    //------------------------------------------------------
    //    LoopInfo loopInfo = procState.loopInfoMap[whileCmd];
    //    Debug.Assert(loopInfo != null);
    //    loopInfo.CheckAtomicBody(bodyBlock);

    //    Set<APLBlock> succAbst = abstBlock.Successors;
    //    Debug.Assert(succAbst.Count == 1);
    //    //succAbst.PickOne().Pc = loopInfo.Head.Pc = loopInfo.Tail.Pc = bodyBlock.Pc;

    //    //------------------------------------------------------
    //    bool result = false;

    //    //------------------------------------------------------
    //    // check if the spec preserves the invariant
    //    if (!abstBlock.IsInvariant(inv))
    //    {
    //        Output.AddError("Spec does not preserve the invariant!");
    //    }
    //    else
    //    {
    //        //------------------------------------------------------
    //        // check if the spec is reflexive
    //        if (!abstBlock.IsReflexive())
    //        {
    //            Output.AddError("Spec is not reflexive!");
    //        }
    //        else
    //        {
    //            //------------------------------------------------------
    //            loopInfo = procState.loopInfoMap[whileCmd];
    //            Debug.Assert(loopInfo != null);
    //            loopInfo.CheckAtomicBody(bodyBlock);

    //            succAbst = abstBlock.Successors;
    //            Debug.Assert(succAbst.Count == 1);
    //            //succAbst.PickOne().Pc = loopInfo.Head.Pc = loopInfo.Tail.Pc = bodyBlock.Pc;

    //            //------------------------------------------------------
    //            // check the abstraction relation
    //            TPGenerator tpGenLoop = new TPGenerator(abstBlock, new TPGenerator(bodyBlock), false);
    //            TPGenerator tpGenSpec = new TPGenerator(abstBlock, false);

    //            if (!Logic.CheckSimulation(inv, tpGenLoop, tpGenSpec))
    //            {
    //                Output.AddError("Abstraction relation does not hold!");
    //            }
    //            else
    //            {
    //                result = true; // success
    //            }
    //        }
    //    }

    //    //------------------------------------------------------
    //    // if success, replace the body of atom
    //    if (result)
    //    {
    //        // undo the branching
    //        CodeTransformations.UndoMakeBranch(procState, parentBB, null, null);

    //        CodeTransformations.ReplaceStructuredCmd(parentBB, abstAtom);

    //        abstAtom.mover = AtomicStmt.Mover.None;

    //        // add the new modifies to the callers
    //        foreach (IdentifierExpr modExpr in procState.impl.Proc.Modifies)
    //        {
    //            procState.CheckAddModifies(modExpr.Decl, true);
    //        }
    //    }
    //    else
    //    {
    //        // undo the branching
    //        CodeTransformations.UndoMakeBranch(procState, parentBB, newlocals, origModifies);
    //    }

    //    procState.MarkAsTransformed();
        
    //    return result;
    //}
    //static public bool DoRun(ProofState proofState, AtomicBlock atomicBlock, BigBlock parentBB, StmtList abstStmt, VariableSeq localVars)
    //{
    //    //------------------------------------------------------
    //    // check mover type of the body
    //    MoverTypeChecker moverChecker = new MoverTypeChecker();
    //    TPGenerator tpGen = new TPGenerator(atomicBlock); // hide:false
    //    MoverType mtype = moverChecker.Check(proofState, tpGen);
    //    if (mtype.None)
    //    {
    //        Output.AddError("Body of the loop is not a mover!");
    //    }

    //    //------------------------------------------------------
    //    // get the spec block

    //    ProcedureState procState = atomicBlock.procState;
    //    Expr inv = proofState.InvariantForProc(procState);

    //    AtomicStmt atom = atomicBlock.parent;
        
    //    // plug in codeStmt
    //    AtomicStmt abstAtomStmt = new AtomicStmt(Token.NoToken, atom.label, abstStmt);
    //    WhileCmd whileCmd = CodeTransformations.ReplaceWhile(parentBB, abstAtomStmt);
    //    // add new local variables
    //    foreach (Variable var in localVars)
    //    {
    //        procState.impl.LocVars.Add(var);
    //    }

    //    // update the cfg
    //    procState.ForceComputeAtomicBlocks();

    //    // call this later than resolve-typecheck in ForceComputeAtomicBlocks
    //    foreach (Variable var in localVars)
    //    {
    //        procState.AddLocalVar(var);
    //    }

    //    AtomicBlock abstBlock = procState.GetAtomicBlock(atom.label);

    //    //------------------------------------------------------
    //    // check if the spec preserves the invariant
    //    if (!abstBlock.IsInvariant(inv))
    //    {
    //        Output.AddError("Spec does not preserve the invariant!");
    //        return false;
    //    }
        
    //    //------------------------------------------------------
    //    // check if the spec is reflexive
    //    if (!abstBlock.IsReflexive(inv))
    //    {
    //        Output.LogLine("Spec is not reflexive!");
    //        return false;
    //    }       

    //    //------------------------------------------------------
    //    // check the abstraction relation
    //    TPGenerator tpGenLoop = new TPGenerator(abstBlock, new TPGenerator(atomicBlock));
    //    TPGenerator tpGenSpec = new TPGenerator(abstBlock);

    //    if (Logic.CheckSimulation(inv, tpGenLoop, tpGenSpec))
    //    {
    //        // abstraction relation hold, so mark the procedure as modified and quit
    //        Output.AddLine("Abstraction relation holds!");

    //        procState.MarkAsTransformed();

    //        return true; // done
    //    }

    //    //------------------------------------------------------
    //    // now plug the while loop back
    //    Output.LogLine("Could not verify the abstraction between loop and spec!");

    //    // this is failure case:
    //    // plug in the original statement back
    //    CodeTransformations.ReplaceAtom(parentBB, whileCmd);
    //    // remove new local variables
    //    foreach (Variable var in localVars)
    //    {
    //        procState.RemoveLocalVar(var);
    //    }

    //    procState.MarkAsTransformed();

    //    return false;
    //}

    //protected void ReduceLoop(ProofState proofState, LoopBlock loopBlock)
    //{

    //    ProcedureState procState = loopBlock.procState;

    //    // get the loopinfo
    //    LoopInfo loopInfo = loopBlock.LoopInfo;

    //    // find the sibling
    //    Set<Block> backEdges = CodeAnalyses.ComputeBackEdges(loopBlock);
    //    if (backEdges.Count != 1)
    //    {
    //        Output.AddError("There is not one back edge of the loop block !");
    //        return;
    //    }

    //    AtomicBlock sibling = procState.LookupAtomicBlockStarts(backEdges.PickOne());

    //    //--------------------------

    //    // check mover types of the blocks
    //    MoverTypeChecker moverTypeChecker1 = new MoverTypeChecker();
    //    TPGenerator tpGen1 = new TPGenerator(loopBlock); // hide:false
    //    MoverType mover1 = moverTypeChecker1.Check(proofState, tpGen1);

    //    if (mover1.None)
    //    {
    //        Output.LogLine("Loop body is none-mover. Skipping the loop " + loopBlock.UniqueLabel);
    //        return;
    //    }

    //    MoverTypeChecker moverTypeChecker2 = new MoverTypeChecker();
    //    TPGenerator tpGen2 = new TPGenerator(sibling); // hide:false
    //    MoverType mover2 = moverTypeChecker2.Check(proofState, tpGen2);

    //    if (mover2.None)
    //    {
    //        Output.LogLine("Loop body is none-mover. Skipping the loop " + sibling.UniqueLabel);
    //        return;
    //    }

    //    // verify loop block

    //    //-----------------
    //    // get the invariant
    //    Expr invs = proofState.InvariantForProc(procState);

    //    //------------------
    //    // create the spec
    //    VariableSeq modifiedVars = CodeAnalyses.ComputeModifiedVars(loopBlock);

    //    GatedAction spec = new GatedAction(Token.NoToken, gate, transition, modifiedVars, true);
    //    //--------------------------

    //    //// check reflexivity of the spec

    //    //if (!Logic.IsReflexive(loopBlock.procState, Expr.Imp(Expr.And(invs, spec.gate), spec.TransitionPredicate(proofState, procState))))
    //    //{
    //    //    Output.LogLine("Could not verify the loop " + fatomicBlock.UniqueLabel);
    //    //    continue;
    //    //}

    //    //--------------------------

    //    // check the simulation

    //    // first loopBlock <= spec

    //    //procState.EnableCondAssertsToCheck();

    //    TPGenerator thisTPGen1 = new TPGenerator(loopBlock);

    //    TPGenerator thatTPGen1 = new TPGenerator(procState, spec);

    //    if (!Logic.CheckSimulation(invs, thisTPGen1, thatTPGen1))
    //    {
    //        Output.LogLine("Could not verify the spec for the loop !");
    //        //procState.DisableCondAssertsToCheck();
    //        return;
    //    }
    //    //procState.DisableCondAssertsToCheck();

    //    //--------------------------

    //    // first loopBlock <= spec

    //    //procState.EnableCondAssertsToCheck();

    //    TPGenerator thisTPGen2 = new TPGenerator(loopBlock);

    //    TPGenerator thatTPGen2 = new TPGenerator(procState, spec, new TPGenerator(sibling, new TPGenerator(loopBlock)));

    //    if (!Logic.CheckSimulation(invs, thisTPGen2, thatTPGen2))
    //    {
    //        Output.LogLine("Could not verify the spec for the loop !");
    //        //procState.DisableCondAssertsToCheck();
    //        return;
    //    }
    //    //procState.DisableCondAssertsToCheck();



    //    //--------------------------

    //    // reduce the loop now
    //    Output.LogLine("Verified the loop " + loopBlock.UniqueLabel);

    //    // do reduce the loop
    //    loopInfo.Reduce(spec, sibling);
    //}

} // end class ReduceCommand

public class ReduceLoop2Command : ProofCommand
{
    string blocklabel;

    public ReduceLoop2Command(string name)
        : base("reduce")
    {
        this.blocklabel = name;
        desc = "reduce loop2 " + blocklabel;
    }

    public static string Usage()
    {
        return "reduce loop2 atomicBlockLabel@procedureName";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("reduce"))
        {
            if (parser.NextAsString().Equals("loop2"))
            {
                string blocklabel = parser.NextAsString();
                return new ReduceLoop2Command(blocklabel);
            }
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {
        AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);
        if (atomicBlock == null)
        {
            Output.AddError("Atomic block does not exists: " + blocklabel);
            return false;
        }

        ProcedureState procState = atomicBlock.procState;

        //------------------------------------------------------
        // check if the atomic block is the body of a loop
        AtomicStmt atom = atomicBlock.parent;
        BigBlock bb = atom.body.ParentBigBlock.successorBigBlock;
        if (bb.ec == null || !(bb.ec is WhileCmd))
        {
            Output.AddError("Could find the while loop!");
            return false;
        }

        if (!((bb.ec as WhileCmd).Body.BigBlocks.Count == 1))
        {
            Output.AddError("The body of the while loop is not atomic!");
            return false;
        }

        AtomicStmt bodyStmt = (bb.ec as WhileCmd).Body.BigBlocks[0].ec as AtomicStmt;
        if (bodyStmt == null)
        {
            Output.AddError("The body of the while loop is not atomic!");
            return false;
        }

        if (!DoRun(proofState, atomicBlock, procState.GetAtomicBlock(bodyStmt.label), bb))
        {
            Output.AddError("Could not reduce the loop!");
            return false;
        }

        Output.AddLine("Reduce the while loop!");

        return false;
    }

    static public bool DoRun(ProofState proofState, ProcedureState procState, AtomicStmt atomicStmt, AtomicBlock bodyBlock, BigBlock parentBB)
    {
        return DoRun(proofState, procState.GetAtomicBlock(atomicStmt.label), bodyBlock, parentBB);
    }

    static public bool DoRun(ProofState proofState, AtomicBlock specBlock, AtomicBlock bodyBlock, BigBlock parentBB)
    {
        WhileCmd whileCmd = parentBB.ec as WhileCmd;
        Debug.Assert(whileCmd != null);

        ProcedureState procState = bodyBlock.procState;
        //------------------------------------------------------
        // peelout if the guard is not null
        if (whileCmd.Guard != null)
        {
            PeelOutCommand.DoRun(proofState, procState, parentBB);
        }
        Debug.Assert(whileCmd.Guard == null);
        Debug.Assert(MergeCommand.IsAtomic(whileCmd.Body));

        //------------------------------------------------------
        Expr inv = proofState.InvariantForProc(procState);

        //------------------------------------------------------
        // check mover type of the spec
        //if (!specBlock.Mover.Right)
        //{
        //    MoverTypeChecker moverChecker = new MoverTypeChecker(proofState, specBlock);
        //    moverChecker.Run();
        //    if (!moverChecker.Result.Right)
        //    {
        //        Output.AddError("Spec block is not a right mover!");
        //        return false;
        //    }
        //}

        //------------------------------------------------------
        // REMOVED: no need to have the body of the loop a mover
        // check mover type of the body
        //MoverTypeChecker moverChecker2 = new MoverTypeChecker(proofState, bodyBlock);
        //moverChecker2.Run();
        //if (moverChecker2.Result.None)
        //{
        //    Output.AddError("Body of the loop is not a mover!");
        //    return false;
        //}

        //------------------------------------------------------
        LoopInfo loopInfo = procState.loopInfoMap[whileCmd];
        Debug.Assert(loopInfo != null);
        loopInfo.CheckAtomicBody(bodyBlock);
        //loopInfo.Head.Pc = loopInfo.Tail.Pc = bodyBlock.Pc;

        //------------------------------------------------------
        // add goto done to the spec block
        // search for done
        //Block doneBlock = null;
        //if (parentBB.successorBigBlock != null)
        //{
        //    string donelabel = parentBB.successorBigBlock.LabelName;
        //    foreach (APLBlock aplBlock in procState.Atoms)
        //    {
        //        if (aplBlock.startBlock.Label == donelabel)
        //        {
        //            doneBlock = aplBlock.startBlock;
        //            break;
        //        }
        //    }

        //    Set<Block> exitBlocks = specBlock.ExitBlocks;
        //    foreach (Block exitBlock in exitBlocks)
        //    {
        //        if (exitBlock.TransferCmd is GotoCmd)
        //        {
        //            GotoCmd gotoCmd = exitBlock.TransferCmd as GotoCmd;
        //            gotoCmd.AddTarget(doneBlock);
        //        }
        //    }
        //}

        //------------------------------------------------------
        // check the abstraction relation
        TPGenerator tpGenLoop = new TPGenerator(specBlock, new TPGenerator(bodyBlock), false);
        TPGenerator tpGenSpec = new TPGenerator(specBlock, false);

        bool result = false;
        if (!Logic.CheckSimulation(inv, tpGenLoop, tpGenSpec, new VariableSeq()))
        {
            Output.AddError("Abstraction relation does not hold!");
        }
        else
        {
            CodeTransformations.RemoveBigBlock(parentBB);

            result = true; // success
        }

        
        procState.MarkAsTransformed();

        return result;
    }
    //static public bool DoRun(ProofState proofState, AtomicBlock atomicBlock, BigBlock parentBB, StmtList abstStmt, VariableSeq localVars)
    //{
    //    //------------------------------------------------------
    //    // check mover type of the body
    //    MoverTypeChecker moverChecker = new MoverTypeChecker();
    //    TPGenerator tpGen = new TPGenerator(atomicBlock); // hide:false
    //    MoverType mtype = moverChecker.Check(proofState, tpGen);
    //    if (mtype.None)
    //    {
    //        Output.AddError("Body of the loop is not a mover!");
    //    }

    //    //------------------------------------------------------
    //    // get the spec block

    //    ProcedureState procState = atomicBlock.procState;
    //    Expr inv = proofState.InvariantForProc(procState);

    //    AtomicStmt atom = atomicBlock.parent;

    //    // plug in codeStmt
    //    AtomicStmt abstAtomStmt = new AtomicStmt(Token.NoToken, atom.label, abstStmt);
    //    WhileCmd whileCmd = CodeTransformations.ReplaceWhile(parentBB, abstAtomStmt);
    //    // add new local variables
    //    foreach (Variable var in localVars)
    //    {
    //        procState.impl.LocVars.Add(var);
    //    }

    //    // update the cfg
    //    procState.ForceComputeAtomicBlocks();

    //    // call this later than resolve-typecheck in ForceComputeAtomicBlocks
    //    foreach (Variable var in localVars)
    //    {
    //        procState.AddLocalVar(var);
    //    }

    //    AtomicBlock abstBlock = procState.GetAtomicBlock(atom.label);

    //    //------------------------------------------------------
    //    // check if the spec preserves the invariant
    //    if (!abstBlock.IsInvariant(inv))
    //    {
    //        Output.AddError("Spec does not preserve the invariant!");
    //        return false;
    //    }

    //    //------------------------------------------------------
    //    // check if the spec is reflexive
    //    if (!abstBlock.IsReflexive(inv))
    //    {
    //        Output.LogLine("Spec is not reflexive!");
    //        return false;
    //    }       

    //    //------------------------------------------------------
    //    // check the abstraction relation
    //    TPGenerator tpGenLoop = new TPGenerator(abstBlock, new TPGenerator(atomicBlock));
    //    TPGenerator tpGenSpec = new TPGenerator(abstBlock);

    //    if (Logic.CheckSimulation(inv, tpGenLoop, tpGenSpec))
    //    {
    //        // abstraction relation hold, so mark the procedure as modified and quit
    //        Output.AddLine("Abstraction relation holds!");

    //        procState.MarkAsTransformed();

    //        return true; // done
    //    }

    //    //------------------------------------------------------
    //    // now plug the while loop back
    //    Output.LogLine("Could not verify the abstraction between loop and spec!");

    //    // this is failure case:
    //    // plug in the original statement back
    //    CodeTransformations.ReplaceAtom(parentBB, whileCmd);
    //    // remove new local variables
    //    foreach (Variable var in localVars)
    //    {
    //        procState.RemoveLocalVar(var);
    //    }

    //    procState.MarkAsTransformed();

    //    return false;
    //}

    //protected void ReduceLoop(ProofState proofState, LoopBlock loopBlock)
    //{

    //    ProcedureState procState = loopBlock.procState;

    //    // get the loopinfo
    //    LoopInfo loopInfo = loopBlock.LoopInfo;

    //    // find the sibling
    //    Set<Block> backEdges = CodeAnalyses.ComputeBackEdges(loopBlock);
    //    if (backEdges.Count != 1)
    //    {
    //        Output.AddError("There is not one back edge of the loop block !");
    //        return;
    //    }

    //    AtomicBlock sibling = procState.LookupAtomicBlockStarts(backEdges.PickOne());

    //    //--------------------------

    //    // check mover types of the blocks
    //    MoverTypeChecker moverTypeChecker1 = new MoverTypeChecker();
    //    TPGenerator tpGen1 = new TPGenerator(loopBlock); // hide:false
    //    MoverType mover1 = moverTypeChecker1.Check(proofState, tpGen1);

    //    if (mover1.None)
    //    {
    //        Output.LogLine("Loop body is none-mover. Skipping the loop " + loopBlock.UniqueLabel);
    //        return;
    //    }

    //    MoverTypeChecker moverTypeChecker2 = new MoverTypeChecker();
    //    TPGenerator tpGen2 = new TPGenerator(sibling); // hide:false
    //    MoverType mover2 = moverTypeChecker2.Check(proofState, tpGen2);

    //    if (mover2.None)
    //    {
    //        Output.LogLine("Loop body is none-mover. Skipping the loop " + sibling.UniqueLabel);
    //        return;
    //    }

    //    // verify loop block

    //    //-----------------
    //    // get the invariant
    //    Expr invs = proofState.InvariantForProc(procState);

    //    //------------------
    //    // create the spec
    //    VariableSeq modifiedVars = CodeAnalyses.ComputeModifiedVars(loopBlock);

    //    GatedAction spec = new GatedAction(Token.NoToken, gate, transition, modifiedVars, true);
    //    //--------------------------

    //    //// check reflexivity of the spec

    //    //if (!Logic.IsReflexive(loopBlock.procState, Expr.Imp(Expr.And(invs, spec.gate), spec.TransitionPredicate(proofState, procState))))
    //    //{
    //    //    Output.LogLine("Could not verify the loop " + fatomicBlock.UniqueLabel);
    //    //    continue;
    //    //}

    //    //--------------------------

    //    // check the simulation

    //    // first loopBlock <= spec

    //    //procState.EnableCondAssertsToCheck();

    //    TPGenerator thisTPGen1 = new TPGenerator(loopBlock);

    //    TPGenerator thatTPGen1 = new TPGenerator(procState, spec);

    //    if (!Logic.CheckSimulation(invs, thisTPGen1, thatTPGen1))
    //    {
    //        Output.LogLine("Could not verify the spec for the loop !");
    //        //procState.DisableCondAssertsToCheck();
    //        return;
    //    }
    //    //procState.DisableCondAssertsToCheck();

    //    //--------------------------

    //    // first loopBlock <= spec

    //    //procState.EnableCondAssertsToCheck();

    //    TPGenerator thisTPGen2 = new TPGenerator(loopBlock);

    //    TPGenerator thatTPGen2 = new TPGenerator(procState, spec, new TPGenerator(sibling, new TPGenerator(loopBlock)));

    //    if (!Logic.CheckSimulation(invs, thisTPGen2, thatTPGen2))
    //    {
    //        Output.LogLine("Could not verify the spec for the loop !");
    //        //procState.DisableCondAssertsToCheck();
    //        return;
    //    }
    //    //procState.DisableCondAssertsToCheck();



    //    //--------------------------

    //    // reduce the loop now
    //    Output.LogLine("Verified the loop " + loopBlock.UniqueLabel);

    //    // do reduce the loop
    //    loopInfo.Reduce(spec, sibling);
    //}

} // end class ReduceCommand

} // end namespace QED