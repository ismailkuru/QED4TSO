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
  

public class CheckCommand : ProofCommand
{
    public enum Kind { Procedure, Block }

	string procname;
    Kind kind;

	public CheckCommand(string name, Kind k)
		: base("check")
	{
		this.procname = name;
        this.kind = k;
		desc = "check " + procname + " " + (kind == Kind.Procedure ? "proc" : "block");
	}

    public CheckCommand(string name)
        : base("check")
    {
        this.procname = name;
        this.kind = Kind.Block;
        desc = "check " + procname + " block";
    }

    public CheckCommand()
        : base("check")
    {
        this.procname = "all";
        this.kind = Kind.Block;
        desc = "check all block";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("check"))
        {
            string procname = parser.NextAsString();
            Kind kind = Kind.Block;
            if (parser.HasNext())
            {
                string k = parser.NextAsString();
                if(k == "proc")
                {
                    kind = Kind.Procedure;
                }
                else if (k == "block")
                {
                    kind = Kind.Block;
                }
                else
                {
                    return null; // unrecognized
                }
            }
            return new CheckCommand(procname, kind);
        }
        return null;
    }

    public static string Usage()
    {
        return "check all|procedureName [proc|block]";
    }

	override public bool Run(ProofState proofState) {

        if (procname == "all")
        {
            DoRun(proofState, proofState.ProcedureStates, this.kind);
        }
        else
        {
            ProcedureState procState = proofState.GetProcedureState(procname);
            if (procState == null)
            {
                Output.AddError("Procedure does not exist: " + procname);
                return false;
            }
            DoRun(proofState, procState, this.kind);
        }

		return false;
	}

    static public void DoRun(ProofState proofState, List<ProcedureState> procStates, Kind kind)
    {
        foreach (ProcedureState procState in procStates)
        {
            DoRun(proofState, procState, kind);
        }
    }
	
	static public void DoRun(ProofState proofState, ProcedureState procState, Kind kind) {
		procState.ComputeAtomicBlocks();

        if (kind == Kind.Block)
        {
            foreach (AtomicBlock atomicBlock in procState.AtomicBlocks)
            {
                RelaxCommand.DoRelax(proofState, procState, atomicBlock.Label, proofState.config.GetBool("Check", "AssumeProvedAsserts", false));
            }
        }
        else
        {
            //DoSeqAnalysis(proofState, procState);
            throw new NotImplementedException();
        }
	}

    //static private CmdSeq DoSeqAnalysis(ProofState proofState, ProcedureState procState)
    //{
    //    Expr inv = proofState.InvariantForProc(procState);

    //    RelyGuarantee rg = new RelyGuarantee(inv, Expr.True, Expr.True);
        
    //    // this should terminate
    //    while (!rg.CheckProcedure(proofState, procState))
    //    {
    //        // collect failed commands
    //        CmdSeq cmds = new CmdSeq();
    //        Set<string> labels = Prover.GetInstance().GetErrorLabels();
    //        foreach (string label in labels)
    //        {
    //            Cmd cmd = LabeledExpr.GetAbsyByLabel(label) as Cmd;
    //            if (cmd != null)
    //            {
    //                Debug.Assert(cmd is AssertCmd || cmd is GatedAction);
    //                cmds.Add(cmd);
    //            }
    //        }
    //        // remove failed commands
    //        foreach (Block b in atomicBlock.Blocks)
    //        {
    //            b.Cmds = CodeTransformations.RelaxCmdSeq(b.Cmds, cmds);
    //        }

    //        atomicBlock.MarkAsTransformed();
    //        gate = atomicBlock.GatePredicate(Expr.True);
    //        condition = Expr.Imp(inv, gate);
    //    }

    //    CmdSeq discharged = new CmdSeq();
    //    // collect remaining assertions
    //    foreach (Block b in atomicBlock.Blocks)
    //    {
    //        foreach (Cmd cmd in b.Cmds)
    //        {
    //            if (cmd is AssertCmd || cmd is GatedAction)
    //            {
    //                discharged.Add(cmd);
    //            }
    //        }
    //    }
    //    return discharged;
    //}
	
} // end class CheckCommand

public class CheckLoopCommand : ProofCommand
{
    string blocklabel;

    public CheckLoopCommand(string label)
        : base("check loop")
    {
        this.blocklabel = label;

        desc = "check loop " + blocklabel;
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("check"))
        {
            if (parser.NextAsString().Equals("loop"))
            {
                string label = parser.NextAsString();
                return new CheckLoopCommand(label);
            }
        }
        return null;
    }

    public static string Usage()
    {
        return "check loop blockLabel";
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

        //--------------------
        bool GatherCmdOnlyBlocks = proofState.config.GetBool("Optimize", "GatherCmdOnlyBlocks", true);
        proofState.config.Set("Optimize", "GatherCmdOnlyBlocks", false);

        bool result = DoRun(proofState, procState, atomicBlock);

        proofState.config.Set("Optimize", "GatherCmdOnlyBlocks", GatherCmdOnlyBlocks);

        //--------------------
        if (result)
        {
            Output.AddLine("Command run successfully!");
        }
        else
        {
            Output.AddError("Command failed!");
        }

        return false;

    }

    static public bool DoRun(ProofState proofState, ProcedureState procState, AtomicBlock atomicBlock)
    {
        //------------------------------------------------------
        // check if the atomic block is the body of a loop
        AtomicStmt atomB = atomicBlock.parent;
        BigBlock bbB = atomB.body.ParentBigBlock;
        BigBlock bbWhile = atomB.body.ParentContext.ParentBigBlock;
        if (bbWhile.ec == null || !(bbWhile.ec is WhileCmd) || !((bbWhile.ec as WhileCmd).Body.BigBlocks.Count == 1) || !((bbWhile.ec as WhileCmd).Body.BigBlocks[0] == atomB.body.ParentBigBlock))
        {
            Output.AddError("Given atomic block is not the body of a while loop!");
            return false;
        }

        // get the other blocks
        AtomicStmt atomA = null;
        AtomicStmt atomC = null;
        BigBlock bbA = null;
        BigBlock bbC = null;

        WhileCmd whileCmd = bbWhile.ec as WhileCmd;
        int index = -1;
        StmtList parentStmt = Qoogie.GetParentContext(bbWhile, procState.Body, out index);
        Debug.Assert(index >= 0);
        if (index > 0)
        {
            bbA = parentStmt.BigBlocks[index - 1];
            atomA = bbA.ec as AtomicStmt;
            
        }
        if (index < parentStmt.BigBlocks.Count - 1)
        {
            bbC = parentStmt.BigBlocks[index + 1];
            atomC = bbC.ec as AtomicStmt;
        }

        // at least one of atomA and atomC must exists
        Debug.Assert(atomA != null || atomC != null);

        Output.AddLine("Checking mover type of " + atomB.label);
        MCache.Reset();
        MoverTypeChecker moverChecker = new MoverTypeChecker(proofState, procState.GetAtomicBlock(atomB.label));
        moverChecker.Run();
        if (atomB.Mover.None)
        {
            Output.AddError("Atomic block in the loop must be a mover. Found non-mover!");
            return false;
        }

        if (atomA != null)
        {
            Output.AddLine("Checking mover type of " + atomA.label);
            MCache.Reset();
            moverChecker = new MoverTypeChecker(proofState, procState.GetAtomicBlock(atomA.label));
            moverChecker.Run();
        }

        if (atomC != null)
        {
            Output.AddLine("Checking mover type of " + atomC.label);
            MCache.Reset();
            moverChecker = new MoverTypeChecker(proofState, procState.GetAtomicBlock(atomC.label));
            moverChecker.Run();
        }

        // only check for right mover for now
        if (atomA == null || MoverType.ComposeSeq(atomA.Mover, atomB.Mover).Right == false)
        {
            Output.AddError("Atomic block before the loop and in the loop must be both right movers!");
            return false;
        }

        //--------------------------------
        // now check the assertions
        
        StmtList copyB = new StmtDuplicator().VisitStmtList(atomB.body);

        // 1. A-B

        Output.AddLine("Phase: A ; B");

        List<BigBlock> refbbA = new List<BigBlock>(atomA.body.BigBlocks);

        atomA.body.BigBlocks.Clear();
        atomA.body.BigBlocks.AddRange(refbbA);
        atomA.body.BigBlocks.AddRange(copyB.BigBlocks);

        procState.MarkAsTransformed();

        RelaxCommand.DoRelax(proofState, procState, atomA.label, true);

        procState.ComputeAtomicBlocks();

        // check if all assertions are discharged
        int count = 0;
        Set<BigBlock> bbs = new BigBlocksCollector().Collect(copyB);
        foreach (BigBlock bb in bbs)
        {
            foreach (Cmd cmd in bb.simpleCmds)
            {
                if (cmd is AssertCmd)
                {
                    ++count;
                    break;
                }
            }
            if (count > 0) break;
        }

        // put original A back
        atomA.body.BigBlocks.Clear();
        atomA.body.BigBlocks.AddRange(refbbA);

        if (count > 0)
        {
            Output.AddError("Not all assertions in the while body are discharged!");
            procState.MarkAsTransformed();
            return false;
        }

        // 2. B-B

        Output.AddLine("Phase: B ; B");

        List<BigBlock> refbbB = new List<BigBlock>(atomB.body.BigBlocks);

        atomB.body.BigBlocks.Clear();
        atomB.body.BigBlocks.AddRange(copyB.BigBlocks);
        atomB.body.BigBlocks.AddRange(refbbB);

        procState.MarkAsTransformed();

        RelaxCommand.DoRelax(proofState, procState, atomB.label, true);

        procState.ComputeAtomicBlocks();

        // check if all assertions are discharged
        count = 0;
        bbs = new BigBlocksCollector().Collect(atomB.body);
        foreach (BigBlock bb in bbs)
        {
            foreach (Cmd cmd in bb.simpleCmds)
            {
                if (cmd is AssertCmd)
                {
                    ++count;
                    break;
                }
            }
            if (count > 0) break;
        }

        // put original B back
        atomB.body.BigBlocks.Clear();
        atomB.body.BigBlocks.AddRange(refbbB);

        if (count > 0)
        {
            Output.AddError("Not all assertions in the while body are discharged!");
            procState.MarkAsTransformed();
            return false;
        }

        Output.AddLine("Discharged all the assertions in the while body!");

        // 2. B-C

        Output.AddLine("Phase: B ; C");

        List<BigBlock> refbbC = new List<BigBlock>(atomC.body.BigBlocks);

        atomC.body.BigBlocks.Clear();
        atomC.body.BigBlocks.AddRange(copyB.BigBlocks);
        atomC.body.BigBlocks.AddRange(refbbC);

        procState.MarkAsTransformed();

        RelaxCommand.DoRelax(proofState, procState, atomC.label, true);

        procState.ComputeAtomicBlocks();

        // put original C back
        atomC.body.BigBlocks.Clear();
        atomC.body.BigBlocks.AddRange(refbbC);

        procState.MarkAsTransformed();

        return true;
    }

} // end class CheckLoopCommand


    // TODO: make relax have a "all" gactlabel to relax all gated actions
    public class RelaxCommand : ProofCommand
    {
        public string blockname;

        public RelaxCommand(string b)
            : base("relax")
        {
            this.blockname = b;

            desc = "relax " + blockname;
        }

        public static string Usage()
        {
            return "relax atomicBlockLabel@procedureName";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("relax"))
            {
                string blockname = parser.NextAsString();
                return new RelaxCommand(blockname);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {
            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blockname);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exist: " + blockname);
                return false;
            }

            DoRelax(proofState, atomicBlock.procState, atomicBlock.Label, proofState.config.GetBool("Check", "AssumeProvedAsserts", false));
            return false;
        }

        static public void DoRelax(ProofState proofState, ProcedureState procState, string label, bool makeAssume)
        {
            Expr inv = proofState.InvariantForProc(procState);

            //procState.EnableCondAssumesForLoops();
            //procState.EnableCondAssertsToCheck();

            int total = 0;
            bool any = false;
            do
            {
                any = false;
                procState.ComputeAtomicBlocks();
                AtomicBlock atomicBlock = procState.GetAtomicBlock(label);
                while (true)
                {
                    CmdSeq discharged = DoSeqAnalysis(proofState, atomicBlock, inv);
                    if (discharged.Length > 0)
                    {
                        any = true;
                        total += discharged.Length;
                        atomicBlock.Relax(discharged, makeAssume);
                    }
                    else
                    {
                        break;
                    }
                }
                procState.MarkAsTransformed();

            } while (any);

            if(total > 0)
            {
                Output.AddLine(total.ToString() + " assertions discharged in block: " + label);
            }

            //procState.DisableCondAssumesForLoops();
            //procState.DisableCondAssertsToCheck();
        }

        static private CmdSeq DoSeqAnalysis(ProofState proofState, AtomicBlock atomicBlock, Expr inv)
        {
            Expr gate = atomicBlock.GatePredicate(Expr.True);
            Expr condition = Expr.Imp(inv, gate);

            // this should terminate
            while(!Prover.GetInstance().CheckValid(condition))
            {
                // collect failed commands
                CmdSeq cmds = new CmdSeq();
                Set<string> labels = Prover.GetInstance().GetErrorLabels();
                if (labels.Count == 0)
                {
                    return new CmdSeq(); // nothing discharged
                }

                foreach (string label in labels)
                {
                    Cmd cmd = LabeledExpr.GetAbsyByLabel(label) as Cmd;
                    if (cmd != null)
                    {
                        Debug.Assert(cmd is AssertCmd || cmd is GatedAction);
                        cmds.Add(cmd);
                    }
                }
                // remove failed commands
                foreach (Block b in atomicBlock.Blocks)
                {
                    CodeTransformations.RelaxCmdSeq(b.Cmds, cmds, false);
                }

                atomicBlock.MarkAsTransformed();
                gate = atomicBlock.GatePredicate(Expr.True);
                condition = Expr.Imp(inv, gate);
            }

            CmdSeq discharged = new CmdSeq();
            // collect remaining assertions
            foreach (Block b in atomicBlock.Blocks)
            {
                foreach (Cmd cmd in b.Cmds)
                {
                    if (cmd is AssertCmd)
                    {
                        discharged.Add(cmd);
                    }
                    else if (cmd is GatedAction && (!(cmd as GatedAction).gate.Equals(Expr.True)))
                    {
                        discharged.Add(cmd);
                    }
                }
            }
            return discharged;
        }

    } // end class RelaxCommand



} // end namespace QED
