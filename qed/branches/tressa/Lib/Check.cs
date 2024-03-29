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
                RelaxCommand.DoRun(proofState, procState, atomicBlock.Label);
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

            DoRun(proofState, atomicBlock.procState, atomicBlock.Label);
            return false;
        }

        static public void DoRun(ProofState proofState, ProcedureState procState, string label)
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
                        atomicBlock.Relax(discharged, false);
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
                Debug.Assert(labels.Count > 0);

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
                    b.Cmds = CodeTransformations.RelaxCmdSeq(b.Cmds, cmds, true);
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

    // for tressa
    public class CheckTressa : ProofCommand
    {
        public enum Kind { Procedure, Block }

        string procname;
        Kind kind;

        public CheckTressa(string name, Kind k)
            : base("checktressa")
        {
            this.procname = name;
            this.kind = k;
            desc = "checktressa " + procname + " " + (kind == Kind.Procedure ? "proc" : "block");
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("checktressa"))
            {
                string procname = parser.NextAsString();
                Kind kind = Kind.Block;
                if (parser.HasNext())
                {
                    string k = parser.NextAsString();
                    if (k == "proc")
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
                return new CheckTressa(procname, kind);
            }
            return null;
        }

        public static string Usage()
        {
            return "checktressa all|procedureName [proc|block]";
        }

        override public bool Run(ProofState proofState)
        {

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

        static public void DoRun(ProofState proofState, ProcedureState procState, Kind kind)
        {
            procState.ComputeAtomicBlocks();

            if (kind == Kind.Block)
            {
                foreach (AtomicBlock atomicBlock in procState.AtomicBlocks)
                {
                    // for tressa; this has to be re-written to account for tressa's only.
                    // RelaxCommand.DoRun(proofState, procState, atomicBlock.Label);
                    Discharge(proofState, procState, atomicBlock.Label);
                }
            }
            else
            {
                //DoSeqAnalysis(proofState, procState);
                throw new NotImplementedException();
            }
        }

        static public void Discharge(ProofState prfst, ProcedureState prcst, String lbl)
        {
            Expr inv = prfst.InvariantForProc(prcst);

            prcst.ComputeAtomicBlocks();
            AtomicBlock ab = prcst.GetAtomicBlock(lbl);
            Expr exit = ab.ExitPredicate(inv);
            bool isDischarged = Prover.GetInstance().CheckValid(exit);

            if (isDischarged)
            {
                ab.RelaxTressa();
                Output.AddLine("All tressa claims are discharged in block: " + lbl);
            }
            else 
            {
                Output.AddLine("At least one tressa claim cannot be discharged in block: " + lbl);
            }
            #region commented out
            ////procState.EnableCondAssumesForLoops();
            ////procState.EnableCondAssertsToCheck();

            //int total = 0;
            //bool any = false;
            //do
            //{
            //    any = false;
            //    prcst.ComputeAtomicBlocks();
            //    AtomicBlock atomicBlock = prcst.GetAtomicBlock(lbl);
            //    while (true)
            //    {
            //        CmdSeq discharged = DoSeqAnalysisForTressa(prfst, atomicBlock, inv);
            //        if (discharged.Length > 0)
            //        {
            //            any = true;
            //            total += discharged.Length;
            //            atomicBlock.Relax(discharged, false);
            //        }
            //        else
            //        {
            //            break;
            //        }
            //    }

            //    prcst.MarkAsTransformed();

            //} while (any);

            //if (total > 0)
            //{
            //    Output.AddLine(total.ToString() + " assertions discharged in block: " + lbl);
            //}

            //}
            #endregion
        }



    } // end class CheckTressa




} // end namespace QED
