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

namespace QED
{

    using System;
    using System.IO;
    using System.Collections;
    using System.Collections.Generic;
    using PureCollections;
    using Microsoft.Boogie;
    using BoogiePL;
    using System.Diagnostics;

    // Tso
    public class RemoveProcedureCommand : ProofCommand {
        string procName;

        public RemoveProcedureCommand(string procname) 
            :base("removeproc")
        {
            this.procName = procname;
            desc = "removeproc " + procName;
        }
        public static string Usage() {
            return "removeproc procedureName";        
        }
        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("removeproc"))
            {
                string procedureName = parser.NextAsString();
                //string afterbefore = parser.NextAsString();
                return new RemoveProcedureCommand(procedureName);
            }
            return null;
        }
        override public bool Run(ProofState proofState)
        {
            ProcedureState procState = proofState.GetProcedureState(procName);      
            proofState.RemoveProcedureState(procState);
           
            return true;
        }
    
    }

    // Tso 
    public class AssertWDIsemptyBufferCommand : ProofCommand
    {
        string atomicLabel;

        public AssertWDIsemptyBufferCommand(string block)
            : base("assertwd")
        {
            this.atomicLabel = block;

            desc = "assertwd " + atomicLabel;
        }

        public static string Usage()
        {
            return "assertwd callLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("assertwd"))
            {
                string blocklabel = parser.NextAsString();
                //string afterbefore = parser.NextAsString();
                return new AssertWDIsemptyBufferCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {
            // Take for this 
            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomicLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomicLabel);
                return false;
            }



            //   Output.AddLine("Block labe is " + atomicBlock.Label);
            ProcedureState procState = atomicBlock.procState;
            // Output.AddLine(" Proc name is " + procState.impl.Proc.Name);

            procState.AsserWDIsEmptyBuffer(proofState, procState, atomicBlock.parent);
            procState.MarkAsTransformed();


            return true;
        }

    }



    //Tso
    public class ElimIsAtHeadAndDrainIfCommand : ProofCommand
    {
        string atomLabel;

        public ElimIsAtHeadAndDrainIfCommand(string block)
            : base("elimisatdrainif")
        {
            this.atomLabel = block;

            desc = "elimisatdrainif " + atomLabel;
        }

        public static string Usage()
        {
            return "elimisatdrainif atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("elimisatdrainif"))
            {
                string blocklabel = parser.NextAsString();
                //string afterbefore = parser.NextAsString();
                return new ElimIsAtHeadAndDrainIfCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;
            procState.EliminateIsAtHeadAndDrainIf(proofState, procState, atomicBlock.parent);
            procState.MarkAsTransformed();


            return true;
        }


    }

    //Tso
    public class ElimIsAtHeadAndDrainIfAsmCommand : ProofCommand
    {

        string atomLabel;

        public ElimIsAtHeadAndDrainIfAsmCommand(string block)
            : base("elimisatdrainifasm")
        {
            this.atomLabel = block;

            desc = "elimisatdrainifasm " + atomLabel;
        }

        public static string Usage()
        {
            return "elimisatdrainifasm atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("elimisatdrainifasm"))
            {
                string blocklabel = parser.NextAsString();
                //string afterbefore = parser.NextAsString();
                return new ElimIsAtHeadAndDrainIfAsmCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;
            procState.EliminateIsAtHeadAndDrainAsmIf(proofState, procState, atomicBlock.parent);
            procState.MarkAsTransformed();


            return true;
        }

    }


    //Tso
    public class ElimSingleDrainIfAsmCommand : ProofCommand
    {

        string atomLabel;



        public ElimSingleDrainIfAsmCommand(string block)
            : base("elimsdrainifasm")
        {
            this.atomLabel = block;

            desc = "elimsdrainifasm " + atomLabel;
        }

        public static string Usage()
        {
            return "elimsdrainifasm atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("elimsdrainifasm"))
            {
                string blocklabel = parser.NextAsString();
                //string afterbefore = parser.NextAsString();
                return new ElimSingleDrainIfAsmCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;
            procState.EliminateSingleDrainHeadAsmIf(proofState, procState, atomicBlock.parent);
            procState.MarkAsTransformed();


            return true;
        }

    }

    //Tso
    public class ElimSingleDrainIfCommand : ProofCommand
    {

        string atomLabel;



        public ElimSingleDrainIfCommand(string block)
            : base("elimsdrainif")
        {
            this.atomLabel = block;

            desc = "elimsdrainif " + atomLabel;
        }

        public static string Usage()
        {
            return "elimsdrainif atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("elimsdrainif"))
            {
                string blocklabel = parser.NextAsString();
                //string afterbefore = parser.NextAsString();
                return new ElimSingleDrainIfCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;
            procState.EliminateSingleDrainHeadIf(proofState, procState, atomicBlock.parent);
            procState.MarkAsTransformed();


            return true;
        }

    }
    //Tso
    public class ElimIsAtHeadAndDrainAsmCommand : ProofCommand
    {

        string atomLabel;



        public ElimIsAtHeadAndDrainAsmCommand(string block)
            : base("elimisatdrainasm")
        {
            this.atomLabel = block;

            desc = "elimisatdrainasm " + atomLabel;
        }

        public static string Usage()
        {
            return "elimisatdrainasm atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("elimisatdrainasm"))
            {
                string blocklabel = parser.NextAsString();
                //string afterbefore = parser.NextAsString();
                return new ElimIsAtHeadAndDrainAsmCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;
            procState.EliminateIsAtHeadAndDrainAsm(proofState, procState, atomicBlock.parent);
            procState.MarkAsTransformed();


            return true;
        }

    }

    //Tso
    public class ElimIsAtHeadAndDrainCommand : ProofCommand
    {

        string atomLabel;



        public ElimIsAtHeadAndDrainCommand(string block)
            : base("elimisatdrain")
        {
            this.atomLabel = block;

            desc = "elimisatdrain " + atomLabel;
        }

        public static string Usage()
        {
            return "elimisatdrain atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("elimisatdrain"))
            {
                string blocklabel = parser.NextAsString();
                //string afterbefore = parser.NextAsString();
                return new ElimIsAtHeadAndDrainCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;
            procState.EliminateIsAtHeadAndDrain(proofState, procState, atomicBlock.parent);
            procState.MarkAsTransformed();


            return true;
        }

    }

    //Tso
    public class ElimSingleDrainAsmCommand : ProofCommand
    {
        string atomLabel;



        public ElimSingleDrainAsmCommand(string block)
            : base("elimsdrainasm")
        {
            this.atomLabel = block;

            desc = "elimsdrainasm " + atomLabel;
        }

        public static string Usage()
        {
            return "elimsdrainasm atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("elimsdrainasm"))
            {
                string blocklabel = parser.NextAsString();
                //string afterbefore = parser.NextAsString();
                return new ElimSingleDrainAsmCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;
            procState.EliminateSingleDrainHeadAsm(proofState, procState, atomicBlock.parent);
            procState.MarkAsTransformed();


            return true;
        }


    }

    //Tso
    public class ElimSingleDrainCommand : ProofCommand
    {

        string atomLabel;



        public ElimSingleDrainCommand(string block)
            : base("elimsdrain")
        {
            this.atomLabel = block;

            desc = "elimsdrain " + atomLabel;
        }

        public static string Usage()
        {
            return "elimsdrain atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("elimsdrain"))
            {
                string blocklabel = parser.NextAsString();
                //string afterbefore = parser.NextAsString();
                return new ElimSingleDrainCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;
            procState.EliminateSingleDrainHead(proofState, procState, atomicBlock.parent);
            procState.MarkAsTransformed();


            return true;
        }

    }

    // Tso
    public class HoistCommand : ProofCommand
    {
        string atomLabel;

        string afterbefore;

        public HoistCommand(string block, string branch)
            : base("hoist")
        {
            this.atomLabel = block;
            this.afterbefore = branch;
            desc = "hoist " + atomLabel + " " + afterbefore;
        }

        public static string Usage()
        {
            return "hoist atomicBlockLabel@procedureName before|after";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("hoist"))
            {
                string blocklabel = parser.NextAsString();
                string afterbefore = parser.NextAsString();
                return new HoistCommand(blocklabel, afterbefore);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;

            if (!CodeTransformations.Hoist(procState, atomicBlock.parent, afterbefore == "after"))
            {
                Output.AddError("Error in hoisting " + atomLabel);
            }
            else
            {
                procState.MarkAsTransformed();
            }

            return false;

        }
    } // end class Hoist

    public class SplitCommand : ProofCommand
    {
        string atomLabel;
        public Kind kind;
        public enum Kind { If, While }

        public SplitCommand(string block, Kind k)
            : base("split")
        {
            this.atomLabel = block;
            this.kind = k;
            desc = "split " + (kind == Kind.If ? "if" : "while") + " " + atomLabel;
        }

        public static string Usage()
        {
            return "split if|while atomicBlockLabel@procedureName";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("split"))
            {
                string kind = parser.NextAsString();
                string blocklabel = parser.NextAsString();

                return new SplitCommand(blocklabel, kind == "if" ? Kind.If : Kind.While);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;

            if (this.kind == Kind.If)
            {
                if (!CodeTransformations.SplitIf(procState, atomicBlock.parent))
                {
                    Output.AddError("Error in splitting if: " + atomLabel);
                }
                else
                {
                    procState.MarkAsTransformed();
                }
            }

            return false;

        }
    } // end class Hoist


    // Added for TSO
    public class UnzipCommand : ProofCommand
    {

        string atomLabel;

        public UnzipCommand(string block)
            : base("unzip")
        {
            this.atomLabel = block;
            desc = "unzip " + atomLabel;
        }

        public static string Usage()
        {
            return "unzip atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("unzip"))
            {
                string blocklabel = parser.NextAsString();

                return new UnzipCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;

            if (!CodeTransformations.Unzip(procState, atomicBlock.parent))
            {
                Output.AddError("Error in unzipping " + atomLabel);
            }
            else
            {
                procState.MarkAsTransformed();
            }

            return false;

        }


    }
    // Added for TSO
    public class ReduceToSingleDrainAtHeadCommand : ProofCommand
    {

        string blocklabel;
        public ReduceToSingleDrainAtHeadCommand(string name)
            : base("star2single")
        {
            this.blocklabel = name;

            desc = "star2single " + blocklabel;
        }

        public static string Usage()
        {
            return "star2single atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("star2single"))
            {
                string blocklabel = parser.NextAsString();
                return new ReduceToSingleDrainAtHeadCommand(blocklabel);
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

            if (DoRun(proofState, procState, atomicBlock.parent) == false)
            {
                Output.AddError("Could not reduce to !");
                return false;
            }

            return false;
        }

        public bool DoRun(ProofState proofState, ProcedureState procState, AtomicStmt atomStmt)
        {


            int index;
            int startIndex;

            StmtList parentStmt = Qoogie.GetParentContext(atomStmt, procState.Body, out index);
            Debug.Assert(parentStmt.BigBlocks[index].ec == atomStmt);
            BigBlock assumeBlock = parentStmt.BigBlocks[index];


            for (startIndex = index - 2; startIndex >= 0; startIndex = startIndex - 2)
            {
                // Check for while* drainHead()
                WhileCmd wcm = parentStmt.BigBlocks[startIndex + 1].ec as WhileCmd;

                if (wcm.Body.BigBlocks[0].ec is CallStmt)
                {
                    CallStmt callStmt = wcm.Body.BigBlocks[0].ec as CallStmt;
                    if (callStmt.cmd.Proc.Name != "drainHead")
                    {
                        Output.AddError(" while(*) {call drainHead() } can not be found ");
                        return false;
                    }
                }

                // Check for write
                CallStmt wrt = parentStmt.BigBlocks[startIndex].ec as CallStmt;
                if (wrt.cmd.Proc.Name != "write")
                {
                    Output.AddError(" write_X function can be found in block " + parentStmt.BigBlocks[startIndex].LabelName);
                    return false;
                }
                //check is over
                List<Expr> pipeIn = new List<Expr>();
                List<IdentifierExpr> pipeOut = new List<IdentifierExpr>();

                // Create new CallCmd
                Expr inIH = Qoogie.DuplicateExpr(wrt.cmd.Outs[0]);
                pipeIn.Add(inIH);
                // Create CallCmd
                CallCmd isAtH = new CallCmd(Token.NoToken, "isAtHeadAndDrain", pipeIn, pipeOut);
                // Create new Atomic Block and insert Call inside it
                AtomicStmt combined = Qoogie.MakeAtomicStmt(new CmdSeq(isAtH), null, null);
                BigBlock newbb = new BigBlock(Token.NoToken, combined.label, new CmdSeq(), combined, null);

                parentStmt.BigBlocks.RemoveAt(startIndex + 1);
                CodeTransformations.InsertAt(parentStmt, newbb, startIndex + 1);
                procState.MarkAsTransformed();

                AtomicBlock ab = proofState.GetAtomicBlockByLabel(newbb.LabelName);
                ab.InstrumentEntry(new CmdSeq(wrt.cmd));
                parentStmt.BigBlocks.RemoveAt(startIndex);
                procState.MarkAsTransformed();
            }



            procState.MarkAsTransformed();

            return true;
        }


    }
    // TSO 



    //TSO
    /*AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);
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
            if (bb.ec == null || !(bb.ec is WhileCmd))
            {
                Output.AddError("Given atomic block is not in the body of a while loop!");
                return false;
            }

            DoRun(proofState, atomicBlock.procState, bb);

            procState.MarkAsTransformed();

            return false;*/

    // Added for TSO
    // This class has to be recapped again for the following points
    //      Assume that we have while(*){call drainHead()} ; BBs
    // BBs is a list of big-blocks for every big block in BBS
    // If bb.ec is a AssumeCmd
    // If bb.ec is a CallStmt
    // If bb.ec is a IfCmd
    // If bb.ec is a WhileCmd

    public class IsAssumeFalseCommand : ProofCommand
    {
        string blocklabel;

        public IsAssumeFalseCommand(string name)
            : base("isassumefalse")
        {
            this.blocklabel = name;

            desc = "isassumefalse " + blocklabel;
        }

        public static string Usage()
        {
            return "isassumefalse blockName";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("isassumefalse"))
            {
                string blocklabel = parser.NextAsString();
                return new IsAssumeFalseCommand(blocklabel);
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

            if (DoRun(proofState, procState, atomicBlock.parent) == false)
            {
                Output.AddError("Could not construct assume false atomic block!");
                return false;
            }

            return false;
        }

        public bool DoRun(ProofState proofState, ProcedureState procState, AtomicStmt atomStmt)
        {

            int index;
            StmtList parentStmt = Qoogie.GetParentContext(atomStmt, procState.Body, out index);
            Debug.Assert(parentStmt.BigBlocks[index].ec == atomStmt);
            BigBlock down = parentStmt.BigBlocks[index];

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);

            Pair rwSet = atomicBlock.ComputeReadWriteSet();
            Set<Variable> read = (Set<Variable>)rwSet.First;
            Set<Variable> write = (Set<Variable>)rwSet.Second;

            //Output.AddLine(" The assigned label " + atomStmt.AssignLabel()); 

            if (!(parentStmt.BigBlocks[index + 1].ec is AtomicStmt))
            {
                Output.AddError(" atomic{ assume Expr}  can not be found ");
                return false;
            }

            else
            {

                AtomicStmt wcm = parentStmt.BigBlocks[index + 1].ec as AtomicStmt;

                if (!(wcm.body.BigBlocks[0].simpleCmds[0] is AssumeCmd))
                {

                    Output.AddError(" atomic{ assume Expr}  can not be found ");
                    return false;
                }
                else
                {


                    AssumeCmd propagate = wcm.body.BigBlocks[0].simpleCmds[0] as AssumeCmd;

                    if (CodeAnalyses.IsGlobalExpr(propagate.Expr))
                    {

                        Output.AddError(" Illegal predicate to  form atomic {assume false} with " + atomicBlock.Label + " : expression can not include global variables");
                        return false;
                    }

                    Set readPro = CodeAnalyses.ComputeReads(propagate);
                    Set writePro = CodeAnalyses.ComputeWrites(propagate);
                    Variable rd = (Variable)readPro.Take();
                    if (!(readPro.Count == 1 && write.Count == 2) && !(write.Contains(rd)) && !(rd.TypedIdent.Type == Microsoft.Boogie.Type.Bool))
                    {

                        //    Output.AddError(" Read Set size " + readPro.Count.ToString());
                        //       Output.AddError(" Write Set size " + write.Count.ToString());

                        Output.AddError(" Illegal number of elements in write set of " + atomicBlock.Label + " and read set of " + parentStmt.BigBlocks[index + 1]);
                        return false;
                    }

                    Variable writ = null;

                    foreach (Variable wrt in write)
                    {

                        if (wrt.Name == rd.Name)
                        {

                            writ = wrt;
                        }

                    }


                    atomicBlock.InstrumentExit(new CmdSeq(propagate));
                    CodeTransformations.RemoveAt(parentStmt, index + 1);

                }
            }

            procState.MarkAsTransformed();

            return true;
        }


    }



    // Added for TSO
    public class SwapLeftCommand : ProofCommand
    {
        string blocklabel;

        public SwapLeftCommand(string name)
            : base("swapleft")
        {
            this.blocklabel = name;

            desc = "swapleft " + blocklabel;
        }

        public static string Usage()
        {
            return "swapleft atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("swapleft"))
            {
                string blocklabel = parser.NextAsString();
                return new SwapLeftCommand(blocklabel);
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

            if
                (DoRun(proofState, procState, atomicBlock.parent) == false)
            {
                Output.AddError("Could not swap to left!");
                return false;
            }

            return false;
        }
        public bool DoRun(ProofState proofState, ProcedureState procState, AtomicStmt atomStmt)
        {


            int index = 0;
            Qoogie.ResolveStmt(procState.Body);
            AssertCmd isBufEmpty = procState.SetAssertCmdForIsBufEmpty(proofState);
            StmtList parentStmt = Qoogie.GetParentContext(atomStmt); // While body

            StmtList parenparentStmt = atomStmt.body.ParentContext.ParentContext;
            BigBlock parentBB = atomStmt.body.ParentContext.ParentBigBlock; // whileCMd



            // Get index of the WhileCmd of atom
            for (int i = 0; i < parenparentStmt.BigBlocks.Count; i++)
            {
                if (parenparentStmt.BigBlocks[i] == parentBB)
                {

                    index = i;
                    break;
                }

            }
            Output.AddLine("Block index of the WhilCmd : " + index.ToString());
            Output.AddLine(" parenparent bigblock count is " + parenparentStmt.BigBlocks.Count.ToString());
            if (!(index + 2 <= parenparentStmt.BigBlocks.Count))
            {
                Output.AddError("-1.Structure of the StmtList must be assert true; call drainHead");
                return false;

            }

            else
            {
                if (!(parentBB.ec is WhileCmd))
                {
                    Output.AddError("0.Structure of the StmtList must be assert true; call drainHead");
                    return false;
                }
                else
                {
                    if (parentStmt.BigBlocks.Count != 2)
                    {

                        Output.AddError("1.Structure of the StmtList must be assert true; call drainHead");
                        return false;
                    }
                    else
                    {
                        if (!(parentStmt.BigBlocks[0].ec is AtomicStmt && parentStmt.BigBlocks[1].ec is CallStmt))
                        {
                            Output.AddError("2.Structure of the StmtList must be assert true; call drainHead");
                            return false;
                        }
                        else
                        {

                            if (!(parenparentStmt.BigBlocks[index + 1].ec is CallStmt || parenparentStmt.BigBlocks[index + 1].ec is AtomicStmt))
                            {

                                Output.AddError("WhileCmd must be followed by AtomicStmt or CallStmt");
                                return false;
                            }
                            else
                            {

                                if (parenparentStmt.BigBlocks[index + 1].ec is CallStmt)
                                {
                                    CallStmt cl = parenparentStmt.BigBlocks[index + 1].ec as CallStmt;
                                    if (cl.CalleeName == "write" || cl.CalleeName == "drainHead" || cl.CalleeName == "read" ||
                                        cl.CalleeName == "read_heap" || cl.CalleeName == "write_heap" || cl.CalleeName == "write_to_ptr" ||
                                        cl.CalleeName == "read_from_heap" || cl.CalleeName == "dummy_write" || cl.CalleeName == "dummy_emptyBuf" ||
                                        cl.CalleeName == "dummy_emptyBuf_assume")
                                        if (CodeTransformations.IsAssumeAtomStmt(cl.body))
                                        {
                                            Output.AddError("CallStmt " + cl.CalleeName + " has AssumeCmd inside");
                                            return false;
                                        }
                                        else
                                        {

                                            // Do swap
                                            // parentStmt.BigBlocks.RemoveAt(0);
                                            //procState.MarkAsTransformed();

                                            BigBlock dupToInsert = Qoogie.DuplicateBigBlock(parenparentStmt.BigBlocks[index + 1]);
                                            foreach (BigBlock itr in parenparentStmt.BigBlocks)
                                            {

                                                Output.AddLine("itr blok lable : " + itr.LabelName);
                                            }
                                            Output.AddLine("The value of index : " + index.ToString());
                                            parenparentStmt.BigBlocks.Insert(index, dupToInsert);
                                            parenparentStmt.BigBlocks.RemoveAt(index + 2);
                                            procState.MarkAsTransformed();

                                            return true;
                                        }
                                }
                                else
                                {
                                    if (parenparentStmt.BigBlocks[index + 1].ec is AtomicStmt)
                                    {

                                        AtomicStmt atom = parenparentStmt.BigBlocks[index + 1].ec as AtomicStmt;

                                        if (atom.body.BigBlocks.Count > 1)
                                        {

                                            if (CodeTransformations.IsAssumeAtomStmt(atom.body))
                                            {
                                                Output.AddError("AtomicStmt " + atom.label + " has AssumeCmd inside");
                                                return false;
                                            }
                                            else
                                            {
                                                // Do swap
                                                //     parentStmt.BigBlocks.RemoveAt(0);
                                                //  procState.MarkAsTransformed();

                                                BigBlock dupToInsert = Qoogie.DuplicateBigBlock(parenparentStmt.BigBlocks[index + 1]);
                                                foreach (BigBlock itr in parenparentStmt.BigBlocks)
                                                {

                                                    Output.AddLine("itr blok lable : " + itr.LabelName);
                                                }
                                                Output.AddLine("The value of index : " + index.ToString());
                                                parenparentStmt.BigBlocks.Insert(index, dupToInsert);
                                                parenparentStmt.BigBlocks.RemoveAt(index + 2);
                                                procState.MarkAsTransformed();

                                                return true;
                                            }

                                        }
                                        else
                                        {
                                            if (atom.body.BigBlocks.Count == 1)
                                            {
                                                if (atom.body.BigBlocks[0].simpleCmds[0] is AssumeCmd)
                                                {
                                                    Output.AddError("AtomicStmt " + atom.label + " has AssumeCmd inside");
                                                    return false;
                                                }
                                                else
                                                {


                                                    // Do Swap
                                                    //       parentStmt.BigBlocks.RemoveAt(0);
                                                    //        procState.MarkAsTransformed();

                                                    BigBlock dupToInsert = Qoogie.DuplicateBigBlock(parenparentStmt.BigBlocks[index + 1]);
                                                    foreach (BigBlock itr in parenparentStmt.BigBlocks)
                                                    {

                                                        Output.AddLine("itr blok lable : " + itr.LabelName);
                                                    }
                                                    Output.AddLine("The value of index : " + index.ToString());
                                                    parenparentStmt.BigBlocks.Insert(index, dupToInsert);
                                                    parenparentStmt.BigBlocks.RemoveAt(index + 2);
                                                    procState.MarkAsTransformed();

                                                    return true;
                                                }
                                            }
                                            else
                                            {
                                                if (atom.body.BigBlocks.Count == 0)
                                                {

                                                    Output.AddError("AtomicStmt " + atom.label + " has no body");
                                                    return false;
                                                }

                                            }


                                        }
                                    }


                                }
                            }
                        }
                    }
                }
            }

            //bool has =  CodeTransformations.IsAssumeAtomStmt(parentStmt);
            procState.MarkAsTransformed();

            return true;

        }

        /* public bool DoRun(ProofState proofState, ProcedureState procState, AtomicStmt atomStmt)
         {


             int index = 0;
             Qoogie.ResolveStmt(procState.Body);
             AssertCmd isBufEmpty = procState.SetAssertCmdForIsBufEmpty(proofState);
             StmtList parentStmt = Qoogie.GetParentContext(atomStmt); // While body
            
             StmtList parenparentStmt = atomStmt.body.ParentContext.ParentContext;
             BigBlock parentBB = atomStmt.body.ParentContext.ParentBigBlock; // whileCMd

            

             // Get index of the WhileCmd of atom
             for (int i = 0; i < parenparentStmt.BigBlocks.Count; i++)
             {
                 if (parenparentStmt.BigBlocks[i] == parentBB)
                 {

                     index = i;
                     break;
                 }

             }
             Output.AddLine("Block index of the WhilCmd : " + index.ToString());
             Output.AddLine(" parenparent bigblock count is " + parenparentStmt.BigBlocks.Count.ToString());
             if (!(index + 2 <= parenparentStmt.BigBlocks.Count))
             {
                 Output.AddError("-1.Structure of the StmtList must be assert true; call drainHead");
                 return false;

             }

             else
             {
                 if (!(parentBB.ec is WhileCmd))
                 {
                     Output.AddError("0.Structure of the StmtList must be assert true; call drainHead");
                     return false;
                 }
                 else
                 {
                     if (parentStmt.BigBlocks.Count != 2)
                     {

                         Output.AddError("1.Structure of the StmtList must be assert true; call drainHead");
                         return false;
                     }
                     else
                     {
                         if (!(parentStmt.BigBlocks[0].ec is AtomicStmt && parentStmt.BigBlocks[1].ec is CallStmt))
                         {
                             Output.AddError("2.Structure of the StmtList must be assert true; call drainHead");
                             return false;
                         }
                         else
                         {

                             if (!(parenparentStmt.BigBlocks[index + 1].ec is CallStmt || parenparentStmt.BigBlocks[index + 1].ec is AtomicStmt))
                             {

                                 Output.AddError("WhileCmd must be followed by AtomicStmt or CallStmt");
                                 return false;
                             }
                             else
                             {

                                 if (parenparentStmt.BigBlocks[index + 1].ec is CallStmt)
                                 {
                                     CallStmt cl = parenparentStmt.BigBlocks[index + 1].ec as CallStmt;
                                    
                                     bool has = CodeTransformations.IsAssumeAtomStmt(cl.body);
                                     if (has)
                                     {

                                         Output.AddError("CallStmt includes AssumeCmd");
                                         return false;

                                     }
                                     else { 
                                     // do swap                                        
                                           parentStmt.BigBlocks.RemoveAt(0);
                                           procState.MarkAsTransformed();
                                           BigBlock dupToInsert = Qoogie.DuplicateBigBlock(parenparentStmt.BigBlocks[index + 1]);  
                                           parenparentStmt.BigBlocks.Insert(0, dupToInsert);
                                           parenparentStmt.BigBlocks.RemoveAt(index + 2);
                                           foreach (BigBlock itr in parenparentStmt.BigBlocks) {

                                               Output.AddLine("itr blok lable : " + itr.LabelName);
                                           }
                                           Output.AddLine("The value of index : " + index.ToString());
                                           return true;
                                     }
                                 }
                                 else
                                 {
                                     if (parenparentStmt.BigBlocks[index + 1].ec is AtomicStmt)
                                     {

                                         AtomicStmt atm = parenparentStmt.BigBlocks[index + 1].ec as AtomicStmt;
                                         Output.AddLine("Atomic Statement'in body'si " + atm.body.BigBlocks[0].LabelName);
                                         bool has = CodeTransformations.IsAssumeAtomStmt(atm.body);
                                         if (has)
                                         {

                                             Output.AddError("CallStmt includes AssumeCmd");
                                             return false;

                                         }
                                         else { 
                                         //do swap
                                             parentStmt.BigBlocks.RemoveAt(0);
                                             procState.MarkAsTransformed();
                                             BigBlock dupToInsert = Qoogie.DuplicateBigBlock(parenparentStmt.BigBlocks[index + 1]);
                                             parenparentStmt.BigBlocks.Insert(index, dupToInsert);
                                             parenparentStmt.BigBlocks.RemoveAt(index + 2);
                                             foreach (BigBlock itr in parenparentStmt.BigBlocks)
                                             {

                                                 Output.AddLine("itr blok lable : " + itr.LabelName);
                                             }
                                             Output.AddLine("The value of index : " + index.ToString());
                                             return true;
                                         }

                                     }

                                 }

                             }
                         }
                     }
                 }
             }
             return true;
         }*/
    }

    // Added for TSO
    public class SwapCommand : ProofCommand
    {
        string blocklabel;

        public SwapCommand(string name)
            : base("swap")
        {
            this.blocklabel = name;

            desc = "swap " + blocklabel;
        }

        public static string Usage()
        {
            return "swap atomicBlockLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("swap"))
            {
                string blocklabel = parser.NextAsString();
                return new SwapCommand(blocklabel);
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

            if (DoRun(proofState, procState, atomicBlock.parent) == false)
            {
                Output.AddError("Could not swap!");
                return false;
            }

            return false;
        }

        public bool DoRun(ProofState proofState, ProcedureState procState, AtomicStmt atomStmt)
        {

            int index;
            StmtList parentStmt = Qoogie.GetParentContext(atomStmt, procState.Body, out index);
            Debug.Assert(parentStmt.BigBlocks[index].ec == atomStmt);
            BigBlock down = parentStmt.BigBlocks[index];

            if (!(parentStmt.BigBlocks[index + 1].ec is WhileCmd))
            {
                Output.AddError(" while(*) {call drainHead() } can not be found ");
                return false;
            }

            else
            {

                WhileCmd wcm = parentStmt.BigBlocks[index + 1].ec as WhileCmd;
                if (wcm.Body.BigBlocks[0].ec is CallStmt)
                {
                    CallStmt callStmt = wcm.Body.BigBlocks[0].ec as CallStmt;
                    if (callStmt.cmd.Proc.Name != "drainHead")
                    {

                        Output.AddError(" while(*) {call drainHead() } can not be found ");
                        return false;

                    }

                }
            }



            parentStmt.BigBlocks.Insert(index + 2, down);
            parentStmt.BigBlocks.RemoveAt(index);



            Debug.Assert(index <= parentStmt.BigBlocks.Count);

            procState.MarkAsTransformed();

            return true;
        }


    }

    //Delete TSO Arbitrary

    public class DeleteDummySkipArbitraryCommand : ProofCommand
    {
        string atomicLabel;
        public DeleteDummySkipArbitraryCommand(string atomicLbl)
            : base("rmskpdat")
        {
            atomicLabel = atomicLbl;
            desc = "rmskpdat " + atomicLabel;
        }

        public static string Usage()
        {
            return "rmskpdat atomicLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("rmskpdat"))
            {
                string blocklabel = parser.NextAsString();
                return new DeleteDummySkipArbitraryCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {
            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomicLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomicLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;

            //------------------------------------------------------
            // check if the atomic block is the body of a loop
            AtomicStmt atom = atomicBlock.parent;
            BigBlock bb = atom.body.ParentContext.ParentBigBlock;
            if (bb.ec == null || !(bb.ec is WhileCmd))
            {
                Output.AddError("Given atomic block is not in the body of a while loop!");
                return false;
            }

            DoRun(proofState, atomicBlock.procState, atom);

            procState.MarkAsTransformed();

            return false;
        }

        public bool DoRun(ProofState proofState, ProcedureState procState, AtomicStmt atom)
        {
            // BigBlock bb = atom.body.ParentContext.ParentBigBlock;
            StmtList parentStmt = Qoogie.GetParentContext(atom);
            // AtomicStmt skipAtom = Qoogie.MakeAtomicStmt(new CmdSeq(new AssertCmd(Token.NoToken, Expr.True)), null, null);
            //BigBlock skipBB = new BigBlock(Token.NoToken, skipAtom.label, new CmdSeq(), skipAtom, null);

            CodeTransformations.RemoveAt(parentStmt, 0);
            // Output.AddLine("Ilk block " + parentStmt.BigBlocks[0].LabelName); 
            return true;



        }
    }

    //

    // TSO Insert Arbitrary
    //TSO
    public class InsertDummySkipArbitraryCommand : ProofCommand
    {
        string atomicLabel;
        public InsertDummySkipArbitraryCommand(string atomicLbl)
            : base("skpdat")
        {
            atomicLabel = atomicLbl;
            desc = "skpdat " + atomicLabel;
        }

        public static string Usage()
        {
            return "skpdat atomicLabel";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("skpdat"))
            {
                string blocklabel = parser.NextAsString();
                return new InsertDummySkipArbitraryCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {
            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomicLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomicLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;

            //------------------------------------------------------
            // check if the atomic block is the body of a loop
            AtomicStmt atom = atomicBlock.parent;
            BigBlock bb = atom.body.ParentContext.ParentBigBlock;
            if (bb.ec == null || !(bb.ec is WhileCmd))
            {
                Output.AddError("Given atomic block is not in the body of a while loop!");
                return false;
            }

            DoRun(proofState, atomicBlock.procState, atom);

            procState.MarkAsTransformed();

            return false;
        }

        public bool DoRun(ProofState proofState, ProcedureState procState, AtomicStmt atom)
        {
            // BigBlock bb = atom.body.ParentContext.ParentBigBlock;
            StmtList parentStmt = Qoogie.GetParentContext(atom);
            AtomicStmt skipAtom = Qoogie.MakeAtomicStmt(new CmdSeq(new AssertCmd(Token.NoToken, Expr.True)), null, null);
            BigBlock skipBB = new BigBlock(Token.NoToken, skipAtom.label, new CmdSeq(), skipAtom, null);

            CodeTransformations.InsertAt(parentStmt, skipBB, 0);
            // Output.AddLine("Ilk block " + parentStmt.BigBlocks[0].LabelName); 
            return true;



        }
    }
    /*
     proc{
     *       stmts-pre
     *       body'
     *      while(*){
     *      
     *          BODY
     * 
     *       }
     *      body''
     *       stmts-post
     * }
     * 
     * proc{
     * 
     *   stmts-pre
     *   stmt-post
     * }
     
     * proc{
     *  
     * 
     * }
     
     */

    //
    //TSO
    public class PeelAwayCommand : ProofCommand
    {

        string blocklabel;

        public PeelAwayCommand(string name)
            : base("peelaway")
        {
            blocklabel = name;
            desc = "peelaway " + blocklabel;
        }

        public static string Usage()
        {
            return "peelaway blockName";

        }
        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("peelaway"))
            {
                string blocklabel = parser.NextAsString();
                return new PeelAwayCommand(blocklabel);
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
            if (bb.ec == null || !(bb.ec is WhileCmd))
            {
                Output.AddError("Given atomic block is not in the body of a while loop!");
                return false;
            }

            DoRun(proofState, atomicBlock.procState, bb);

            procState.MarkAsTransformed();

            return false;
        }
       

        static public void DoRun(ProofState proofState, ProcedureState procState, BigBlock bb)
        {
           
        }

    }
    //TSO
    public class PrePeelOutCommand : ProofCommand
    {
        string blocklabel;

        public PrePeelOutCommand(string name)
            : base("prepeelout")
        {
            this.blocklabel = name;
            desc = "prepeelout " + blocklabel;
        }

        public static string Usage()
        {
            return "prepeelout blockName";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("prepeelout"))
            {
                string blocklabel = parser.NextAsString();
                return new PrePeelOutCommand(blocklabel);
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
            if (bb.ec == null || !(bb.ec is WhileCmd))
            {
                Output.AddError("Given atomic block is not in the body of a while loop!");
                return false;
            }

            DoRun(proofState, atomicBlock.procState, bb);

            procState.MarkAsTransformed();

            return false;
        }

        static public void DoRun(ProofState proofState, ProcedureState procState, BigBlock bb)
        {
            WhileCmd whileCmd = bb.ec as WhileCmd;
            Debug.Assert(whileCmd != null);

            int index;
            StmtList parentStmt = Qoogie.GetParentContext(bb, procState.Body, out index);
            StmtList body = whileCmd.Body;

            //---------------------------
            StmtList S1 = body;
            StmtList S2 = Qoogie.DuplicateStatement(body);

            //---------------------------
            // S1
            /* CodeTransformations.ReplaceBreakWithThrow(S1);
             bool hasContinue = CodeTransformations.ReplaceContinueWithThrow(S1);
             CodeTransformations.ReplaceReturnWithThrow(S1);
             if (hasContinue)
             {
                 S1 = Qoogie.SkipEx(S1, null, proofState.exContinueExpr);
             }
             S1 = Qoogie.SuppressEx(S1, null); // , proofState.exBreakExpr, proofState.exReturnExpr);
             */
            if (whileCmd.Guard != null)
            {
                // make while(e) while(*)
                if (MergeCommand.IsAtomic(S1))
                {
                    AtomicStmt atom = S1.BigBlocks[0].ec as AtomicStmt;
                    CodeTransformations.InstrumentEntry(atom.body, new CmdSeq(new AssumeCmd(Token.NoToken, whileCmd.Guard)), true);
                }
                else
                {
                    CodeTransformations.InstrumentEntry(S1, new CmdSeq(new AssumeCmd(Token.NoToken, whileCmd.Guard)), false);
                }
            }

            //!   whilxeCmd.Body = S1;

            //---------------------------
            // S2
            //! S2 = Qoogie.Suppress(S2);
            /*hasContinue = CodeTransformations.ReplaceContinueWithThrow(S2);
            if (hasContinue)
            {
                S2 = Qoogie.SuppressEx(S2, null, proofState.exContinueExpr);
            }
            bool hasBreak = CodeTransformations.ReplaceBreakWithThrow(S2);
            if (hasBreak)
            {
                S2 = Qoogie.SkipEx(S2, null, proofState.exBreakExpr);
            }*/

            Expr guard = whileCmd.Guard == null ? null : Qoogie.DuplicateExpr(whileCmd.Guard);
            IfCmd ifCmd = new IfCmd(Token.NoToken, guard, S2, null, null);
            BigBlock ifbb = new BigBlock(Token.NoToken, null, new CmdSeq(), ifCmd, null);
            parentStmt.BigBlocks.Insert(index, ifbb);
            //---------------------------
            whileCmd.Guard = null;

            procState.MarkAsTransformed();
        }


    }




    // end class Swap
    public class PeelOutCommand : ProofCommand
    {
        string blocklabel;

        public PeelOutCommand(string name)
            : base("peelout")
        {
            this.blocklabel = name;
            desc = "peelout " + blocklabel;
        }

        public static string Usage()
        {
            return "peelout atomicBlockLabel@procedureName";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("peelout"))
            {
                string blocklabel = parser.NextAsString();
                return new PeelOutCommand(blocklabel);
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
            if (bb.ec == null || !(bb.ec is WhileCmd))
            {
                Output.AddError("Given atomic block is not in the body of a while loop!");
                return false;
            }

            DoRun(proofState, atomicBlock.procState, bb);

            procState.MarkAsTransformed();

            return false;
        }

        static public void DoRun(ProofState proofState, ProcedureState procState, BigBlock bb)
        {
            WhileCmd whileCmd = bb.ec as WhileCmd;
            Debug.Assert(whileCmd != null);

            int index;
            StmtList parentStmt = Qoogie.GetParentContext(bb, procState.Body, out index);
            StmtList body = whileCmd.Body;

            //---------------------------
            StmtList S1 = body;
            StmtList S2 = Qoogie.DuplicateStatement(body);

            //---------------------------
            // S1
            CodeTransformations.ReplaceBreakWithThrow(S1);
            bool hasContinue = CodeTransformations.ReplaceContinueWithThrow(S1);
            CodeTransformations.ReplaceReturnWithThrow(S1);
            if (hasContinue)
            {
                S1 = Qoogie.SkipEx(S1, null, proofState.exContinueExpr);
            }
            S1 = Qoogie.SuppressEx(S1, null); // , proofState.exBreakExpr, proofState.exReturnExpr);

            if (whileCmd.Guard != null)
            {
                // make while(e) while(*)
                if (MergeCommand.IsAtomic(S1))
                {
                    AtomicStmt atom = S1.BigBlocks[0].ec as AtomicStmt;
                    CodeTransformations.InstrumentEntry(atom.body, new CmdSeq(new AssumeCmd(Token.NoToken, whileCmd.Guard)), true);
                }
                else
                {
                    CodeTransformations.InstrumentEntry(S1, new CmdSeq(new AssumeCmd(Token.NoToken, whileCmd.Guard)), false);
                }
            }

            whileCmd.Body = S1;

            //---------------------------
            // S2
            S2 = Qoogie.Suppress(S2);
            hasContinue = CodeTransformations.ReplaceContinueWithThrow(S2);
            if (hasContinue)
            {
                S2 = Qoogie.SuppressEx(S2, null, proofState.exContinueExpr);
            }
            bool hasBreak = CodeTransformations.ReplaceBreakWithThrow(S2);
            if (hasBreak)
            {
                S2 = Qoogie.SkipEx(S2, null, proofState.exBreakExpr);
            }

            Expr guard = whileCmd.Guard == null ? null : Qoogie.DuplicateExpr(whileCmd.Guard);
            IfCmd ifCmd = new IfCmd(Token.NoToken, guard, S2, null, null);
            BigBlock ifbb = new BigBlock(Token.NoToken, null, new CmdSeq(), ifCmd, null);
            parentStmt.BigBlocks.Insert(index + 1, ifbb);

            //---------------------------
            whileCmd.Guard = null;

            procState.MarkAsTransformed();
        }
    } // end class PeelOutCommand



    public class PeelOut2Command : ProofCommand
    {
        string blocklabel;

        public PeelOut2Command(string name)
            : base("peelout2")
        {
            this.blocklabel = name;
            desc = "peelout2 " + blocklabel;
        }

        public static string Usage()
        {
            return "peelout2 atomicBlockLabel@procedureName";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("peelout2"))
            {
                string blocklabel = parser.NextAsString();
                return new PeelOut2Command(blocklabel);
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
            if (bb.ec == null || !(bb.ec is WhileCmd))
            {
                Output.AddError("Given atomic block is not in the body of a while loop!");
                return false;
            }

            DoRun(proofState, atomicBlock.procState, bb);

            procState.MarkAsTransformed();

            return false;
        }

        static public void DoRun(ProofState proofState, ProcedureState procState, BigBlock bb)
        {
            WhileCmd whileCmd = bb.ec as WhileCmd;
            Debug.Assert(whileCmd != null);

            int index;
            StmtList parentStmt = Qoogie.GetParentContext(bb, procState.Body, out index);
            StmtList body = whileCmd.Body;

            //---------------------------
            StmtList S1 = body;
            StmtList S2 = Qoogie.DuplicateStatement(body);

            //---------------------------
            // S1
            CodeTransformations.ReplaceBreakWithThrow(S1);
            bool hasContinue = CodeTransformations.ReplaceContinueWithThrow(S1);
            CodeTransformations.ReplaceReturnWithThrow(S1);
            if (hasContinue)
            {
                S1 = Qoogie.SkipEx(S1, null, proofState.exContinueExpr);
            }
            S1 = Qoogie.SuppressEx2(S1, null); // , proofState.exBreakExpr, proofState.exReturnExpr);

            if (whileCmd.Guard != null)
            {
                // make while(e) while(*)
                if (MergeCommand.IsAtomic(S1))
                {
                    AtomicStmt atom = S1.BigBlocks[0].ec as AtomicStmt;
                    CodeTransformations.InstrumentEntry(atom.body, new CmdSeq(new AssumeCmd(Token.NoToken, whileCmd.Guard)), true);
                }
                else
                {
                    CodeTransformations.InstrumentEntry(S1, new CmdSeq(new AssumeCmd(Token.NoToken, whileCmd.Guard)), false);
                }
            }

            whileCmd.Body = S1;

            //---------------------------
            // S2
            S2 = Qoogie.Suppress(S2);
            hasContinue = CodeTransformations.ReplaceContinueWithThrow(S2);
            if (hasContinue)
            {
                S2 = Qoogie.SuppressEx2(S2, null, proofState.exContinueExpr);
            }
            bool hasBreak = CodeTransformations.ReplaceBreakWithThrow(S2);
            if (hasBreak)
            {
                S2 = Qoogie.SkipEx(S2, null, proofState.exBreakExpr);
            }

            Expr guard = whileCmd.Guard == null ? null : Qoogie.DuplicateExpr(whileCmd.Guard);
            IfCmd ifCmd = new IfCmd(Token.NoToken, guard, S2, null, null);
            BigBlock ifbb = new BigBlock(Token.NoToken, null, new CmdSeq(), ifCmd, null);
            parentStmt.BigBlocks.Insert(index + 1, ifbb);

            //---------------------------
            whileCmd.Guard = null;

            procState.MarkAsTransformed();
        }
    } // end class PeelOut2Command

    //tso
    public class SkipAfterCommand : ProofCommand
    {
        string blocklabel;
        int offset;

        public SkipAfterCommand(string name, int off)
            : base("skipafter")
        {
            this.blocklabel = name;
            this.offset = off;
            desc = "skipafter " + blocklabel + " " + offset;
        }

        public static string Usage()
        {
            return "skipafter atomicBlockLabel number";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("skipafter"))
            {
                int offset = 0;
                string blocklabel = parser.NextAsString();
                if (parser.HasNext())
                {
                    offset = parser.NextAsInt(0);
                }
                return new SkipAfterCommand(blocklabel, offset);
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
            if (DoRun(proofState, procState, atomicBlock.parent) == null)
            {
                Output.AddError("Could not insert skip!");
                return false;
            }

            Output.AddLine("Inserted skip!");

            return false;
        }

        public AtomicStmt DoRun(ProofState proofState, ProcedureState procState, AtomicStmt atomStmt)
        {
            AtomicStmt skipAtom = Qoogie.MakeAtomicStmt(new CmdSeq(new AssumeCmd(Token.NoToken, Expr.True)), null, null);
            BigBlock skipBB = new BigBlock(Token.NoToken, skipAtom.label, new CmdSeq(), skipAtom, null);

            int index;
            StmtList parentStmt = Qoogie.GetParentContext(atomStmt, procState.Body, out index);
            Debug.Assert(parentStmt.BigBlocks[index].ec == atomStmt);
            index = index + offset + 1;

            //for (; index < parentStmt.BigBlocks.Count && !(parentStmt.BigBlocks[index].ec is AtomicStmt); ++index) ;
            Debug.Assert(index <= parentStmt.BigBlocks.Count);
            parentStmt.BigBlocks.Insert(index, skipBB);

            procState.MarkAsTransformed();

            return skipAtom;
        }

    } // end class SkipCommand

#if false
public class CloneCommand : ProofCommand
{
	string blockLabel;
	
	string branchLabel;
	
	public CloneCommand(string block, string branch)
		: base("clone")
	{
		blockLabel = block;
		branchLabel = branch;
		desc = "clone " + blockLabel + " " + branchLabel;
	}
	
	override public bool Run(ProofState proofState) {

        if (!proofState.AtomicBlockExists(blockLabel))
        {
            Output.AddError("Block " + blockLabel + " does not exist!");
            return false;
        }


		AtomicBlock atomicBlock = proofState.GetAtomicBlock(blockLabel);
		
		if(!atomicBlock.IsClonable) {
			return false;
		}
		
		if(branchLabel == "*") {
		
			CloneAtomicBlock(atomicBlock, proofState);
		
		} else {
		
			AtomicBlock otherBlock = proofState.GetAtomicBlock(branchLabel);

            if (!proofState.AtomicBlockExists(branchLabel))
            {
                Output.AddError("Block " + branchLabel + " does not exist!");
                return false;
            }
			
			if(atomicBlock.Successors.Contains(otherBlock)) {
				CloneAfter(proofState, atomicBlock, otherBlock);
			} else {
                if (!otherBlock.Successors.Contains(atomicBlock))
                {
                    Output.AddError("Blocks " + blockLabel + " and " + branchLabel + " are not connected!");
                    return false;
                }
				CloneBefore(proofState, atomicBlock, otherBlock);
			}
		}
		
		return false;
	}
	
	private void CloneAfter(ProofState proofState, AtomicBlock atomicBlock, AtomicBlock successor) {
		Debug.Assert(atomicBlock.Successors.Count > 1);
		
		AtomicBlock cloneBlock = atomicBlock.Clone(new Dictionary<Block, Block>());
		
		//--------------------------------------------
		
		Set<Block> exitBlocks = cloneBlock.ExitBlocks;
		
		Debug.Assert(exitBlocks.Count == 1); // we cannot handle more complicated cases
		
		Block exitBlock = exitBlocks.PickOne();
		
		exitBlock.TransferCmd = new GotoCmd(Token.NoToken, new BlockSeq(successor.startBlock));
		
		//--------------------------------------------
		
		foreach(Block predBlock in atomicBlock.startBlock.Predecessors) {
			GotoCmd predGotoCmd = (predBlock.TransferCmd as GotoCmd);
			predGotoCmd.AddTarget(cloneBlock.startBlock);		
		}
		
		//--------------------------------------------
		
		exitBlocks = atomicBlock.ExitBlocks;
		
		Debug.Assert(exitBlocks.Count == 1); // we cannot handle more complicated cases
		
		exitBlock = exitBlocks.PickOne();
		
		GotoCmd exitGotoCmd = exitBlock.TransferCmd as GotoCmd;
		if(exitGotoCmd != null) {
			BlockSeq newTargets = new BlockSeq();
			foreach(Block target in exitGotoCmd.labelTargets) {
				if(target != successor.startBlock) {
					newTargets.Add(target);
				}
			}
			exitBlock.TransferCmd = new GotoCmd(Token.NoToken, newTargets);			
		}				
		
		//--------------------------------------------
		
		// finally modify the procedure state
		ProcedureState procState = atomicBlock.procState;
		
		procState.AddAtomicBlock(cloneBlock);

        procState.CFGUpdated();
	}
	
	private void CloneBefore(ProofState proofState, AtomicBlock atomicBlock, AtomicBlock predecessor) {
		Debug.Assert(atomicBlock.startBlock.Predecessors.Length > 1);
		
		AtomicBlock cloneBlock = atomicBlock.Clone();
		
		//--------------------------------------------
		
		Set<Block> exitBlocks = predecessor.ExitBlocks;
		
		Debug.Assert(exitBlocks.Count == 1); // we cannot handle more complicated cases
		
		Block exitBlock = exitBlocks.PickOne();
		
		GotoCmd exitGotoCmd = exitBlock.TransferCmd as GotoCmd;
		BlockSeq newTargets = new BlockSeq();
		foreach(Block target in exitGotoCmd.labelTargets) {
			if(target != atomicBlock.startBlock) {
				newTargets.Add(target);
			}
		}
		newTargets.Add(cloneBlock.startBlock);
		exitBlock.TransferCmd = new GotoCmd(Token.NoToken, newTargets);			
		
		//--------------------------------------------
		
		// finally modify the procedure state
		ProcedureState procState = atomicBlock.procState;
		
		procState.AddAtomicBlock(cloneBlock);
		
		procState.CFGUpdated();
	}
	
	private void CloneAtomicBlock(AtomicBlock atomicBlock, ProofState proofState) {
		Debug.Assert(atomicBlock.Successors.Count > 1 || atomicBlock.startBlock.Predecessors.Length > 1);
		
		Block startBlock = atomicBlock.startBlock;
		
		Set<AtomicBlock> newAtomicBlocks = new Set<AtomicBlock>();
		
		// create the block in the middle
		Block middle = new Block(Token.NoToken, startBlock.Label, new CmdSeq(), new GotoCmd(Token.NoToken, new BlockSeq()));
				
		// clone for predecessors		
		if(startBlock.Predecessors.Length > 0) {
			if(startBlock.Predecessors.Length == 1) {
				Block predBlock = startBlock.Predecessors[0];
				GotoCmd gotoCmd = (predBlock.TransferCmd as GotoCmd);	
				BlockSeq newTargets = new BlockSeq();
				foreach(Block target in gotoCmd.labelTargets) {
					if(target != startBlock) {
						newTargets.Add(target);
					}
				}
				newTargets.Add(middle);
				predBlock.TransferCmd = new GotoCmd(Token.NoToken, newTargets);		
			
			} else {
			
				foreach(Block predBlock in startBlock.Predecessors) {
					
					AtomicBlock cloneBlock = atomicBlock.Clone();
					
					GotoCmd gotoCmd = (predBlock.TransferCmd as GotoCmd);	
					BlockSeq newTargets = new BlockSeq();
					foreach(Block target in gotoCmd.labelTargets) {
						if(target != startBlock) {
							newTargets.Add(target);
						}
					}
					newTargets.Add(cloneBlock.startBlock);
					predBlock.TransferCmd = new GotoCmd(Token.NoToken, newTargets);	
					
					newAtomicBlocks.Add(cloneBlock);				
				}
			
			}
		}
		
		// clone for successors
		if(atomicBlock.Successors.Count > 0) {	
			if(atomicBlock.Successors.Count == 1) {
				
				(middle.TransferCmd as GotoCmd).AddTarget(atomicBlock.Successors.PickOne().startBlock);
			
			} else {
			
				foreach(AtomicBlock successor in atomicBlock.Successors) {
					
					AtomicBlock cloneBlock = atomicBlock.Clone();
					
					Set<Block> exitBlocks = cloneBlock.ExitBlocks;
					Debug.Assert(exitBlocks.Count == 1); // we cannot handle more complicated cases
					
					Block exitBlock = exitBlocks.PickOne();
					
					exitBlock.TransferCmd = new GotoCmd(Token.NoToken, new BlockSeq(successor.startBlock));
					
					(middle.TransferCmd as GotoCmd).AddTarget(cloneBlock.startBlock);
					
					newAtomicBlocks.Add(cloneBlock);
				}	
			}
		}
		
		// create the middle atomic block
		AtomicBlock middleAtomic = new AtomicBlock(atomicBlock.procState, middle);
		newAtomicBlocks.Add(middleAtomic);
		
		// finally modify the procedure state
		ProcedureState procState = atomicBlock.procState;
		
		procState.RemoveAtomicBlock(atomicBlock);
		
		foreach(AtomicBlock newAtomicBlock in newAtomicBlocks) {
			procState.AddAtomicBlock(newAtomicBlock);
		}
		
		procState.CFGUpdated();
	}
	
} // end class CloneCommand
#endif

} // end namespace QED
