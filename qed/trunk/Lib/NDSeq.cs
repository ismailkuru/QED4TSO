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
    using Microsoft.Boogie;
    using BoogiePL;
    using System.Diagnostics;
    using PureCollections;

    
    public class CheckSafeCommand : ProofCommand
    {
        public enum Kind { Procedure, Block }

        string procname;
        Kind kind;

        // for now we only consider Kind.Procedure
        public CheckSafeCommand(string name)
            : base("checksafe")
        {
            this.procname = name;
            this.kind = Kind.Procedure;
            desc = "checksafe " + procname;
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("checksafe"))
            {
                string procname = parser.NextAsString();
                return new CheckSafeCommand(procname);
            }
            return null;
        }

        public static string Usage()
        {
            return "checksafe procedureName";
        }

        override public bool Run(ProofState proofState)
        {

            ProcedureState procState = proofState.GetProcedureState(procname);
            if (procState == null)
            {
                Output.AddError("Procedure does not exist: " + procname);
                return false;
            }
            DoRun(proofState, procState, this.kind);
        
            return false;
        }

        // compute mover types of statements, for now just show them
        static public void DoRun(ProofState proofState, ProcedureState procState, Kind kind)
        {
            foreach (ProcedureState pstate in proofState.ProcedureStates)
            {
                pstate.ComputeAtomicBlocks();
            }

            // PHASE 1: Compute mover types of atomic blocks
            // map: (AtomicStmt x string) -> Set(AtomicStmt x string)
            IDictionary<Pair, Set<Pair>> map = CodeAnalyses.ComputeParallelAtomicStmt(procState.Body);

            // reset the cache
            MCache.Enabled = true;
            MCache.Reset();

            proofState.LastMoverChecks = new List<MoverCheck>();
            // map to blocks
            foreach (Pair pair in map.Keys)
            {
                AtomicStmt atom = pair.First as AtomicStmt;
                string procName = pair.Second as string;
                AtomicBlock atomicBlock = (procName == null) ? procState.GetAtomicBlock(atom.label)
                                                             : proofState.GetProcedureState(procName).GetAtomicBlock(atom.label);
                List<AtomicBlock> allBlocks = new List<AtomicBlock>();
                foreach (Pair pair2 in map[pair])
                {
                    AtomicStmt atom2 = pair2.First as AtomicStmt;
                    string procName2 = pair2.Second as string;
                    AtomicBlock atomicBlock2 = (procName2 == null) ? procState.GetAtomicBlock(atom2.label)
                                                                   : proofState.GetProcedureState(procName2).GetAtomicBlock(atom2.label);
                    Debug.Assert(atomicBlock2 != null);
                    allBlocks.Add(atomicBlock2);
                }

                MoverTypeChecker checker = new MoverTypeChecker(proofState, atomicBlock, allBlocks);

                checker.Run(); // sets the mover type of the block as well

                proofState.LastMoverChecks.AddRange(checker.mcs);
                // do not need thos for now
                //Output.AddLine(MoverCheck.Report(checker.mcs));
            }

            // PHASE 2: Compute the mover type of every compound statement

            new MoverVisitor().Compute(procState);

            // PHASE 3: Check safety of parallelization
            SafeParallelizationChecker safetychecker = new SafeParallelizationChecker(procState);
            Set unsafeStmts = safetychecker.Check();

            if (unsafeStmts.Count == 0)
            {
                Output.AddLine("Safely parallelizable!");
            }
            else
            {
                Output.AddLine("NOT safely parallelizable!");
                Output.AddLine("Unsafe statements:");
                foreach (object obj in unsafeStmts)
                {
                    if (obj is ParallelStmt)
                    {
                        ParallelStmt parStmt = obj as ParallelStmt;
                        Output.AddLine("Parallel statement at (" + parStmt.tok.line + "," + parStmt.tok.col + ")");
                    }
                    else if (obj is ForeachStmt)
                    {
                        ForeachStmt feStmt = obj as ForeachStmt;
                        Output.AddLine("Foreach statement at (" + feStmt.tok.line + "," + feStmt.tok.col + ")");
                    }
                    else
                    {
                        // TODO: write meaning information
                        Output.AddLine("Other statement: " + obj.ToString());
                    }
                }
            }

            procState.MarkAsTransformed();
        }

        private static void ComputeMoversForAtoms()
        {
            throw new NotImplementedException();
        }

    } // end class CheckSafeCommand

    public class SafeParallelizationChecker : StmtVisitor
    {
        internal ProcedureState procState;
        internal Set unsafeStmts;

        public SafeParallelizationChecker(ProcedureState proc)
        {
            this.procState = proc;
            this.unsafeStmts = new Set();
        }

        public Set Check()
        {
            // visit the statements
            VisitStmtList(procState.Body);
            return this.unsafeStmts;
        }

        public override ForeachStmt VisitForeachStmt(ForeachStmt foreachStmt)
        {
            if (QKeyValue.FindBoolAttribute(foreachStmt.attributes, "parallel"))
            {
                if (foreachStmt.Mover == null)
                {
                    unsafeStmts.Add(foreachStmt);
                }
            }
            
            return base.VisitForeachStmt(foreachStmt);
        }

        public override ParallelStmt VisitParallelStmt(ParallelStmt parStmt)
        {
            if (parStmt.Mover == null)
            {
                unsafeStmts.Add(parStmt);
            }

            return base.VisitParallelStmt(parStmt);
        }

        public override CobeginStmt VisitCobeginStmt(CobeginStmt cobgn)
        {
            if (QKeyValue.FindBoolAttribute(cobgn.attributes, "parallel"))
            {
                if (cobgn.Mover == null)
                {
                    unsafeStmts.Add(cobgn);
                }
            }
            
            return base.VisitCobeginStmt(cobgn);
        }



    }
    

} // end namespace QED
