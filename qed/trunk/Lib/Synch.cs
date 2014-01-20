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
    using Type = Microsoft.Boogie.Type;


    public class LockingCommand : ProofCommand
    {
        string varname;
        string lockname;
        Kind kind;
        public enum Kind { Mutex, RWLock };

        public LockingCommand(Kind kind, string varname, string lockname)
            : base("locking")
        {
            this.kind = kind;
            this.varname = varname;
            this.lockname = lockname;

            desc = "locking " + (kind == Kind.Mutex ? "mutex " : "rwlock ") + varname + " " + lockname;
        }

        public static string Usage()
        {
            return "locking mutex|rwlock [recordName.]variableName [recordName.]variableName";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("locking"))
            {
                string kind = parser.NextAsString();
                if (kind.Equals("mutex"))
                {
                    if (parser.HasNext())
                    {
                        string varname = parser.NextAsString();
                        if (parser.HasNext())
                        {
                            string lockname = parser.NextAsString();
                            return new LockingCommand(Kind.Mutex, varname, lockname);
                        }
                    }
                }
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {
            // find the variable
            Variable var = Qoogie.GetVariableByName(proofState, this.varname, null);
            if (var == null)
            {
                Output.AddError("Locking command failed!");
                return false;
            }

            // find the lock
            Variable lock_ = Qoogie.GetVariableByName(proofState, this.lockname, null);
            if (lock_ == null)
            {
                Output.AddError("Locking command failed!");
                return false;
            }

            if (lock_.TypedIdent.Type != proofState.mutexType)
            {
                Output.AddError("The given variable is not a lock: " + this.lockname);
            }

            // instrument the statements
            DoInstrument(proofState, var, lock_);

            Output.AddLine("Locking discipline was instrumented successfully!");
            return false;
        }

        private void DoInstrument(ProofState proofState, Variable var, Variable lock_)
        {
            foreach (ProcedureState procState in proofState.ProcedureStates)
            {
                procState.ComputeAtomicBlocks();
                // do annotate
                foreach (AtomicBlock atomicBlock in procState.AtomicBlocks)
                {
                    Set<BigBlock> bbs = new BigBlocksCollector().Collect(atomicBlock.parent.body);
                    foreach (BigBlock bb in bbs)
                    {
                        Set accessedVars = new Set();
                        foreach (Cmd cmd in bb.simpleCmds)
                        {
                            accessedVars.AddRange(CodeAnalyses.ComputeGlobalAccesses(cmd));
                        }
                        if (accessedVars.Contains(var))
                        {
                            //InstrumentEntry(bb, cmds);
                        }
                    }
                }
            }
        }
    }


}