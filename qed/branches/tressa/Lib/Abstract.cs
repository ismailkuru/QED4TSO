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


    public class SimulateCommand : ProofCommand
    {
        public string blocklabel;
        public string codeText;

        public SimulateCommand(string l, string c)
            : base("simulate")
        {
            this.blocklabel = l;
            this.codeText = c;

            StringBuilder stb = new StringBuilder();
            stb.Append("simulate ").Append(blocklabel).Append(" ").Append(codeText);
            desc = stb.ToString();
        }

        public static string Usage()
        {
            return "simulate atomicBlockLabel@procedureName codeText";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("simulate"))
            {
                string blockname = parser.NextAsString();
                string code = parser.RestAsString();
                return new SimulateCommand(blockname, code);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {
            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);

            if (atomicBlock == null)
            {
                Output.AddError("No such atomic block: " + blocklabel);
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

            if (!DoRun(proofState, atomicBlock, codeStmt, localVars))
            {
                Output.AddError("Could not simulate the atomic block " + blocklabel);
            }
            else
            {
                Output.AddLine("Replaced the statement with the abstract statement!");
            }

            return false;
        }

        static public bool DoRun(ProofState proofState, ProcedureState procState, AtomicStmt atomicStmt, StmtList abstStmt, VariableSeq newlocals)
        {
            return DoRun(proofState, procState.GetAtomicBlock(atomicStmt.label), abstStmt, newlocals);
        }

        static public bool DoRun(ProofState proofState, AtomicBlock atomicBlock, StmtList abstStmt, VariableSeq newlocals)
        {
            ProcedureState procState = atomicBlock.procState;

            foreach (Variable var in newlocals)
            {
                if (procState.GetLocalVar(var.Name) != null)
                {
                    Output.AddError("Variable already exists: " + var.Name);
                    return false;
                }
            }

            //--------------------------------------------------
            Expr inv = proofState.InvariantForProc(procState);

            //--------------------------------------------------
            BigBlock parent = Qoogie.GetParentBigBlock(atomicBlock.parent);

            AtomicStmt abstAtom;
            IdentifierExprSeq origModifies;
            CodeTransformations.MakeBranch(procState, parent, abstStmt, newlocals, out abstAtom, out origModifies);

            //--------------------------------------------------
            AtomicBlock abstBlock = procState.GetAtomicBlock(abstAtom.label);
            bool result = false;
            if (abstBlock.IsInvariant(inv))
            {
                Output.AddLine("New statement preserves the invariant!");

                if (atomicBlock.IsAbstractedBy(inv, abstBlock, newlocals))
                {
                    Output.AddLine("Abstraction relation holds!");

                    result = true;
                }
                else
                {
                    Output.AddLine("Abstraction relation does not hold!");
                }
            }
            else
            {
                Output.AddLine("New statement does not preserve the invariant!");
            }

            //--------------------------------------------------

            // undo the branching
            CodeTransformations.UndoMakeBranch(procState, parent, result, newlocals, origModifies);

            // if success, replace the body of atom
            if (result)
            {
                CodeTransformations.ReplaceBody(atomicBlock.parent, abstStmt);

                atomicBlock.parent.mover = AtomicStmt.Mover.None;

                // add the new modifies to the callers
                foreach (IdentifierExpr modExpr in procState.impl.Proc.Modifies)
                {
                    procState.CheckAddModifies(modExpr.Decl, true);
                }
            }

            procState.MarkAsTransformed();

            return result;
        }


    } // end class SimulateCommand

    
    public class AssertCommand : ProofCommand
    {
        public enum Kind { Block, Stmt, Proc }

        public Kind kind;
        public string label;

        public Expr assertion;

        public AssertCommand(string b, Kind k, Expr a)
            : base("assert")
        {
            this.label = b;
            this.assertion = a;
            this.kind = k;

            desc = "assert " + (kind == Kind.Proc ? "proc " : (kind == Kind.Stmt ? "stmt " : "")) + label + " " + Output.ToString(assertion);
        }

        public static string Usage()
        {
            return "assert [stmt|proc] procedureName assertionFormula";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("assert"))
            {
                Expr assertion;
                string label = parser.NextAsString();
                Kind kind = Kind.Block;
                if (label == "proc")
                {
                    kind = Kind.Proc;
                    label = parser.NextAsString();
                } else if(label == "stmt")
                {
                    kind = Kind.Stmt;
                    label = parser.NextAsString();
                }
                assertion = parser.RestAsExpr();
                return new AssertCommand(label, kind, assertion);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {
            ProcedureState procState = null;
            List<AtomicBlock> atomicBlocks = new List<AtomicBlock>();
            if (kind == Kind.Proc)
            {
                procState = proofState.GetProcedureState(label);
                atomicBlocks.AddRange(procState.AtomicBlocks);
            }
            else if(kind == Kind.Block)
            {
                AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(label);
                if (atomicBlock == null)
                {
                    Output.AddError("Atomic block does not exists: " + label);
                    return false;
                }
                atomicBlocks.Add(atomicBlock);
                procState = atomicBlock.procState;
            }
            else if (kind == Kind.Stmt)
            {
                AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(label);
                if (atomicBlock == null)
                {
                    Output.AddError("Atomic block does not exists: " + label);
                    return false;
                }
                procState = atomicBlock.procState;

                StmtList parentStmt = Qoogie.GetParentContext(atomicBlock.parent);
                bool found = false;
                for (int i = 0; i < parentStmt.BigBlocks.Count; ++i)
                {
                    BigBlock bb = parentStmt.BigBlocks[i];
                    if (!found && bb.ec is APLStmt)
                    {
                        APLStmt atom = bb.ec as APLStmt;
                        if (atom.label == atomicBlock.Label)
                        {
                            found = true;
                        }
                    }
                    if (found)
                    {
                        List<AtomicStmt> atomicStmts = new AtomicStmtCollector().Collect(bb);
                        foreach (AtomicStmt atomicStmt in atomicStmts)
                        {
                            atomicBlocks.Add(procState.GetAtomicBlock(atomicStmt.label));
                        }
                    }
                }
                Debug.Assert(found);
            }

            if (!procState.ResolveTypeCheckExpr(assertion, false))
            {
                Output.AddError("Expression is invalid");
                return false;
            }

            DoRun(atomicBlocks, assertion);

            return false;
        }

        static public void DoRun(List<AtomicBlock> atomicBlocks, Expr assertion)
        {
            foreach (AtomicBlock atomicBlock in atomicBlocks)
            {
                // now add the assertion at the beginning of the atomic block, but disable it.
                AssertCmd assertCmd = new AssertCmd(Token.NoToken, assertion);
                atomicBlock.InstrumentEntry(new CmdSeq(assertCmd));
                //atomicBlock.procState.condAssertsToCheck.Add(assertCmd);

                Output.AddLine("Atomic block annotated with the assertion.");
            }
        }

    } // end class AssertCommand

    public class AssumeCommand : ProofCommand
    {
        public string label;
        public Expr assertion;

        public AssumeCommand(string b, Expr a)
            : base("assert")
        {
            this.label = b;
            this.assertion = a;

            desc = "assume " + label + " " + Output.ToString(assertion);
        }

        public static string Usage()
        {
            return "assume atomicBlockLabel assertionFormula";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("assume"))
            {
                string label = parser.NextAsString();
                Expr assertion = parser.RestAsExpr();
                return new AssumeCommand(label, assertion);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {
            ProcedureState procState = null;

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(label);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + label);
                return false;
            }
            procState = atomicBlock.procState;

            if (!procState.ResolveTypeCheckExpr(assertion, false))
            {
                Output.AddError("Expression is invalid");
                return false;
            }

            DoRun(atomicBlock, assertion);

            return false;
        }

        static public void DoRun(AtomicBlock atomicBlock, Expr assertion)
        {
            // do the check
            ProcedureState procState = atomicBlock.procState;

            TPGenerator tpGen = new TPGenerator(atomicBlock);
            tpGen.assumeAsserts = true;

            Expr pcExpr = Expr.Neq(procState.pcExpr, ProofState.GetInstance().exSkipExpr);
            Expr wp = tpGen.Compute(TPGenOptions.ComputeWPre(Expr.Or(assertion, pcExpr)));
            Expr inv = ProofState.GetInstance().InvariantForProc(procState);
            Expr condition =  Expr.Imp(inv, wp);

            if(!Prover.GetInstance().CheckValid(condition))
            {
                Output.AddError("The assertion does not hold at the end of the block!");
                return;
            }

            // insert the atomic block
            AtomicStmt atom = Qoogie.MakeAtomicStmt(new CmdSeq(new AssumeCmd(Token.NoToken, assertion)), null, null);
            CodeTransformations.InsertAfter(procState.Body, atomicBlock.parent, atom);

            Output.AddLine("Inserted the assumption!");

            procState.MarkAsTransformed();
        }

    } // end class AssumeCommand

    public class AbstractCommand : ProofCommand
    {
        public enum Kind { Read, Write, Both}
        
        public string varname;
        public string blocklabel;
        public Kind kind;

        public AbstractCommand(string v, string l, Kind k)
            : base("abstract")
        {
            this.varname = v;
            this.blocklabel = l;
            this.kind = k;

            StringBuilder stb = new StringBuilder();
            stb.Append("abstract ");
            switch(kind)
            {
                case Kind.Read: stb.Append("read"); break;
                case Kind.Write: stb.Append("write"); break;
                case Kind.Both: stb.Append("both"); break;
            }
            stb.Append(" ").Append(varname).Append(" ").Append(blocklabel);

            desc = stb.ToString();
        }

        public static string Usage()
        {
            return "abstract read|write|both variableName atomicBlockLabel@procedureName";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("abstract"))
            {
                string rw = parser.NextAsString();
                Kind kind;
                switch (rw)
                {
                    case "read": kind = Kind.Read; break;
                    case "write": kind = Kind.Write; break;
                    case "both": kind = Kind.Both; break;
                    default: return null;
                }

                string v = parser.NextAsString();
                string b = parser.NextAsString();

                return new AbstractCommand(v, b, kind);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);

            if (atomicBlock == null)
            {
                Output.AddError("No such atomic block: " + blocklabel);
                return false;
            }

            Variable absVar;
            if (proofState.HasGlobalVar(varname))
            {
                absVar = proofState.GetGlobalVar(varname);
            }
            else
            {
                absVar = atomicBlock.procState.GetLocalVar(varname);
            }
            Debug.Assert(absVar != null);

            if (kind == Kind.Read)
            {
                if(!AbstractRead(proofState, atomicBlock, absVar)) {
                    Output.AddError("Could not abstract read!");
                }
            }
            else if (kind == Kind.Write)
            {
                if (!AbstractWrite(proofState, atomicBlock, absVar))
                {
                    Output.AddError("Could not abstract write!");
                }
            }
            else
            {
                if (!AbstractBoth(proofState, atomicBlock, absVar))
                {
                    Output.AddError("Could not abstract both!");
                }
            }

            return false;
        }

        static public bool AbstractBoth(ProofState proofState, AtomicBlock atomicBlock, Variable absVar)
        {
            ProcedureState procState = atomicBlock.procState;

            StmtList cloneBody = new StmtDuplicator().VisitStmtList(atomicBlock.parent.body);

            Variable fvar = DoAbstractBoth(procState, atomicBlock, absVar);

            //----------------------------------------------
            // check invariant
            
            Expr inv = proofState.InvariantForProc(procState);

            if (!atomicBlock.IsInvariant(inv))
            {
                Output.AddError("Atomic block violates the invariant after read+write abstraction: " + atomicBlock.UniqueLabel);

                atomicBlock.parent.body = cloneBody;
                procState.RemoveLocalVar(fvar);

                return false;
            }

            DoAbstractBoth(procState, atomicBlock, absVar);

            return true;
        }

        static public bool AbstractRead(ProofState proofState, AtomicBlock atomicBlock, Variable absVar)
        {
            ProcedureState procState = atomicBlock.procState;

            StmtList cloneBody = new StmtDuplicator().VisitStmtList(atomicBlock.parent.body);

            Variable fvar = DoAbstractRead(procState, atomicBlock, absVar);

            //----------------------------------------------
            // check invariant

            Expr inv = proofState.InvariantForProc(procState);
            
            if (!atomicBlock.IsInvariant(inv))
            {
                Output.AddError("Atomic block violates the invariant after read abstraction: " + atomicBlock.UniqueLabel);

                atomicBlock.parent.body = cloneBody;
                procState.RemoveLocalVar(fvar);

                return false;
            }

            return true;
        }

        static public bool AbstractWrite(ProofState proofState, AtomicBlock atomicBlock, Variable absVar)
        {

            ProcedureState procState = atomicBlock.procState;

            StmtList cloneBody = new StmtDuplicator().VisitStmtList(atomicBlock.parent.body);

            DoAbstractWrite(procState, atomicBlock, absVar);

            //----------------------------------------------
            // check invariant

            Expr inv = proofState.InvariantForProc(procState);

            if (!atomicBlock.IsInvariant(inv))
            {
                Output.AddError("Atomic block violates the invariant after write abstraction: " + atomicBlock.UniqueLabel);

                atomicBlock.parent.body = cloneBody;

                return false;
            }

            return true;
        }

        static int nextAbstId = 0;
        static private Variable DoAbstractRead(ProcedureState procState, AtomicBlock atomicBlock, Variable absVar)
        {
            // add fresh variable
            Variable fvar = procState.CreateFreshLocalVar("abst_" + absVar.Name + "_" + (nextAbstId++), absVar.TypedIdent.Type);

            // substitute reads of absVar
            Hashtable map = new Hashtable();
            map.Add(absVar, new IdentifierExpr(Token.NoToken, fvar));

            new MyReadSubstituter(map, true).VisitAtomicBlock(atomicBlock);

            // havoc the abstracted value at the beginning of the block
            HavocCmd havocCmd = new HavocCmd(Token.NoToken, new IdentifierExprSeq(new IdentifierExpr(Token.NoToken, fvar)));
            atomicBlock.InstrumentEntry(new CmdSeq(havocCmd));

            return fvar;
        }

        static private void DoAbstractWrite(ProcedureState procState, AtomicBlock atomicBlock, Variable absVar)
        {
            // insert havoc at the end
            HavocCmd havocCmd = new HavocCmd(Token.NoToken, new IdentifierExprSeq(new IdentifierExpr(Token.NoToken, absVar)));
            atomicBlock.InstrumentExit(new CmdSeq(havocCmd));

            procState.CheckAddModifies(absVar, true);
        }

        static private Variable DoAbstractBoth(ProcedureState procState, AtomicBlock atomicBlock, Variable absVar)
        {
            // add fresh variable
            Variable fvar = procState.CreateFreshLocalVar("abst_" + absVar.Name + "_" + (nextAbstId++), absVar.TypedIdent.Type);

            // substitute reads of absVar
            Hashtable map = new Hashtable();
            map.Add(absVar, new IdentifierExpr(Token.NoToken, fvar));

            new MyReadSubstituter(map, false).VisitAtomicBlock(atomicBlock);

            // havoc the abstracted value at the beginning of the block
            HavocCmd havocCmd = new HavocCmd(Token.NoToken, new IdentifierExprSeq(new IdentifierExpr(Token.NoToken, fvar)));
            atomicBlock.InstrumentEntry(new CmdSeq(havocCmd));

            return fvar;
        }


    } // end class AbstractCommand

public class AbstractCommand2 : ProofCommand
{
	public string varname;
	public string blocklabel;
	public bool reads;
	public bool writes; 

	public AbstractCommand2(string v, string l, bool r, bool w)
		: base("abstract")
	{
		this.varname = v;
		this.blocklabel = l;
		this.reads = r;
		this.writes = w;
		
		StringBuilder stb = new StringBuilder();
		stb.Append("abstract ");
		if(reads) {
			stb.Append("r");
		}		
		if(writes) {
			stb.Append("w");
		}		
		stb.Append(" ").Append(varname).Append(" ").Append(blocklabel);
		
		desc = stb.ToString();
		
	}

    public static string Usage()
    {
        return "abstract read|write variableName atomicBlockLabel@procedureName";
    }
	
	override public bool Run(ProofState proofState) {

        AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);

        if(atomicBlock == null) {
			Output.AddError("No such atomic block: "+ blocklabel);
			return false;
		}
			
		Variable absVar;
        if (proofState.HasGlobalVar(varname))
        {
            absVar = proofState.GetGlobalVar(varname);
        }
        else
        {
            absVar = atomicBlock.procState.GetLocalVar(varname);
        }
        Debug.Assert(absVar != null);

        return DoRun(proofState, atomicBlock, absVar, reads, writes);
	}

    static public bool DoRun(ProofState proofState, AtomicBlock atomicBlock, Variable absVar, bool reads, bool writes)
    {

        // now do abstraction

        if (reads)
        {
            atomicBlock.AbstractRead(absVar, proofState.InvariantForProc(atomicBlock.procState));
        }

        if (writes)
        {
            atomicBlock.AbstractWrite(absVar, proofState.InvariantForProc(atomicBlock.procState));

            ProcedureState procState = atomicBlock.procState;
            procState.CheckAddModifies(absVar, true);
        }

        return false;
    }
	
	
} // end class AbstractCommand


public class FieldAccess
{
    public Record rec;
    public Expr obj;
    public string fld;
    public bool isread;

    public FieldAccess(Record r, Expr o, string f, bool isr)
    {
        this.rec = r;
        this.obj = o;
        this.fld = f;
        this.isread = isr;
    }
}

public class NullCheckCommand : ProofCommand
{
    public NullCheckCommand()
        : base("nullcheck")
    {
        desc = "nullcheck";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("nullcheck"))
        {
            return new NullCheckCommand();
        }
        return null;
    }

    public static string Usage()
    {
        return "nullcheck";
    }

    override public bool Run(ProofState proofState)
    {
        foreach (ProcedureState procState in proofState.ProcedureStates)
        {
            Set<BigBlock> bbs = new BigBlocksCollector().Collect(procState.Body);
            foreach (BigBlock bb in bbs)
            {
                CmdSeq cmds = bb.simpleCmds;
                CmdSeq newcmds = new CmdSeq();

                for (int i = 0; i < cmds.Length; ++i)
                {
                    Cmd cmd = cmds[i];
                    Set<FieldAccess> accesses = new FieldAccessCollector().Collect(cmd);

                    foreach (FieldAccess access in accesses)
                    {
                        newcmds.Add(new AssertCmd(Token.NoToken, Expr.Eq(Expr.FieldSelect(Token.NoToken, access.obj, "alloc"), proofState.allocExpr)));
                    }

                    newcmds.Add(cmd);
                }

                bb.simpleCmds = newcmds;
            }

            procState.MarkAsTransformed();
        }

        Output.AddLine("Instrumented the program with null checks.");

        return false;
    }

} // end class SaveCommand

//public class AbstractPathCommand : ProofCommand
//{
//    public string varname;
//    public string blocklabel;
//    public bool reads;
//    public bool writes;

//    public AbstractPathCommand(string v, string l, bool r, bool w)
//        : base("abstractpath")
//    {
//        this.varname = v;
//        this.blocklabel = l;
//        this.reads = r;
//        this.writes = w;

//        StringBuilder stb = new StringBuilder();
//        stb.Append("abstractpath ");
//        if (reads)
//        {
//            stb.Append("r");
//        }
//        if (writes)
//        {
//            stb.Append("w");
//        }
//        stb.Append(" ").Append(varname).Append(" ").Append(blocklabel);

//        desc = stb.ToString();

//    }

//    override public bool Run(ProofState proofState)
//    {

//        AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);

//        if (atomicBlock == null)
//        {
//            Output.AddError("No such atomic block: " + blocklabel);
//            return false;
//        }

//        Set<AtomicBlock> successors = CodeAnalyses.ComputeReachableAtomicBlocks(atomicBlock);

//        Variable absVar;
//        if (proofState.HasGlobalVar(varname))
//        {
//            absVar = proofState.GetGlobalVar(varname);
//        }
//        else
//        {
//            absVar = atomicBlock.procState.GetLocalVar(varname);
//        }
//        Debug.Assert(absVar != null);

//        foreach (AtomicBlock ablock in successors)
//        {
//            AbstractCommand.DoRun(proofState, ablock, absVar, reads, writes);
//        }

//        return false;
//    }


//} // end class AbstractCommand


} // end namespace QED