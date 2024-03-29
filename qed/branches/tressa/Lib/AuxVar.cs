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
  

public class AuxIntroCommand : ProofCommand
{
	string varname;
	string vartype;
    string procname;
    Kind kind;
    public enum Kind { Begin, End };

    public AuxIntroCommand(Kind k, string name, string type, string procname)
        : base("aux")
    {
        this.kind = k;
        this.varname = name;
		this.vartype = type;
        this.procname = procname;

		desc = "aux " + (kind == Kind.Begin ? "begin " : "end ") + varname + (vartype != null ? (" " + vartype) : "") + (procname != null ? (" " + procname) : "");
    }
	
	public static string Usage()
    {
        return "aux begin|end variableName [variableType] [procedureName]";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("aux"))
        {
            string kind = parser.NextAsString();
			if (kind.Equals("intro") || kind.Equals("begin"))
            {
                string auxname = parser.NextAsString();
                if (parser.HasNext())
                {
                    string auxtype = parser.NextAsString();
					if (parser.HasNext())
					{
						string procname = parser.NextAsString();
						return new AuxIntroCommand(Kind.Begin, auxname, auxtype, procname);
					}
					else
					{
						return new AuxIntroCommand(Kind.Begin, auxname, auxtype, null);
					}
                }				
            }
			else if (kind.Equals("remove") || kind.Equals("end"))
			{
				string auxname = parser.NextAsString();
				if (parser.HasNext())
				{
					string procname = parser.NextAsString();
					return new AuxIntroCommand(Kind.End, auxname, null, procname);
				}
				else
				{
					return new AuxIntroCommand(Kind.End, auxname, null, null);
				}
			}
        }
        return null;
    }

	override public bool Run(ProofState proofState)
	{
		ProcedureState procState = null;

		if (this.procname != null)
		{
			procState = proofState.GetProcedureState(procname);
			if (procState == null)
			{
				Output.AddError("Procedure could not been found: " + procname);
				return false;
			}
		}

		if (this.kind == Kind.Begin)
		{
			Type type = Qoogie.ParseType(vartype);

			if (!proofState.ResolveType(type, out type))
			{
				Output.AddError("Incorrect type!");
				return false;
			}

			DoBeginAdd(proofState, type, procState);
		}
		else
		{
			DoEndAdd(proofState, procState);
		}

		return false;
	}

	private Variable DoBeginAdd(ProofState proofState, Type type, ProcedureState procState)
	{
		Variable var = null;

		if (procState != null)
		{
			var = procState.GetLocalVar(varname);
			if (var != null)
			{
				// check if var is marked as hidden
				if (Qoogie.CheckQKeyValue(var, "isaux"))
				{
					Output.AddError("Variable has been added: " + var.Name);
					return null;
				}
				procState.MakeAuxVar(var as LocalVariable);
			}
			else
			{
				Debug.Assert(type != null);
				var = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, varname, type));
				procState.AddAuxVar(var as LocalVariable);
			}
		}
		else
		{
			var = proofState.GetGlobalVar(varname);
			if (var != null)
			{
				// check if var is marked as hidden
				if (Qoogie.CheckQKeyValue(var, "isaux"))
				{
					Output.AddError("Variable has been added: " + var.Name);
					return null;
				}
				proofState.MakeAuxVar(var as GlobalVariable);
			}
			else
			{
				Debug.Assert(type != null);
				var = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, varname, type));
				proofState.AddAuxVar(var as GlobalVariable);
			}
		}

		Output.AddLine("Done with introducing variable: " + varname);

		return var;
	}

	private void DoEndAdd(ProofState proofState, ProcedureState procState)
	{
		if (procState != null)
		{
			LocalVariable var = procState.GetLocalVar(varname) as LocalVariable;
			if (var != null)
			{
				// check if var is marked as hidden
				if (!Qoogie.CheckQKeyValue(var, "isaux"))
				{
					Output.AddError("Variable has not been added: " + var.Name);
					return;
				}
				procState.MakeNonAuxVar(var);
			}
			else
			{
				Output.AddError("Variable could not been found: " + var.Name);
				return;
			}
		}
		else
		{
			GlobalVariable var = proofState.GetGlobalVar(varname) as GlobalVariable;
			if (var != null)
			{
				// check if var is marked as hidden
				if (!Qoogie.CheckQKeyValue(var, "isaux"))
				{
					Output.AddError("Variable has not been added: " + var.Name);
					return;
				}
				proofState.MakeNonAuxVar(var);
			}
			else
			{
				Output.AddError("Variable could not been found: " + var.Name);
				return;
			}
		}

		Output.AddLine("Done with adding variable: " + varname);
	}


	public static Variable DoRun(ProofState proofState, string auxname, Type auxtype)
	{
		return new AuxIntroCommand(Kind.Begin, auxname, auxtype.ToString(), null).DoBeginAdd(proofState, auxtype, null);
	}
} // end class AddAuxCommand



public class AnnotateCommand : ProofCommand
{
	string blocklabel;
	string varname;
    string codeText;
	
	public AnnotateCommand(string label, string name, string code)
		: base("annotate")
	{
		this.blocklabel = label;
        this.varname = name;
        this.codeText = code;
		
		desc = "annotate " + blocklabel+ " " + varname + " " + codeText;
	}

    public static string Usage()
    {
        return "annotate atomicBlockLabel@procedureName variableName codeText";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("annotate"))
        {
            string label = parser.NextAsString();
            string name = parser.NextAsString();
            string code = parser.RestAsString();
            return new AnnotateCommand(label, name, code);
        }
        return null;
    }

	override public bool Run(ProofState proofState) {

        AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);
        if (atomicBlock == null)
        {
            Output.AddError("Could not find the block: " + blocklabel);
            return false;
        }

        Variable auxVar = proofState.GetGlobalVar(varname);
        if (auxVar == null)
        {
            Output.AddError("Could not find the variable: " + varname);
            return false;
        }

        ProcedureState procState = atomicBlock.procState;

        // parse, resolve and typecheck
        VariableSeq localVars;
        StmtList codeStmt = Qoogie.ParseCode(codeText, out localVars);

        Debug.Assert(localVars == null || localVars.Length == 0);

        CmdSeq cmds = codeStmt.BigBlocks[0].simpleCmds;
        atomicBlock.InstrumentExit(cmds);

        procState.CheckAddModifies(auxVar, true);

        procState.MarkAsTransformed();

        return false;
	}
	
} // end class AnnotateCommand

public class HideCommand : ProofCommand
{
    string varname;
    string procname;
    Kind kind;
    public enum Kind { Begin, End };

    public HideCommand(Kind k, string name, string procname)
        : base("hide")
    {
        this.kind = k;
        this.varname = name;
        this.procname = procname;

        desc = "hide " + (kind == Kind.Begin ? "begin " : "end ") + varname + (procname != null ? (" " + procname) : "");
    }

    public static string Usage()
    {
        return "hide begin|end variableName [procedureName]";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("hide"))
        {
            string kind = parser.NextAsString();
            if (kind.Equals("begin"))
            {
                string auxname = parser.NextAsString();
                if (parser.HasNext())
                {
                    string procname = parser.NextAsString();
                    return new HideCommand(Kind.Begin, auxname, procname);
                }
                return new HideCommand(Kind.Begin, auxname, null);
            }
            else if (kind.Equals("end"))
            {
                string auxname = parser.NextAsString();
                if (parser.HasNext())
                {
                    string procname = parser.NextAsString();
                    return new HideCommand(Kind.End, auxname, procname);
                }
                return new HideCommand(Kind.End, auxname, null);
            }
        }
        return null;
    }


    override public bool Run(ProofState proofState)
    {
        Variable var = null;
        ProcedureState procState = null;
        if (this.procname == null)
        {
            var = proofState.GetGlobalVar(this.varname);            
        }
        else
        {
            procState = proofState.GetProcedureState(procname);
            if (procState == null)
            {
                Output.AddError("Procedure could not been found: " + procname);
                return false;
            }
        }

        if (var == null)
        {
            Output.AddError("Variable could not been found: " + varname);
            return false;
        }

        if (this.kind == Kind.Begin)
        {
            DoBeginHide(proofState, var, procState);
        }
        else
        {
            DoEndHide(proofState, var, procState);
        }

        return false;
    }

    private void DoBeginHide(ProofState proofState, Variable var, ProcedureState procState)
    {
        // check if var is marked as hidden
        if (Qoogie.CheckQKeyValue(var, "ishidden"))
        {
            Output.AddError("Variable has already been hidden: " + var.Name);
            return;
        }

        if (procState != null)
        {
            procState.HideVar(var as LocalVariable);
        }
        else
        {
            proofState.HideVar(var as GlobalVariable);
        }
        
        Output.AddLine("Done with hiding variable: " + var.Name);
    }

    private void DoEndHide(ProofState proofState, Variable var, ProcedureState procState)
    {
        // check if var is marked as hidden
        if (!Qoogie.CheckQKeyValue(var, "ishidden"))
        {
            Output.AddError("Variable has not been hidden: " + var.Name);
            return;
        }

        if (procState != null)
        {
            procState.RemoveLocalVar(var as LocalVariable);
        }
        else
        {
            proofState.RemoveGlobalVar(var as GlobalVariable);
            
            // quantify the invariant
            proofState.QuantifyInvariant(var as GlobalVariable);
        }

        Output.AddLine("Done with removing variable: " + var.Name);
    }

} // end class HideCommand


} // end namespace QED