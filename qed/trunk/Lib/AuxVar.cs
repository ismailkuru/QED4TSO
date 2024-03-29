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
    string recordname;
    Kind kind;
    public enum Kind { Begin, End };

    public AuxIntroCommand(Kind k, string name, string type, string procname, string recordname)
        : base("aux")
    {
        this.kind = k;
        this.varname = name;
		this.vartype = type;
        this.procname = procname;
        this.recordname = recordname;

		desc = "aux " + (kind == Kind.Begin ? "begin " : "end ") + (recordname != null ? (recordname + ".") : "") + varname + (vartype != null ? (" " + vartype) : "") + (procname != null ? (" " + procname) : "");
    }
	
	public static string Usage()
    {
        return "aux begin|end [recordName.]variableName [variableType] [procedureName]";
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
						return new AuxIntroCommand(Kind.Begin, auxname, auxtype, procname, null);
					}
					else
					{
                        // procname null, check recordname
                        int i = auxname.IndexOf('.');

                        if (i >= 0)
                        {
                            return new AuxIntroCommand(Kind.Begin, auxname.Substring(i+1), auxtype, null, auxname.Substring(0, i));
                        }
                        else
                        {
                            return new AuxIntroCommand(Kind.Begin, auxname, auxtype, null, null);
                        }
					}
                }				
            }
			else if (kind.Equals("remove") || kind.Equals("end"))
			{
				string auxname = parser.NextAsString();
				if (parser.HasNext())
				{
					string procname = parser.NextAsString();
					return new AuxIntroCommand(Kind.End, auxname, null, procname, null);
				}
				else
				{
                    // procname null, check recordname
                    int i = auxname.IndexOf('.');

                    if (i >= 0)
                    {
                        return new AuxIntroCommand(Kind.End, auxname.Substring(i+1), null, null, auxname.Substring(0, i));
                    }
                    else
                    {
                        return new AuxIntroCommand(Kind.End, auxname, null, null, null);
                    }
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
					Output.AddError("Variable has already been added: " + var.Name);
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
        else if (recordname != null)
        {
            Record record = proofState.program.Records[recordname];
            if (record == null)
            {
                Output.AddError("Record not found: " + recordname);
                return null;
            }
            var = record.GetFieldMap(varname);
            if (var != null)
            {
                // check if var is marked as hidden
                if (Qoogie.CheckQKeyValue(var, "isaux"))
                {
                    Output.AddError("Field has been already added: " + var.Name);
                    return null;
                }
            }
            else
            {
                Debug.Assert(type != null);
                var = record.AddField(varname, type);
            }
            record.MakeAuxField(varname);
            proofState.MakeAuxVar(var as GlobalVariable);
        }
        else
		{
			var = proofState.GetGlobalVar(varname);
			if (var != null)
			{
				// check if var is marked as hidden
				if (Qoogie.CheckQKeyValue(var, "isaux"))
				{
					Output.AddError("Variable has been already added: " + var.Name);
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
        else if (recordname != null)
        {
            Record record = proofState.program.Records[recordname];
            if (record == null)
            {
                Output.AddError("Record not found: " + recordname);
                return;
            }
            Variable var = record.GetFieldMap(varname);
            if (var != null)
            {
                // check if var is marked as hidden
                if (!Qoogie.CheckQKeyValue(var, "isaux"))
                {
                    Output.AddError("Field has not been added: " + var.Name);
                    return;
                }
                record.MakeNonAuxField(varname);
                proofState.MakeNonAuxVar(var as GlobalVariable);
            }
            else
            {
                Output.AddError("Field could not been found: " + var.Name);
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
		return new AuxIntroCommand(Kind.Begin, auxname, auxtype.ToString(), null, null).DoBeginAdd(proofState, auxtype, null);
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
    string recordname;
    Kind kind;
    public enum Kind { Begin, End };

    public HideCommand(Kind k, string name, string procname, string recordname)
        : base("hide")
    {
        this.kind = k;
        this.varname = name;
        this.procname = procname;
        this.recordname = recordname;

        desc = "hide " + (kind == Kind.Begin ? "begin " : "end ") + (recordname != null ? (recordname + ".") : "") + varname + (procname != null ? (" " + procname) : "");
    }

    public static string Usage()
    {
        return "hide begin|end [recordName.]variableName [procedureName]";
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
                    return new HideCommand(Kind.Begin, auxname, procname, null);
                }
                else
                {
                    // procname null, check recordname
                    int i = auxname.IndexOf('.');

                    if (i >= 0)
                    {
                        return new HideCommand(Kind.Begin, auxname.Substring(i+1), null, auxname.Substring(0,i));
                    }
                    else
                    {
                        return new HideCommand(Kind.Begin, auxname, null, null);
                    }
                }
            }
            else if (kind.Equals("end"))
            {
                string auxname = parser.NextAsString();
                if (parser.HasNext())
                {
                    string procname = parser.NextAsString();
                    return new HideCommand(Kind.End, auxname, procname, null);
                }
                else
                {
                    // procname null, check recordname
                    int i = auxname.IndexOf('.');

                    if (i >= 0)
                    {
                        return new HideCommand(Kind.End, auxname.Substring(i+1), null, auxname.Substring(0, i));
                    }
                    else
                    {
                        return new HideCommand(Kind.End, auxname, null, null);
                    }
                }
            }
        }
        return null;
    }


    override public bool Run(ProofState proofState)
    {
        Variable var = null;
        ProcedureState procState = null;
        Record record = null;

        if (this.procname == null)
        {
            var = proofState.GetGlobalVar(this.varname);
            if (var == null)
            {
                Output.AddError("Variable not found: " + this.varname);
                return false;
            }
        }
        else if (recordname != null)
        {
            record = proofState.program.Records[this.recordname];
            if (record == null)
            {
                Output.AddError("Record not found: " + this.recordname);
                return false;
            }
            var = record.GetFieldMap(this.varname);
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
            DoBeginHide(proofState, var, procState, record);
        }
        else
        {
            DoEndHide(proofState, var, procState, record);
        }

        return false;
    }

    private void DoBeginHide(ProofState proofState, Variable var, ProcedureState procState, Record record)
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
            if (record != null)
            {
                record.HideField(varname);
            }

            proofState.HideVar(var as GlobalVariable);
        }
        
        Output.AddLine("Done with hiding variable: " + var.Name);
    }

    private void DoEndHide(ProofState proofState, Variable var, ProcedureState procState, Record record)
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
            if (record != null)
            {
                record.RemoveField(varname);
            }

            proofState.RemoveGlobalVar(var as GlobalVariable);
            
            // quantify the invariant
            proofState.QuantifyInvariant(var as GlobalVariable);
        }

        Output.AddLine("Done with removing variable: " + var.Name);
    }

} // end class HideCommand


} // end namespace QED