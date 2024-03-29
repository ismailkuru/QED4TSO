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
  
#if false
public class CleanupCommand : ProofCommand
{
	string varname;
	
	public CleanupCommand(string name)
		: base("cleanup")
	{
		this.varname = name;
		desc = "cleanup " + varname;
		
	}
	
	override public bool Run(ProofState proofState) {
		
		Set freeVars = new Set();
		
		foreach(ProcedureState procState in proofState.procedureStates.Values) {
			if(!procState.IsReduced) {
				foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
					foreach(Block block in atomicBlock.blocks) {
						CmdSeq newCmds = new CmdSeq();
						for(int i = 0, n = block.Cmds.Length; i < n; ++i) {
							Cmd cmd = block.Cmds[i];
							bool clean = false;
							if(cmd is AssumeCmd) {
								Expr expr = (cmd as AssumeCmd).Expr;
								freeVars.Clear();
								expr.ComputeFreeVariables(freeVars);
								
								foreach(Variable var in freeVars) {
									if(varname == var.Name) {
										clean = true;
										break;
									}
								}
							} else
							if(cmd is AssignCmd) {
                                freeVars.Clear();

                                AssignCmd assignCmd = cmd as AssignCmd;

								List<AssignLhs> exprL = assignCmd.Lhss;
                                foreach (AssignLhs alhs in exprL)
                                {
                                    freeVars.Add(alhs.DeepAssignedVariable);
                                }
                                
                                List<Expr> exprR = assignCmd.Rhss;
                                foreach (Expr expr in exprR)
                                {
                                    expr.ComputeFreeVariables(freeVars);
                                }
								
								foreach(Variable var in freeVars) {
									if(varname == var.Name) {
										clean = true;
										break;
									}
								}
							}
							if(!clean) {
								newCmds.Add(cmd);
							}
						} // end for
						block.Cmds = newCmds;
					}
				}
			}
		}
		
		// clean up invariants
		List<Expr> newList = new List<Expr>();
		foreach(Expr expr in proofState.invs) {
			bool clean = false;
			freeVars.Clear();
			expr.ComputeFreeVariables(freeVars);
			
			foreach(Variable var in freeVars) {
				if(varname == var.Name) {
					clean = true;
					Output.AddLine("Cleaned up the invariant " + expr);
					break;
				}
			}
			if(!clean) {
				newList.Add(expr);
			}
		}
		proofState.invs.Clear();
		proofState.invs.AddRange(newList);
		
		// clean up rely
		newList.Clear();
		foreach(Expr expr in proofState.rely) {
			bool clean = false;
			freeVars.Clear();
			expr.ComputeFreeVariables(freeVars);
			
			foreach(Variable var in freeVars) {
				if(varname == var.Name) {
					clean = true;
					Output.AddLine("Cleaned up the rely condition " + expr);
					break;
				}
			}
			if(!clean) {
				newList.Add(expr);
			}
		}
		proofState.rely.Clear();
		proofState.rely.AddRange(newList);
		
		// clean up guarantee
		newList.Clear();
		foreach(Expr expr in proofState.guar) {
			bool clean = false;
			freeVars.Clear();
			expr.ComputeFreeVariables(freeVars);
			
			foreach(Variable var in freeVars) {
				if(varname == var.Name) {
					clean = true;
					Output.AddLine("Cleaned up the guarantee condition " + expr);
					break;
				}
			}
			if(!clean) {
				newList.Add(expr);
			}
		}
		proofState.guar.Clear();
		proofState.guar.AddRange(newList);
		
		// clean up global variables
		GlobalVariable gvar = proofState.GetGlobalVar(varname);
		Debug.Assert(gvar != null);
		Output.AddLine("Cleaned up the aux variable " + gvar.Name);
		proofState.RemoveGlobalVar(gvar);
		
		return false;
	}
	
} // end class CleanupCommand
#endif


} // end namespace QED