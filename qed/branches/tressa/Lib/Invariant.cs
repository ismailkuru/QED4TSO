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
  

public class InvariantCommand : ProofCommand
{
	public Expr formula;

	public InvariantCommand(Expr inv)
		: base("invariant")
	{
		this.formula = inv;
		
		desc = "invariant" + " " + Output.ToString(this.formula);
	}

    public static string Usage()
    {
        return "invariant invariantFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("invariant"))
        {
            Expr inv = parser.RestAsExpr();
            return new InvariantCommand(inv);
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {
        proofState.ResolveTypeCheckExpr(this.formula, false);

        DoRun(proofState, this.formula);

        return false;

    }	
	
	static public bool DoRun(ProofState proofState, Expr formula) {

        bool sanity = (formula == null);

        bool tmp = CommandLineOptions.Clo.RestartProverPerVC;
        CommandLineOptions.Clo.RestartProverPerVC = false;

        if (!sanity)
        {
            if (Prover.GetInstance().CheckValid(Expr.Imp(proofState.Invariant, formula)))
            {
                Output.AddLine("The invariant is already implied by the existing invariant!");
                return false;
            }
        }
		
		Expr invs = sanity ? proofState.Invariant : Expr.And(proofState.Invariant, formula);


        if (Prover.GetInstance().CheckValid(Expr.Imp(invs, Expr.False)))
        {
            Output.AddError("The invariant implies False !!!");
            return false;
        }


        bool result = true;

        if (proofState.config.GetBool("Invariant", "CheckWithRG", false))
        {
            // TODO: the first invariant check below does not consider assertions, use the second one for a correct treatment !!!
            
            RelyGuarantee rg = new RelyGuarantee(invs, proofState.Rely, proofState.Guar);

            foreach (ProcedureState procState in proofState.procedureStates.Values)
            {
                if ((!procState.IsReduced) || procState.IsPublic)
                {
                    if (!rg.CheckProcedure(proofState, procState))
                    {
                        Output.LogLine("The new invariant does not hold!");

                        proofState.LastErrorTrace = rg.LastErrorTrace;
                        result = false;
                        break;
                    }
                }
            }
        }
        else
        {
            List<AtomicBlock> atomicBlocks = proofState.AtomicBlocks;
            foreach (AtomicBlock atomicBlock in atomicBlocks)
            {
                if (!atomicBlock.IsInvariant(invs))
                {
                    Output.AddError("The atomic block " + atomicBlock.UniqueLabel + " does not preserve the invariant!");
                    result = false;
                    break;
                }
            }
        }
		
		// if we reach here, the new invariant is safe to add to the proof state
        if (result && !sanity)
        {
            proofState.AddInvariant(formula);
            Output.LogLine("Added the new program invariant: " + Output.ToString(formula));
        }

        CommandLineOptions.Clo.RestartProverPerVC = tmp;

		return result;		
	}	
	
	override public void Print() {
		Output.LogLine("invariant " + Output.ToString(this.formula));
	}
	
} // end class InvariantCommand

//*************************************************************

public class LocalInvariantCommand : ProofCommand
{
	public Expr formula;
	public string procname;

	public LocalInvariantCommand(Expr inv, string name)
		: base("localinv")
	{
		this.formula = inv;
		this.procname = name;
		
		desc = "localinv" + " " + this.procname + " " +  Output.ToString(this.formula);
	}

    public static string Usage()
    {
        return "localinv procedureName invariantFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("localinv"))
        {
            string procname = parser.NextAsString();
            Expr linv = parser.RestAsExpr();
            return new LocalInvariantCommand(linv, procname);
        }
        return null;
    }
	
	override public bool Run(ProofState proofState) {
		
		ProcedureState procState = proofState.GetProcedureState(procname);
		procState.ResolveTypeCheckExpr(this.formula, false);
		
		// sanity check
		if(Prover.GetInstance().CheckValid(Expr.Imp(proofState.Invariant, this.formula))) {
			Output.AddLine("The invariant is already implied by the existing invariant!");
			return false;
		}
		
		Expr invs = Expr.And(proofState.Invariant, this.formula);
		
		// check the validity
		RelyGuarantee rg = new RelyGuarantee(invs, proofState.Rely, proofState.Guar);
		
		if((!procState.IsReduced) || procState.IsPublic) {
			if(!rg.CheckProcedure(proofState, procState)) {
				Output.LogLine("The new invariant does not hold!");
				
				proofState.LastErrorTrace = rg.LastErrorTrace;
				
				return true;
			}
		}
		
		// if we reach here, the new invariant is safe to add to the procedure state
		procState.localinvs.Add(this.formula);
		
		Output.LogLine("Added the new program invariant: " + Output.ToString(this.formula));
				
		return false;
		
	}	
	
} // end class LocalInvariantCommand

public class TransInvCommand : ProofCommand
{
    public Expr formula;

    public TransInvCommand(Expr inv)
        : base("transinv")
    {
        this.formula = inv;

        desc = "transinv" + " " + Output.ToString(this.formula);
    }

    public static string Usage()
    {
        return "transinv invariantFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("transinv"))
        {
            Expr tinv = parser.RestAsExpr();
            return new TransInvCommand(tinv);
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {

        proofState.ResolveTypeCheckExpr(this.formula, true);

        Expr rely = Expr.And(proofState.Rely, this.formula);
        Expr guar = Expr.And(proofState.Guar, this.formula);

        // check the validity
        RelyGuarantee rg = new RelyGuarantee(proofState.Invariant, rely, guar);

        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            if ((!procState.IsReduced) || procState.IsPublic)
            {
                if (!rg.CheckProcedure(proofState, procState))
                {
                    Output.LogLine("The new transition invariant does not hold!");
                    return true;
                }
            }
        }

        // if we reach here, the new transition invariant is safe to add to the proof state
        proofState.rely.Add(this.formula);
        proofState.guar.Add(this.formula);

        Output.LogLine("Added the new transition invariant: " + Output.ToString(this.formula));

        return false;

    }

} // end class InvariantCommand

} // end namespace QED