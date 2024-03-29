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

namespace Microsoft.Boogie {

using QED;
using System;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using BoogiePL;
using System.Diagnostics;


public class GatedActionHelper
  {

    // this requires that there is no old() in trans but primes, and trans is not compact but full
    //static public bool IsReflexive(ProcedureState procState, Expr invs, Expr gate, Expr trans)
    //{
    //    // transition[V/V']
    //    trans = procState.MakeUnprimed(trans);

    //    // (inv && gate) ==> transition[V/V']
    //    Expr condition = Expr.Imp(Expr.And(invs, gate), trans);

    //    return Prover.GetInstance().CheckValid(condition);
    //}

    // this requires that there is no old() in trans but primes, and trans is not compact but full
    static public Set<Expr> IsInvariant(Expr inv, Expr gate, Expr trans)
    {
        //----------------------------------------
        // label the conjuncts
        // Expr invp = ProofState.GetInstance().MakePrime(inv);

        Hashtable invMap = new Hashtable();
        Set<Expr> conjuncts = Logic.GetTopConjuncts(inv);
        int count = 0;
        Expr invp = Expr.True;
        foreach (Expr c in conjuncts)
        {
            string lbl = "InvLbl_" + (count++);
            Expr pe = ProofState.GetInstance().MakePrime(c);
            invMap.Add(lbl, c);
            
            invp = Expr.And(invp, new LabeledExpr(lbl, pe, false));
        }

        //----------------------------------------
        // inv ==> (!gate || (gate && trans ==> invp))
        // Expr condition = Expr.Imp(inv, Expr.Or(Expr.Not(gate), Expr.Imp(Expr.And(gate, trans), invp)));
        Expr condition = Expr.Imp(inv, Expr.Imp(Expr.And(gate, trans), invp));

        bool result = Prover.GetInstance().CheckValid(condition);

        //----------------------------------------
        if (!result)
        {
            Set<Expr> failed = new Set<Expr>();
            foreach (string lbl in Prover.GetInstance().failedLabels)
            {
                if (lbl.StartsWith("InvLbl_"))
                {
                    failed.Add(invMap[lbl] as Expr);
                }
            }
            if (failed.Count == 0)
            {
                Output.AddError("Invariant check failed with no failed labels!");
            }
            return failed;
        }
        return null;
    }

    static public GatedAction Translate(ProofState proofState, ProcedureState procState, Cmd cmd)
    {
        if (cmd is GatedAction)
        {
            return cmd as GatedAction;
        }
        else if (cmd is CallCmd)
        {
            CallCmd callCmd = cmd as CallCmd;

            ProcedureState calleeState = proofState.GetProcedureState(callCmd.Proc.Name);
            return calleeState.SpecAtCall(procState, callCmd);
        }
        else if (cmd is AssertCmd)
        {
            AssertCmd assertCmd = cmd as AssertCmd;

            return new GatedAction(cmd.tok, assertCmd.Expr, Expr.True, new IdentifierExprSeq(), true);
        }
        else if (cmd is AssumeCmd)
        {

            AssumeCmd assumeCmd = cmd as AssumeCmd;

            return new GatedAction(cmd.tok, Expr.True, assumeCmd.Expr, new IdentifierExprSeq(), false);
        }
        else if (cmd is AssignCmd)
        {
            AssignCmd assignCmd = cmd as AssignCmd;

            Expr expr = Expr.True;
            IdentifierExprSeq modVars = new IdentifierExprSeq();

            for (int i = 0; i < assignCmd.Lhss.Count; i++)
            {

                Expr rhs = Logic.MakeOld(assignCmd.Rhss[i]);
                Expr lhs = assignCmd.Lhss[i].AsExpr;

                expr = Expr.And(expr, Expr.Eq(lhs, rhs));
                modVars.Add(assignCmd.Lhss[i].DeepAssignedIdentifier);
            }

            return new GatedAction(cmd.tok, Expr.True, expr, modVars, false);
        }
        //else if (cmd is ArrayAssignCmd)
        //{

        //    ArrayAssignCmd arrayCmd = (ArrayAssignCmd)cmd;

        //    Expr array = Logic.MakeOld(arrayCmd.Array);
        //    Expr index0 = Logic.MakeOld(arrayCmd.Index0);
        //    Expr index1 = arrayCmd.Index1 == null ? null : Logic.MakeOld(arrayCmd.Index1);
        //    Expr rhs = Logic.MakeOld(arrayCmd.Rhs);

        //    UpdateExpr storeExp = new UpdateExpr(cmd.tok, array, index0, index1, rhs);
        //    storeExp.Type = arrayCmd.Array.Type;

        //    return new GatedAction(cmd.tok, Expr.True, Expr.Eq(arrayCmd.Array, storeExp), new IdentifierExprSeq(arrayCmd.Array), false);
        //}
        else if (cmd is HavocCmd)
        {
            HavocCmd havocCmd = cmd as HavocCmd;

            return new GatedAction(cmd.tok, Expr.True, Expr.True, new IdentifierExprSeq(havocCmd.Vars), false);

        }
        return null;
    }
    
  }


} // end namespace QED