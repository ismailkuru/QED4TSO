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


    public class SyncMutexCommand : SyncCommand
    {
        public Expr syncPredicate;

        public Variable auxVar;

        public string auxVarName;

        public string[] vars;

        private Expr inv;

        public SyncMutexCommand(Expr predicate, string auxname, string[] vs)
            : base()
        {
            this.syncPredicate = predicate;
            this.auxVarName = auxname;
            this.vars = vs;

            desc = "sync mutex " + auxVarName + " " + Util.ArrayToString(vars) + Output.ToString(this.syncPredicate);
        }

        override protected void AnnotateProgram(ProofState proofState)
        {

            
        }

        override protected void StartSync(ProofState proofState)
        {
            proofState.ResolveTypeCheckExpr(this.syncPredicate, false);

            foreach (ProcedureState procState in proofState.procedureStates.Values)
            {
                procState.RecomputeTransitionPredicates();
            }

            // create the auxiliary variable
            auxVar = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, auxVarName, BasicType.Int));
            IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVar);

            ProofState.GetInstance().AddAuxVar((GlobalVariable)auxVar);
            Output.LogLine("Added new auxiliary variable " + auxVarName);

            this.inv = Expr.Iff(Expr.Not(syncPredicate),
                                Expr.Eq(auxExp, Expr.Literal(0)));
        }

        override protected Expr ComputeTransitionAnnotation()
        {
            // add the extra condition to each transition predicate
            IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVar);
            Expr pred = this.syncPredicate;
            Expr predprime = ProofState.GetInstance().MakePrime(pred);
            Expr notpred = Expr.Not(pred);
            Expr notpredprime = Expr.Not(predprime);

            Expr annotExpr = Logic.And(
                                        Expr.Imp(Expr.Iff(pred, predprime), Expr.Eq(auxExp, ProofState.GetInstance().GetPrimedExpr(auxVar))),
                                        Expr.Imp(Expr.And(notpred, predprime), Expr.Eq(ProofState.GetInstance().GetPrimedExpr(auxVar), ProofState.GetInstance().tidExpr)),
                                        Expr.Imp(Expr.And(pred, notpredprime), Expr.Eq(ProofState.GetInstance().GetPrimedExpr(auxVar), Expr.Literal(0))));

            return annotExpr;
        }

        override protected void EndSync(ProofState proofState)
        {
            Expr annotExpr = ComputeTransitionAnnotation();

            foreach (ProcedureState procState in proofState.procedureStates.Values)
            {
                foreach (AtomicBlock atomicBlock in procState.atomicBlocks)
                {
                    atomicBlock.PushAnnotation(annotExpr);
                }
            }

            proofState.invs.Add(this.inv);
        }
    } // end class RefineCommand


} // end namespace QED
