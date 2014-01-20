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
    using System.Windows.Forms;
    using System.IO;
    using System.Collections;
    using System.Collections.Generic;
    using Microsoft.Boogie;
    using BoogiePL;
    using System.Diagnostics;
    using Microsoft.Boogie.AbstractInterpretation;
    using AI = Microsoft.AbstractInterpretationFramework;
    using Microsoft.Contracts;
    using System.Text;
    using Type = Microsoft.Boogie.Type;


    public class QuantElim
    {

        public static Expr EliminateExists(Expr expr) 
        {
            NAryExpr naexpr = expr as NAryExpr;
            Debug.Assert(naexpr != null && naexpr.Fun.FunctionName == "==>");

            Expr lhs = naexpr.Args[0];
            Expr rhs = naexpr.Args[1];

            // compute free variables
            Set<Variable> fv = MyQuantExprVisitor.ExistsVisitor().Collect(lhs);

            // remove exists
            lhs = MyQuantExprVisitor.ExistsVisitor().Eliminate(lhs);
            Debug.Assert(lhs != null);

            // collect havoced variables of rhs
            Set<Variable> hvars = MyQuantExprVisitor.ExistsVisitor().Collect(rhs);

            // ask for instantiation for each bounded var
            foreach (Variable hvar in hvars)
            {
                Expr inst = AskForInst(lhs, rhs, hvar, fv);

                // substitute
                Hashtable map = new Hashtable();
                map.Add(hvar, inst);
                rhs = MyQuantExprVisitor.ExistsVisitor().Substitute(rhs, map);
            }

            return Expr.Imp(lhs, rhs);
        }

        public static Expr EliminateForall(Expr expr)
        {
            NAryExpr naexpr = expr as NAryExpr;
            Debug.Assert(naexpr != null && naexpr.Fun.FunctionName == "==>");

            Expr lhs = naexpr.Args[0];
            Expr rhs = naexpr.Args[1];

            // compute free variables
            Set<Variable> fv = MyQuantExprVisitor.ForallVisitor().Collect(rhs);

            // remove exists
            rhs = MyQuantExprVisitor.ForallVisitor().Eliminate(rhs);
            Debug.Assert(rhs != null);

            // collect havoced variables of rhs
            Set<Variable> hvars = MyQuantExprVisitor.ForallVisitor().Collect(lhs);

            // ask for instantiation for each bounded var
            foreach (Variable hvar in hvars)
            {
                Expr inst = AskForInst(lhs, rhs, hvar, fv);

                // substitute
                Hashtable map = new Hashtable();
                map.Add(hvar, inst);
                lhs = MyQuantExprVisitor.ForallVisitor().Substitute(lhs, map);
            }

            return Expr.Imp(lhs, rhs);
        }

        private static Expr AskForInst(Expr lhs, Expr rhs, Variable hv, Set<Variable> fv)
        {
            StringBuilder sb = new StringBuilder();

            sb.Append("Enter instantiation for: ");
            sb.AppendLine(hv.Name);

            sb.AppendLine();
            sb.AppendLine(Output.ToString(lhs));
            sb.AppendLine("==>");
            sb.AppendLine(Output.ToString(rhs));

            string instStr = InputBox.Show("Enter instantiation", sb.ToString());
            Debug.Assert(instStr != null);

            Expr instExpr = Qoogie.ParseExpr(instStr);
            Debug.Assert(instExpr != null);

            ProofState.GetInstance().ResolveTypeCheckExpr(instExpr, false, fv);

            return lhs;
        }

        
    }

} // end namespace QED