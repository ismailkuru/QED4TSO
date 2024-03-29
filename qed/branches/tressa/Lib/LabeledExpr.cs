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
using Microsoft.Boogie.AbstractInterpretation;
using AI = Microsoft.AbstractInterpretationFramework;
using Microsoft.Contracts;
using Type = Microsoft.Boogie.Type;

    public class LabeledExprHelper
    {

        static readonly string InvariantPrefix = "INV";
        static readonly string GuardPrefix = "GRD";
        static readonly string AssertPrefix = "ASS";
        static readonly string NegAssertPrefix = "NAS";
        static readonly string AtomicBlockPrefix = "WPC";
        static readonly string APLBlockPrefix = "APL";
        static readonly string BlockPrefix = "BLK";
        static readonly string PostCondPrefix = "PST";

        static public bool IsInvariant(string label)
        {
            return label.StartsWith(InvariantPrefix);
        }

        static public bool IsGuar(string label)
        {
            return label.StartsWith(GuardPrefix);
        }

        static public bool IsNegAssert(string label)
        {
            return label.StartsWith(NegAssertPrefix);
        }

        static public bool IsAtomicBlock(string label)
        {
            return label.StartsWith(AtomicBlockPrefix);
        }

        static public bool IsAPLBlock(string label)
        {
            return label.StartsWith(APLBlockPrefix);
        }

        static public bool IsBlock(string label)
        {
            return label.StartsWith(BlockPrefix);
        }

        static public bool IsPostCond(string label)
        {
            return label.StartsWith(PostCondPrefix);
        }

        static public bool IsAssert(string label)
        {
            return label.StartsWith(AssertPrefix);
        }

        static public Expr Invariant(APLBlock atomicBlock, Expr invs)
        {
            string label = LabeledExprHelper.InvariantPrefix + atomicBlock.UniqueId.ToString();
            return new LabeledExpr(label, invs, false, atomicBlock);
        }

        static public Expr Guar(APLBlock atomicBlock, Expr guar)
        {
            string label = LabeledExprHelper.GuardPrefix + atomicBlock.UniqueId.ToString();
            return new LabeledExpr(label, guar, false, atomicBlock);
        }

        static public Expr PostCond(APLBlock atomicBlock, Expr postcond)
        {
            string label = LabeledExprHelper.PostCondPrefix + atomicBlock.UniqueId.ToString();
            return new LabeledExpr(label, postcond, false, atomicBlock);
        }

        static public Expr AtomicBlock(APLBlock atomicBlock, Expr wp)
        {
            string label = LabeledExprHelper.AtomicBlockPrefix + atomicBlock.UniqueId.ToString();
            return Expr.Imp(new LabeledExpr(label, Expr.True, true, atomicBlock), wp);
        }

        static public Expr Block(Block block, Expr wp)
        {
            string label = LabeledExprHelper.BlockPrefix + block.UniqueId.ToString();
            return new LabeledExpr(label, wp, true, block);
        }

        //static public Expr NegAuxAssert(APLBlock atomicBlock, Expr cond)
        //{
        //    return new LabeledExpr(atomicBlock.Label, Expr.Not(cond), true);
        //}

        static public Expr NegAuxAssert(string label, APLBlock aplBlock, Expr cond)
        {
            return new LabeledExpr(label, Expr.Not(cond), true);
        }

        static public Expr AuxAssert(string label, APLBlock aplBlock, Expr cond)
        {
            return new LabeledExpr(label, cond, false);
        }

        static public Expr AuxTrans(string label, APLBlock aplBlock, Expr cond)
        {
            return Expr.Imp(new LabeledExpr(label, Expr.True, true, aplBlock), cond);
        }

        static public Expr Assert(Cmd cmd, Expr cond)
        {
            string label = LabeledExprHelper.AssertPrefix + cmd.UniqueId.ToString();
            return new LabeledExpr(label, cond, false, cmd);
        }
        
        internal static Expr APLBlock(APLBlock aplBlock, Expr wp)
        {
            string label = LabeledExprHelper.APLBlockPrefix + aplBlock.UniqueId.ToString();
            return Expr.Imp(new LabeledExpr(label, Expr.True, true, aplBlock), wp);
        }
    }
  
} // end namespace QED
