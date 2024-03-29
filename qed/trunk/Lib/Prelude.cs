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


    public class Prelude
    {
        public const string TIDName = "TID";
        public const string tidName = "tid";
        public const string tidxName = "tidx";
        public const string TidName = "Tid";

        public const string ExceptionTypeName = "Exception";
        public const string ExSkipName = "ExSkip";
        public const string ExReturnName = "ExReturn";
        public const string ExBreakName = "ExBreak";
        public const string ExContinueName = "ExContinue";

        public static string FileName = "qed_prelude.bpl";

        public static string AllocTypeName = "AllocType";
        public static string AllocName = "Alloc";
        public static string DeallocName = "Dealloc";
        public static string NullName = "Null";

        public static string MutexTypeName = "Mutex";
        public static string MutexOwnerFieldName = "owner";
        public static string LockProcName = "lock";
        public static string UnlockProcName = "unlock";

        public static Program GetPrelude()
        {
            return Qoogie.ParseFile(GetPreludePath());
        }

        public static string GetPreludePath()
        {
            return Util.GetExecutingPath() + "\\" + Prelude.FileName;
        }

        //// program containing the elements of the prelude
        //static public Program program;

        //public ResolutionContext GetResolutionContext(bool twostate)
        //{
        //    ResolutionContext rc = new ResolutionContext((IErrorSink)null);

        //    Debug.Assert(rc.StateMode == ResolutionContext.State.Single);
        //    if (twostate) rc.StateMode = ResolutionContext.State.Two;

        //    foreach (Declaration d in program.TopLevelDeclarations)
        //    {
        //        d.Register(rc);
        //    }

        //    return rc;

        //}

        //public TypecheckingContext GetTypecheckingContext()
        //{
        //    TypecheckingContext tc = new TypecheckingContext((IErrorSink)null);

        //    foreach (Declaration d in program.TopLevelDeclarations)
        //    {
        //        d.Typecheck(tc);
        //    }

        //    return tc;
        //}

//        static private string[] qed_elements = {
//// 0
//"const unique tid: int;",
//// 1
//"const unique tidx: int;",
//// 2
//"axiom (0 < tid) && (0 < tidx) && (tid != tidx);",
//// 3
//"var Tid : int;",
//// 4
//"invariant (0 < Tid) && (tid <= Tid) && (tidx <= Tid);",
//// 5
//@"
//type Exception;
//const unique ExReturn : Exception;
//const unique ExSkip : Exception;
//const unique ExBreak : Exception;
//const unique ExContinue : Exception;
//",
////6
//@"
//type boolean;
//const unique True : boolean;
//const unique False : boolean;
//axiom (forall b : boolean :: b == True || b == False);
//"
//                                               };

//        static private string CreatePrelude(ProofState proofState)
//        {
//            StringBuilder strb = new StringBuilder();

//            Program program = proofState.program;
//            if(Qoogie.GetConstant(program, tidName) == null) {
//                strb.AppendLine(qed_elements[0]);
//            }
//            if (Qoogie.GetConstant(program, tidxName) == null)
//            {
//                strb.AppendLine(qed_elements[1]);
//            }
//            strb.AppendLine(qed_elements[2]);

//            if (Qoogie.GetGlobalVar(program, TidName) == null)
//            {
//                strb.AppendLine(qed_elements[3]);
//            }
//            strb.AppendLine(qed_elements[4]);

//            // add exceptions
//            if (Qoogie.GetType(program, "Exception") == null)
//            {
//                strb.AppendLine(qed_elements[5]);
//            }

//            // add booleans
//            if (Qoogie.GetType(program, "boolean") == null)
//            {
//                strb.AppendLine(qed_elements[6]);
//            }

//            return strb.ToString();
//        }
        

//        internal static bool Append(ProofState proofState)
//        {
//            string preludeText = CreatePrelude(proofState);

//            // parse prelude
//            Program preludeProg = Qoogie.ParseProgram("QED Prelude", preludeText);

//            // success
//            if (preludeProg != null)
//            {
//                proofState.program.TopLevelDeclarations.AddRange(preludeProg.TopLevelDeclarations);
//            }

//            return Verifier.ResolveTypeCheck(proofState.program);
//        }

    } // end class Prelude



} // end namespace QED
