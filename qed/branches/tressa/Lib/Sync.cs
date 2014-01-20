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


    public abstract class SyncCommand : ProofCommand
    {

        public SyncCommand()
            : base("sync")
        {

        }

        override public bool Run(ProofState proofState)
        {
            StartSync(proofState);

            AnnotateProgram(proofState);

            EndSync(proofState);

            return false;
        }

        abstract protected void AnnotateProgram(ProofState proofState);

        abstract protected void StartSync(ProofState proofState);

        abstract protected Expr ComputeTransitionAnnotation();

        abstract protected void EndSync(ProofState proofState);
    }

} // end namespace QED