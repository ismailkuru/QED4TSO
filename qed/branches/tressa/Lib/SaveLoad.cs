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


    public class SaveCommand : ProofCommand
    {
        string filename;

        public SaveCommand(string file)
            : base("save")
        {
            this.filename = file;
            desc = "save " + filename;
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("save"))
            {
                if (parser.HasNext())
                {
                    string filename = parser.NextAsString();
                    return new SaveCommand(filename);
                }
            }
            return null;
        }

        public static string Usage()
        {
            return "save file-name";
        }

        override public bool Run(ProofState proofState)
        {
            try
            {
                Util.WriteToFile(this.filename, proofState.TextView);
                Output.AddError("Program saved to " + this.filename);
            }
            catch(Exception e)
            {
                Output.AddError("Error while saving the current program!");
                Output.Add(e);
            }

            return false;
        }

    } // end class SaveCommand

    public class LoadCommand : ProofCommand
    {
        string filename;

        public LoadCommand(string file)
            : base("load")
        {
            this.filename = file;
            desc = "load " + filename;
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("load"))
            {
                if (parser.HasNext())
                {
                    string filename = parser.NextAsString();
                    return new LoadCommand(filename);
                }
            }
            return null;
        }

        public static string Usage()
        {
            return "load file-name";
        }

        override public bool Run(ProofState proofState)
        {
            throw new NotImplementedException();
        }

    } // end class LoadCommand
    
} // end namespace QED
