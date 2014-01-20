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
using System.Reflection;
  

public class EvalCommand : ProofCommand
{
	string classname;
	
	public EvalCommand(string name)
		: base("eval")
	{
		this.classname = name;
		desc = "eval " + classname;	
	}

    public static string Usage()
    {
        return "eval className";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("eval"))
        {
            string classname = parser.NextAsString();
            return new EvalCommand(classname);
        }
        return null;
    }

	
	override public bool Run(ProofState proofState) {
		
		Assembly assembly = Assembly.GetExecutingAssembly();
		
		ProofCommand command =  (ProofCommand) (assembly.CreateInstance(classname));
		
		return command.Run(proofState);
	}
	
} // end class CleanupCommand



} // end namespace QED