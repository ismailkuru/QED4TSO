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
  

public class Dot
{
	public Dot() {
	}
	
	public void SaveDotOutput(string filename, string dotstr) {
		//StringWriter strw = new StringWriter();
		// ExternalProcess.Run("dot.exe", "", dotstr, strw);
		
		using(TextWriter filew = new StreamWriter(File.OpenWrite(filename))) {
			filew.WriteLine(dotstr);
		}
        
        Output.LogLine("Text written to dot file: " + filename);
	}
	
	public void PrintDotFile(string infilename, string outfilename) {
		
		ExternalProcess.Run("dot.exe", "-Tjpg " + infilename + " -o " + outfilename, Output.Target);
		
        Output.LogLine("Printed dot file written to dot file: " + outfilename);
	}
}

} // end namespace QED