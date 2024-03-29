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
    using System.Text;
using System.Collections;
using System.Collections.Generic;
using Microsoft.Boogie;
using BoogiePL;
using System.Diagnostics;
using Microsoft.Boogie.AbstractInterpretation;
using AI = Microsoft.AbstractInterpretationFramework;
using Microsoft.Contracts;
using PureCollections;

public class Util {
	
	static public VariableSeq RemoveFromVarSeq(VariableSeq seq, Variable elt) {
		VariableSeq newSeq = new VariableSeq();
		foreach(object obj in seq) {
			if(obj != elt) {
				newSeq.Add(obj);
			}
		}
		return newSeq;
	}
	
	
	public static void CreateEmptyFile(string file_name) {
		FileStream fs = null;
		if(File.Exists(file_name)) {
			 fs = File.Open(file_name, FileMode.Truncate);
		} else {
			fs = File.Open(file_name, FileMode.CreateNew);
		}
		fs.Close();
	}
	
	public static Set<GlobalVariable> FilterGlobalVariables(Set<Variable> vars) {
		Set<GlobalVariable> globals = new Set<GlobalVariable>();
		foreach(Variable var in vars) {
			if(var is GlobalVariable) {
				globals.Add((GlobalVariable)var);
			}
		}
		return globals;
	}
	
	public static Set FilterGlobalVariables(Set vars) {
		Set globals = new Set();
		foreach(object var in vars) {
			if(var is GlobalVariable) {
				globals.Add((GlobalVariable)var);
			}
		}
		return globals;
	}

    public static string ToGuiString(string str)
    {
        return str.Replace("\n", "\r\n");
    }

    public static string FromGuiString(string str)
    {
        return str.Replace("\r\n", "\n");
    }

    public static void CopyToClipboard(string str) {
        System.Windows.Forms.Clipboard.SetText(str);
    }



    public static string ArrayToString(string[] vars)
    {
        StringBuilder strb = new StringBuilder();
        int i = 0;
        for (; i < vars.Length - 1; ++i)
        {
            strb.Append(vars[i]).Append(",");
        }
        if (i < vars.Length)
        {
            strb.Append(vars[i]);
        }
        return strb.ToString();
    }


    public static string GetExecutingPath()
    {
        return Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location);
    }

    internal static VariableSeq FilterLocalVariables(VariableSeq vars)
    {
        VariableSeq globals = new VariableSeq();
        foreach (object var in vars)
        {
            if (var != null && !(var is GlobalVariable))
            {
                globals.Add(var);
            }
        }
        return globals;
    }

    internal static VariableSeq FilterGlobalVariables(VariableSeq vars)
    {
        VariableSeq globals = new VariableSeq();
        foreach (object var in vars)
        {
            if (var is GlobalVariable)
            {
                globals.Add((GlobalVariable)var);
            }
        }
        return globals;
    }

    internal static VariableSeq RemoveDuplicates(VariableSeq variableSeq)
    {
        VariableSeq newVars = new VariableSeq();
        foreach (Variable var in variableSeq)
        {
            if (!newVars.Has(var))
            {
                newVars.Add(var);
            }
        }
        return newVars;
    }

    internal static IdentifierExprSeq RemoveDuplicates(IdentifierExprSeq variableSeq)
    {
        IdentifierExprSeq newVars = new IdentifierExprSeq();
        foreach (IdentifierExpr var in variableSeq)
        {
            if (!newVars.Has(var))
            {
                newVars.Add(var);
            }
        }
        return newVars;
    }

    internal static IdentifierExprSeq MakeIdentifierExprSeq(VariableSeq variableSeq)
    {
        IdentifierExprSeq seq = new IdentifierExprSeq();
        foreach (Variable var in variableSeq)
        {
            seq.Add(new IdentifierExpr(Token.NoToken, var));
        }
        return seq;
    }


    public static List<string> ReadLinesFromFile(string filename)
    {
        List<string> lst = new List<string>();
        using (StreamReader reader = new StreamReader(filename))
        {
            while (!reader.EndOfStream)
            {
                string line = reader.ReadLine();
                lst.Add(line);
            }
        }
        return lst;
    }

    public static string ReadFromFile(string filename)
    {
        StringBuilder strb = new StringBuilder();
        using (StreamReader reader = new StreamReader(filename))
        {
            while (!reader.EndOfStream)
            {
                string line = reader.ReadLine();
                strb.AppendLine(line);
            }
        }
        return strb.ToString();
    }

    public static void WriteLinesToFile(string filename, List<string> lines)
    {
        using (StreamWriter writer = new StreamWriter(filename))
        {
            foreach (string line in lines)
            {
                writer.WriteLine(line);
            }
        }
    }

    public static void WriteToFile(string filename, string lines)
    {
        using (StreamWriter writer = new StreamWriter(filename))
        {
            writer.Write(lines);
        }
    }



    public static string AddLineNumbers(string str, bool output_rn)
    {
        // get the lines
        string[] lines = str.Split(new string[] {"\r\n", "\n"}, StringSplitOptions.None);

        // number the lines
        StringBuilder strb = new StringBuilder();
        for (int i = 0; i < lines.Length; ++i)
        {
            strb.Append(string.Format("{0,4:D}", i + 1)).Append(":  ").Append(lines[i]).Append(output_rn ? "\r\n" : "\n");
        }
        return strb.ToString();
    }

    public static string RemoveLineNumbers(string str, bool output_rn)
    {
        // get the lines
        string[] lines = str.Split(new string[] { "\r\n", "\n" }, StringSplitOptions.None);

        // un-number the lines
        StringBuilder strb = new StringBuilder();
        for (int i = 0; i < lines.Length; ++i)
        {
            string s = lines[i];
            int idx = s.IndexOf(':');
            string sub = idx >= 0 ? s.Substring(0, idx).Trim() : "";
            int num;
            if (int.TryParse(sub, out num))
            {
                strb.Append(lines[i].Substring(idx + 1 + /*!*/ 2)).Append(output_rn ? "\r\n" : "\n");
            }
            else
            {
                strb.Append(lines[i]).Append(output_rn ? "\r\n" : "\n");
            }
        }
        return strb.ToString();
    }

} // end class Util

  
} // end namespace QED