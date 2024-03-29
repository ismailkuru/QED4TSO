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
using Microsoft.Contracts;
    using System.Text;
  
public abstract class ProofCommand
{
	public string name;
	
	public string desc;
	
	public ProofCommand(string n) {
		this.name = n;
	}
	
	abstract public bool Run(ProofState proofState);
	
	public virtual void Print() {
		Output.Log(desc);
	}
	
	public override string ToString() {
		return desc;
	}
	
} // end class ProofCommand

public class ProofScript : IEnumerable<ProofCommand>
{
	private List<ProofCommand> commands;
	
	private string filename;
	
	public ProofScript(string name) {
		this.commands = new List<ProofCommand>();
		this.filename = name;
	}
	
	public void AddCommand(ProofCommand command) {
		commands.Add(command);	
	}
	
	public void InsertCommand(int index, ProofCommand command) {
		commands.Insert(index,command);
	}
	
	public void RemoveCommand(ProofCommand command) {
		commands.Remove(command);
	}

    public int Count
    {
        get
        {
            return commands.Count;
        }
    }
	
	public ProofCommand this[int i]
	{
		get {
			return commands[i];
		}
		
		set {
			commands[i] = value;
		}
	}
	
	#region IEnumerable<ProofCommand> Members

	public IEnumerator<ProofCommand> GetEnumerator()
    {
        for (int i = 0, n = commands.Count; i < n; ++i)
        {
            yield return this[i];
        }
    }
    
    IEnumerator IEnumerable.GetEnumerator()
    {
        for (int j = 0, n = commands.Count; j < n; ++j)
        {
            yield return this[j];
        }
    }

    #endregion
	
	static public ProofScript Parse(string filename) {
		ProofScript script = new ProofScript(filename);
		using (StreamReader reader = new StreamReader(filename)) {
            string prevline = null;
			while(!reader.EndOfStream) {
				string line = reader.ReadLine();
                // remove space
                line = line.Trim();
                if (line.Length == 0) continue;
                // remove comments
                if (line[0] == '#') continue;

                if (prevline != null)
                {
                    line = prevline + line;
                    prevline = null;
                }

                if (line.EndsWith("\\\\"))
                {
                    prevline = line.Substring(0, line.Length - 2);
                    continue;
                }

                // check inline command
                if (line.StartsWith("include"))
                {
                    string ifile = line.Substring(7).Trim();
                    ProofScript iscript = Parse(ifile);
                    script.AddScript(iscript);
                    continue;
                }

			    ProofCommand cmd = ParseCommand(line);
				if(cmd != null) script.AddCommand(cmd);								
			}
            Debug.Assert(prevline == null);
		}
		return script;
	}

    private void AddScript(ProofScript iscript)
    {
        commands.AddRange(iscript.commands);
    }
	
	static public ProofCommand ParseCommand(string cmdline) {
        // remove \\
        cmdline.Replace("\\\\", "");
        
		return CmdFactory.Create(cmdline);	
	}
	
	public void Print() {
		Output.LogLine("ProofScript:");
		foreach(ProofCommand cmd in commands) {
			cmd.Print();
			Output.LogLine();
		}
	}

    string[,] steps = {{"reduce", "mover",  "merge", "", "", "", "", "", "", "", "", ""},
                       {"simulate", "assert", "assume", "mutex", "annotate", "aux", "pre", "nullcheck", "rwlock", "mutexptr", "abstract", "refine"},
                       {"invariant", "", "", "", "", "", "", "", "", "", "", ""},
                       {"hoist", "peelout", "split", "inline", "", "", "", "", "", "", "", ""}};
    public string Report()
    {
        int stepid = -1;
        int stepct = 1;

        IDictionary<string, int> countMap = new Dictionary<string, int>();
        foreach(ProofCommand command in this) {
            if(!countMap.ContainsKey(command.name)) {
                countMap.Add(command.name, 0);
            }
            countMap[command.name] = countMap[command.name] + 1;

            // find main step index
            for (int i = 0; i < steps.GetLength(0); ++i)
            {
                for (int j = 0; j < steps.GetLength(1); ++j)
                {
                    if (steps[i, j] == "") break;
                    if (command.name.StartsWith(steps[i, j]))
                    {
                        if (stepid != i)
                        {
                            stepid = i;
                            ++stepct;
                        }
                    }
                }
            }
        }

        StringBuilder strb = new StringBuilder();
        strb.Append("Num commands: ").Append(this.Count).AppendLine();
        strb.Append("Num main steps: ").Append(stepct).AppendLine();
        foreach(string name in countMap.Keys) {
            strb.Append(name).Append(": ").Append(countMap[name]).AppendLine();
        }
        return strb.ToString();
    }
} // end class ProofScript


} // end namespace QED