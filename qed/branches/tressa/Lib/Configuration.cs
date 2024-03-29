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
using StringBuilder  = System.Text.StringBuilder;
  

	/// <summary>
	/// Summary description for Configuration.
	/// </summary>
	public class Configuration {
	
		protected Hashtable sections = new Hashtable();
		
		public Configuration() {
			 
		}

		public Configuration(string[] args) {
            if (args == null) return;

            if(args.Length == 1) {
				Parse(args[0]);
			} else if(args.Length > 2){
				Parse(args[2]);
				Set("Input", "BplFile", args[0]);
				Set("Input", "ScriptFile", args[1]);
			}

            string boogieoptions = GetStr("Boogie", "CommandLineOptions", "/print:-") // /printUnstructured
								  + " "
								  + GetStr("Input", "BplFile", "flags.bpl");

			string[] boogieargs = boogieoptions.Split(new char[] {' ', '\t'}, StringSplitOptions.RemoveEmptyEntries);

            CommandLineOptions.Clo.RunningBoogieFromCommandLine = true;
			if (CommandLineOptions.Clo.Parse(boogieargs) != 1)
			{
				Output.LogLine("*** Error: Parsing the command line arguments.");
				return;
			}
			if (CommandLineOptions.Clo.Files.Count == 0)
			{
				Output.LogLine("*** Error: No input files were specified.");
				return;
			}
			Output.LogLine("---Command arguments");
			foreach (string arg in args) 
			{
				Output.LogLine(arg);
			}
			Output.LogLine("--------------------");

			CommandLineOptions.Clo.RunningBoogieOnSsc = false;
            CommandLineOptions.Clo.PrintUnstructured = 0; // print only structured statements

            CommandLineOptions.Clo.Z3Options = GetZ3Options();
		}

        internal static List<string> GetZ3Options()
        {
            return Util.ReadLinesFromFile(Util.GetExecutingPath() + "\\z3.ini");
        }
		
		private static bool iscomment(string s) {
			for (int i = 0; i < s.Length; i++) {
				if (s[i] == ' ' || s[i] == '\t') {
					continue;
				}
				return s[i] == '#';
			}
			return true;
		}

		private static string issection(string s) {
			for (int i = 0; i < s.Length; i++) {
				if (s[i] == ' ' || s[i] == '\t') {
					continue;
				}
				if (s[i] != '[') {
					return null;
				}
				if (s[s.Length-1] != ']') {
					return null;
				}
				return s.Substring(i+1, s.Length-2-i);
			}
			Debug.Assert(false);
			return null;
		}

		public string GetStr(string var_name) {
			return GetStr("", var_name);
		}

		public int GetInt(string var_name) {
			return GetInt("", var_name);
		}

		public long GetLong(string var_name) {
			return GetLong("", var_name);
		}

		public int GetInt(string var_name, int defalutValue) {
			return GetInt("", var_name, defalutValue);
		}

		public long GetLong(string var_name, long defaultValue) {
			return GetLong("", var_name, defaultValue);
		}

		public string GetStr(string section_name, string var_name) {
			Hashtable sh = peeksection(section_name);

			if (sh != null) {
                string val =  sh[var_name] as string;
                if (val != null)
                {
                    val = val.Trim();
                    if (val != "")
                    {
                        return val;
                    }
				}
			}
			return null;
		}
		
		public string GetStr(string section_name, string var_name, string defaultValue) {
			string tmp = GetStr(section_name, var_name);
			if (tmp == null)
				return defaultValue;
			else return tmp;
		}

		public int GetInt(string sectionName, string varName) {
			return GetInt(sectionName, varName, 0);
		}

		/// <summary>
		/// Get the int value for the given section name and variable name
		/// </summary>
		/// <param name="sectionName">section name</param>
		/// <param name="varName">variable name</param>
		/// <param name="defaultValue">the default value if no match found</param>
		/// <returns>the value found in the config file or the default value
		/// when no match was found</returns>
		public int GetInt(string sectionName, string varName, int defaultValue) {
			string tmp = GetStr(sectionName, varName);
			if (tmp == null)
				return defaultValue;
			else return Int32.Parse(tmp);
		}

		/// <summary>
		/// Get the long value for the given section name and variable name
		/// </summary>
		/// <param name="sectionName">section name</param>
		/// <param name="varName">variable name</param>
		/// <param name="defaultValue">the default value if no match found</param>
		/// <returns>the value found in the config file or the default value
		/// when no match was found</returns>
		public long GetLong(string sectionName, string varName, long defaultValue) {
			string tmp = GetStr(sectionName, varName);
			if (tmp == null)
				return defaultValue;
			else return Int64.Parse(tmp);
		}

		public long GetLong(string sectionName, string varName) {
			return GetLong(sectionName, varName, (long) 0);
		}

		public bool GetBool(string var_name) {
			return GetBool("", var_name);
		}

		public bool GetBool(string var_name, bool defaultValue) {
			return GetBool("", var_name, defaultValue);
		}

		public bool GetBool(string sectionName, string var_name) {
			return GetBool(sectionName, var_name, true);
		}

		public bool GetBool(string sectionName, string var_name, bool defaultValue) {
            string tmp = GetStr(sectionName, var_name);
			if(tmp == null)
				return defaultValue;
			else return Boolean.Parse(tmp);
		}
		
		public void Set(string var_name, object val) {
			Set("", var_name, val);
		}
		
		public void Set(string sectionName, string var_name, object val) {
			Hashtable sh = getsection(sectionName);
			
			sh[var_name] = val.ToString();
		}
		
		public Hashtable getsection(string sectionName) {
			Hashtable sh = peeksection(sectionName);
			if(sh == null) {
				sh = new Hashtable();
				sections[sectionName] = sh;
			}
			return sh;
		}

		public Hashtable peeksection(string sectionName) {
			Hashtable sh = null;
			if(sections.Contains(sectionName)) {
				sh = (Hashtable) sections[sectionName];
			}
			return sh;
		}

		public void Parse(string conffile) {

			FileInfo fi = new FileInfo(conffile);
			StreamReader conf_file = fi.OpenText();
			string rbuf;
			Hashtable cursecn = getsection("");

			while ((rbuf = conf_file.ReadLine()) != null) {
				if (iscomment(rbuf)) {
					continue;
				}
				string secn = issection(rbuf);
				if (secn == null) {
					string [] namval;

					namval = rbuf.Split('=');
					if (namval.Length != 2) {
						Output.LogLine("Parsing encountered exception ");
						throw new Exception ("bad format");
					}
					cursecn[namval[0]] = namval[1];
				} else {
					if (sections[secn] != null) {
						Output.LogLine("Duplicate section name " + secn);
					}
					cursecn = getsection(secn);
				}
			}
			conf_file.Close();
		}

        public string Print()
        {
            StringBuilder strb = new StringBuilder();


            if (sections.ContainsKey(""))
            {
                Hashtable map = sections[""] as Hashtable;
                foreach (string key in map.Keys)
                {
                    strb.Append(key).Append("=").Append(map[key] as string).AppendLine();
                }
                strb.AppendLine();
            }

            foreach (string sectionname in sections.Keys)
            {
                if (sectionname == "") continue;

                strb.Append("[").Append(sectionname).Append("]").AppendLine();

                Hashtable map = sections[sectionname] as Hashtable;
                Debug.Assert(map != null);
                foreach (string key in map.Keys)
                {
                    strb.Append(key).Append("=").Append(map[key] as string).AppendLine();
                }
                strb.AppendLine();
            }

            return strb.ToString();
        }
    }

    public class ConfigCommand : ProofCommand
    {
        string section;
        string key;
        string value;

        public ConfigCommand(string s, string k, string v)
            : base("config")
        {
            this.section = s;
            this.key = k;
            this.value = v;

            desc = "config " + section + " " + key + " " + value;
        }

        public static string Usage()
        {
            return "config [sectionName] keyName value";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("config"))
            {
                string s1 = parser.NextAsString();
                string s2 = parser.NextAsString();
                if (parser.HasNext())
                {
                    string s3 = parser.NextAsString();
                    return new ConfigCommand(s1, s2, s3);
                }
                else
                {
                    return new ConfigCommand("", s1, s2);
                }
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {
            proofState.config.Set(section, key, value);

            Output.AddLine("Option is set: " + section + "." + key + "=" + value);

            return false;
        }

    } // end class ConfigCommand


} // end namespace QED