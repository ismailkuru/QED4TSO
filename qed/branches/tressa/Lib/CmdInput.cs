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
using Type = Microsoft.Boogie.Type;
using System.Reflection;

    public class CmdFactory
    {
        static public List<string> AvailableCommands; // usage of the commands
        static public List<System.Type> CommandTypes;
        static public string[] CommandTypeNames = new string[] {
                                                    "QED.RefineMutexCommand",
                                                    "QED.RefineStableCommand",
                                                    "QED.RefineReadWriteCommand",
                                                    "QED.RefinePointerCommand",
                                                    "QED.ReduceCommand",
                                                    "QED.ReduceLoopCommand",
                                                    "QED.MoverCommand",
                                                    "QED.FixMoverCommand",
                                                    "QED.MergeCommand",
                                                    "QED.AssertCommand",
                                                    "QED.RelaxCommand",
                                                    "QED.AuxIntroCommand",
                                                    "QED.ConfigCommand",
                                                    "QED.AnnotateCommand",
                                                    "QED.InstrumentEntryCommand",
                                                    "QED.InstrumentExitCommand",
                                                    "QED.InvariantCommand",
                                                    "QED.LocalInvariantCommand",
                                                    "QED.TransInvCommand",
                                                    "QED.CheckCommand",
                                                    "QED.HoistCommand",
                                                    "QED.PurifyCommand",
                                                    "QED.EvalCommand",
                                                    "QED.AbstractCommand",
                                                    "QED.SimulateCommand",
                                                    "QED.PreCommand",
                                                    "QED.PostCommand",
                                                    "QED.MTypeCommand",
                                                    "QED.LoopInvCommand",
                                                    "QED.InlineCommand",
                                                    "QED.ReduceLoop2Command",
                                                    "QED.ProverCommand",
                                                    "QED.PeelOutCommand",
                                                    "QED.SkipCommand",
                                                    "QED.ReduceSkipCommand",
                                                    "QED.SplitCommand",
                                                    "QED.AssumeCommand",
                                                    "QED.SaveCommand",
                                                    "QED.LoadCommand",
                                                    "QED.NullCheckCommand",
                                                    "QED.RelabelCommand",
                                                    "QED.HideCommand"
                                                    //"QED.RefineMutex2Command"
                                                    //for tressa
                                                    ,"QED.CheckTressa"
                                                    };


        static CmdFactory()
        {
            Debug.Assert(CommandTypeNames != null);

            // initialize AllCommands
            CommandTypes = new List<System.Type>();
            AvailableCommands = new List<string>();

            foreach (string typeName in CommandTypeNames)
            {
                System.Type type = System.Type.GetType(typeName);
                CommandTypes.Add(type);
                AvailableCommands.Add(Usage(type));
            }
        }

        private static string Usage(System.Type c)
        {
            MethodInfo m = null;

            try
            {
                m = c.GetMethod("Usage");
            }
            catch
            {
                Debug.Assert(false);
            }

            object o = m.Invoke(null, new object[] {});
            Debug.Assert(o != null);
            return o as string;
        }

        static public ProofCommand Create(string cmdline)
        {
            ProofCommand cmd = null;

            CmdParser parser = new CmdParser(cmdline);

            foreach (System.Type c in CommandTypes)
            {
                MethodInfo m = null;

                try
                {
                    m = c.GetMethod("Parse");
                }
                catch
                {
                    continue;
                }
                if (m == null)
                {
                    continue;
                }

                object o = null;
                try
                {
                    BoogiePL.Errors.count = 0;
                    o = m.Invoke(null, new object[] { parser });
                }
                catch(Exception e)
                {
                    Output.AddError("Error in parsing the command: " + cmdline);
                    Output.Add(e);
                    o = null;
                    BoogiePL.Errors.count = 0;
                }

                if (o != null)
                {
                    Debug.Assert(o.GetType().Equals(c));
                    cmd = o as ProofCommand;
                    break;
                }
                else
                {
                    // reset parser
                    parser.Reset();
                }
            }

            return cmd;
        }


//        static public ProofCommand Create2(string cmdline)
//        {
//            ProofCommand cmd = null;

//            CmdParser parser = new CmdParser(cmdline);

//            try
//            {
//                switch (parser.NextAsString())
//                {

//                    case "mutex":
//                        {
//                            string aux = parser.NextAsString();
//                            Expr pred = parser.RestAsExpr();
//                            cmd = new RefineMutexCommand(pred, aux);
//                        }
//                        break;

//                    case "stable":
//                        {
//                            string aux = parser.NextAsString();
//                            Expr pred = parser.RestAsExpr();
//                            cmd = new RefineStableCommand(pred, aux);
//                        }
//                        break;

//                    //case "progress":
//                    //    {
//                    //        string aux = parser.NextAsString();
//                    //        List<Expr> predlist = parser.RestAsExprList('#');
//                    //        cmd = new RefineProgressCommand(predlist, aux);
//                    //    }
//                    //    break;

//                    case "rwlock":
//                        {
//                            string aux = parser.NextAsString();
//                            List<Expr> preds = parser.RestAsExprList('#');
//                            cmd = new RefineReadWriteCommand(preds[0], preds[1], aux);
//                        }
//                        break;

//                    case "mutexptr":
//                        {
//                            string aux = parser.NextAsString();
//                            Expr pred = parser.RestAsExpr();
//                            cmd = new RefinePointerCommand((pred as ForallExpr), aux);
//                        }
//                        break;

//#if false
//                case "sync":
//                    {
//                        string kind = parser.NextAsString();
//                        if (kind.Equals("mutex"))
//                        {
//                            string aux = parser.NextAsString();
//                            string[] vars = parser.NextAsStringArray(',');
//                            Expr pred = parser.RestAsExpr();
//                            cmd = new SyncMutexCommand(pred, aux, vars);
//                        }
//                        else
//                        {
//                            cmd = null;
//                        }
//                    }
//                    break;
//#endif

//#if false
//                case "addproph":
//                    {
//                        string varname = parser.NextAsString();
//                        cmd = new ProphecyIntroCommand(varname);
//                    }
//                    break;

//                case "trap":
//                    {
//                        string block = parser.NextAsString();
//                        Expr pred = parser.RestAsExpr();
//                        cmd = new TrapPredCommand(block, pred);
//                    }
//                    break;

//                case "conspar":
//                    {
//                        string startblock = parser.NextAsString();
//                        string endblock = parser.NextAsString();
//                        string varname = parser.NextAsString();
//                        Expr pred = parser.RestAsExpr();
//                        cmd = new ConsParCommand(startblock, endblock, varname, pred);
//                    }
//                    break;
//#endif

//                    case "reduce":
//                        {
//                            string kind = parser.NextAsString();
//                            if (kind.Equals("all"))
//                            {
//                                //cmd = new ReduceCommand();
//                            }
//                            else
//                                if (kind.Equals("proc"))
//                                {
//                                    string procname = parser.NextAsString();
//                                    //cmd = new ReduceProcCommand(procname);
//                                }
//                                else
//                                    if (kind.Equals("loop"))
//                                    {
//                                        //string blocklabel = parser.NextAsString();
//                                        //List<Expr> gt = parser.NextAsExprList('#');
//                                        //if(gt.Count == 2) {
//                                        //    cmd = new ReduceLoopCommand(blocklabel, gt[0], gt[1]);
//                                        //}

//                                    }
//                                    else
//                                    {
//                                        cmd = null;
//                                    }
//                        }
//                        break;

//                    case "mover":
//                        {
//                            string label = parser.NextAsString();
//                            //cmd = new MoverCommand(label);
//                        }
//                        break;

//                    case "fixmover":
//                        {
//                            bool r = false;
//                            bool l = false;
//                            string rl = parser.NextAsString();
//                            r = rl.IndexOf("r") >= 0;
//                            l = rl.IndexOf("l") >= 0;

//                            string label = parser.NextAsString();

//                            cmd = new FixMoverCommand(r, l, label);
//                        }
//                        break;

//                    case "merge":
//                        {
//                           // cmd = new MergeCommand(parser.NextStartsWith("*"));
//                        }
//                        break;

//                    case "assert":
//                        {
//                            string blockname = parser.NextAsString();
//                            Expr assertion = parser.RestAsExpr();
//                            //cmd = new AssertCommand(blockname, assertion);
//                        }
//                        break;

//                    case "relax":
//                        {
//                            string blockname = parser.NextAsString();
//                            cmd = new RelaxCommand(blockname);
//                        }
//                        break;

//                    /*******************************************************************************************/
//                    case "aux":
//                        {
//                            string auxname = parser.NextAsString();
//                            string auxtype = parser.NextAsString();
//                            //cmd = new AuxIntroCommand(auxname, auxtype);
//                        }
//                        break;
//#if false
//                case "hideaux":
//                    {
//                        string auxname = parser.NextAsString();
//                        cmd = new CleanupCommand(auxname);
//                    }
//                    break;
//#endif
//                    /*******************************************************************************************/

//                    case "config":
//                        {

//                            string s1 = parser.NextAsString();
//                            string s2 = parser.NextAsString();
//                            if (parser.HasNext())
//                            {
//                                string s3 = parser.NextAsString();
//                                cmd = new ConfigCommand(s1, s2, s3);
//                            }
//                            else
//                            {
//                                cmd = new ConfigCommand("", s1, s2);
//                            }
//                        }
//                        break;


//                    case "annotate":
//                        {
//                            string label = parser.NextAsString();
//                            Expr expr = parser.RestAsExpr();
//                           // cmd = new AnnotateCommand(label, expr);
//                        }
//                        break;

//                    case "instrument":
//                        {
//                            string kind = parser.NextAsString();
//                            if (kind.Equals("entry"))
//                            {
//                                List<Expr> exprlist = parser.RestAsExprList('#');
//                                Expr rely = exprlist[0];
//                                Expr guar = exprlist[1];
//                                cmd = new InstrumentEntryCommand(rely, guar, exprlist.GetRange(2, exprlist.Count));
//                            }
//                            else
//                                if (kind.Equals("exit"))
//                                {
//                                    List<Expr> exprlist = parser.RestAsExprList('#');
//                                    Expr rely = exprlist[0];
//                                    Expr guar = exprlist[1];
//                                    cmd = new InstrumentExitCommand(rely, guar, exprlist.GetRange(2, exprlist.Count));
//                                }
//                                else
//                                {
//                                    cmd = null;
//                                }
//                        }
//                        break;
//#if false		
//                case "speculate": 
//                    {
//                        List<Expr> exprlist = parser.RestAsExprList('#');
//                            Expr rely = exprlist[0];
//                            Expr guar = exprlist[1];
//                        cmd = new SpeculateCommand(rely, guar, exprlist.GetRange(2, exprlist.Count)); 
//                    }
//                    break;
//#endif
//                    case "annot":
//                        {
//                            string kind = parser.NextAsString();
//                            if (kind.Equals("pre"))
//                            {
//                                string label = parser.NextAsString();
//                                Expr formula = parser.RestAsExpr();
//                                cmd = new PreCommand(label, formula);
//                            }
//                            else
//                                if (kind.Equals("post"))
//                                {
//                                    string label = parser.NextAsString();
//                                    Expr formula = parser.RestAsExpr();
//                                    cmd = new PostCommand(label, formula);
//                                }
//                                else if (kind.Equals("inv"))
//                                {
//                                    //string label = parser.NextAsString();
//                                    //Expr formula = parser.RestAsExpr();
//                                    //cmd = new LoopInvCommand(label, formula);
//                                }
//                                else if (kind.Equals("mover"))
//                                {
//                                    string label = parser.NextAsString();
//                                    MoverType mtype = parser.NextAsMoverType();
//                                    cmd = new MTypeCommand(label, mtype);

//                                }
//                                else
//                                {
//                                    cmd = null;
//                                }
//                        }
//                        break;

//                    case "invariant":
//                        {
//                            Expr inv = parser.RestAsExpr();
//                            cmd = new InvariantCommand(inv);
//                        }
//                        break;

//                    case "localinv":
//                        {
//                            string procname = parser.NextAsString();
//                            Expr linv = parser.RestAsExpr();
//                            cmd = new LocalInvariantCommand(linv, procname);
//                        }
//                        break;

//                    case "transinv":
//                        {
//                            Expr tinv = parser.RestAsExpr();
//                            cmd = new TransInvCommand(tinv);
//                        }
//                        break;
//#if false		
//                case "reach": 
//                    {
//                        string procname = parser.NextAsString();
//                        cmd = new ReachCommand(procname);
//                    }
//                    break;
//#endif

//                    case "check":
//                        {
//                            string procname = parser.NextAsString();
//                            //cmd = new CheckCommand(procname);
//                        }
//                        break;

//                    case "hoist":
//                        {
//                            string blocklabel = parser.NextAsString();
//                            string afterbefore = parser.NextAsString();
//                            cmd = new HoistCommand(blocklabel, afterbefore);
//                        }
//                        break;

//#if false
//                case "clone": 
//                    {
//                        string blocklabel = parser.NextAsString();
//                        string branchlabel = parser.NextAsString();
//                        cmd = new CloneCommand(blocklabel, branchlabel);
//                    }
//                    break;
//#endif

//                    case "purify":
//                        {
//                            string procname;
//                            if (parser.NextStartsWith("all", out procname))
//                            {
//                                cmd = new PurifyCommand();
//                            }
//                            else
//                            {
//                                Debug.Assert(procname != null);
//                                cmd = new PurifyCommand(/*procname*/);
//                            }
//                        }
//                        break;

//#if false
//                case "thrlocal": 
//                    {
//                        string procname = parser.NextAsString();
//                        string varname = parser.NextAsString();
//                        cmd = new ThreadLocalCommand(procname, varname);
//                    }
//                    break;
//#endif
//                    case "eval":
//                        {
//                            string classname = parser.NextAsString();
//                            cmd = new EvalCommand(classname);
//                        }
//                        break;

//                    case "abstract":
//                        {
//                            bool read;

//                            string rw = parser.NextAsString();
//                            if (rw == "read")
//                            {
//                                read = true;
//                            }
//                            else if (rw == "write")
//                            {
//                                read = false;
//                            }
//                            else
//                            {
//                                cmd = null;
//                                break;
//                            }

//                            string v = parser.NextAsString();
//                            string b = parser.NextAsString();

//                            //cmd = new AbstractCommand(v, b, read);
//                        }
//                        break;

//                    case "simulate":
//                        {
//                            string blockname = parser.NextAsString();
//                            string code = parser.RestAsString();
//                            cmd = new SimulateCommand(blockname, code);
//                        }
//                        break;
//#if false
//                case "abstractpath":
//                    {
//                        bool rr = false;
//                        bool ww = false;

//                        string rw = parser.NextAsString();
//                        rr = rw.IndexOf("r") >= 0;
//                        ww = rw.IndexOf("w") >= 0;

//                        string v = parser.NextAsString();
//                        string b = parser.NextAsString();

//                        cmd = new AbstractPathCommand(v, b, rr, ww);
//                    }
//                    break;
//#endif
//                    default:
//                        cmd = null;
//                        break;
//                }

//            }
//            catch
//            {
//                // if any parsing error, just return null
//                cmd = null;
//            }

//            return cmd;
//        }

        static public Expr ParseExpr(string exprstr)
        {
            return Qoogie.ParseExpr(exprstr);
        }

    } // end class CmdFactory


public class CmdParser : IEnumerable<string>
{
	string line;
    string inputLine;

    public CmdParser(string input_line) {
        this.inputLine = input_line.Trim();
        Reset();
	}

    public void Reset()
    {
        this.line = Trim(this.inputLine);
    }

    public string Trim(string str)
    {
        str = str.Trim();
        while (str.StartsWith("\n") || str.StartsWith("\r"))
        {
            str = str.Substring(1);
        }
        while (str.EndsWith("\n") || str.EndsWith("\r"))
        {
            str = str.Substring(0, str.Length-1);
        }
        str = str.Trim();
        return str;
    }

	public bool HasNext() {
		return line.Length > 0;
	}
	
	public bool NextEquals(string s) {
		string str = NextAsString();
		if(str == null) return false;
		
		return str.Equals(s);
	}
	
	public bool NextEquals(string s, out string outstr) {
		string str = NextAsString();
		if(str == null) {
			outstr = null;
			return false;
		}
		
		outstr = str;
		return str.Equals(s);
	}
	
	public bool NextStartsWith(string s) {
		string str = NextAsString();
		if(str == null) return false;
		
		return str.StartsWith(s);
	}
	
	public bool NextStartsWith(string s, out string outstr) {
		string str = NextAsString();
		if(str == null) {
			outstr = null;
			return false;
		}
		
		outstr = str;
		return str.StartsWith(s);
	}
	
	public string NextAsString() {
		if(HasNext()) {
			string str;
			int i = line.IndexOf(' ');
			if(i == -1) {
				str = line;
				line = "";
			} else {
				str = Trim(line.Substring(0, i));
				line = Trim(line.Substring(i+1));
			}
			return str;
		} else {
			return null;
		}
	}
	
	public string RestAsString() {
		if(HasNext()) {
			string str = line;
			line = "";
			return str;
		} else {
			return null;
		}
	}
	
	public string[] NextAsStringArray(char separator) {
		string str = NextAsString();
		if(str == null) return null;
			
		return str.Split(new char[] {separator}, StringSplitOptions.RemoveEmptyEntries);
	} 
	
	public string[] RestAsStringArray(char separator) {
		string str = RestAsString();
		if(str == null) return null;
			
		return str.Split(new char[] {separator}, StringSplitOptions.RemoveEmptyEntries);
	} 
	
	public List<string> NextAsStringList(char separator) {
		string[] strs = NextAsStringArray(separator);
		if(strs == null) return null;
			
		List<string> strlist = new List<string>();
		for(int i = 0, n = strs.Length; i < n; ++i) {
			strlist.Add(strs[i]);
		}
		return strlist;
	} 
	
	public List<string> RestAsStringList(char separator) {
		string[] strs = RestAsStringArray(separator);
		if(strs == null) return null;
			
		List<string> strlist = new List<string>();
		for(int i = 0, n = strs.Length; i < n; ++i) {
			strlist.Add(strs[i]);
		}
		return strlist;
	} 
	
	public Set<string> NextAsStringSet(char separator) {
		string[] strs = NextAsStringArray(separator);
		if(strs == null) return null;
			
		Set<string> strset = new Set<string>();
		for(int i = 0, n = strs.Length; i < n; ++i) {
			strset.Add(strs[i]);
		}
		return strset;
	} 
	
	public bool NextAsBool(bool def) {
		string str = NextAsString();
		if(str == null) return def;
			
		return bool.Parse(str);
	}
	
	public int NextAsInt(int def) {
		string str = NextAsString();
		if(str == null) return def;
			
		return int.Parse(str);
	}
	
	public Expr NextAsExpr() {
		string str = NextAsString();
		if(str == null) return null;
			
		return ParseExpr(str);
	} 
	
	public Expr RestAsExpr() {
		string str = RestAsString();
		if(str == null) return null;
			
		return ParseExpr(str);
	} 
	
	public List<Expr> NextAsExprList(char separator) {
		string[] strs = NextAsStringArray(separator);
		if(strs == null) return null;
			
		List<Expr> exprs = new List<Expr>();
		for(int i = 0, n = strs.Length; i < n; ++i) {
			exprs.Add(ParseExpr(strs[i]));
		}
		return exprs;
	}
	
	public List<Expr> RestAsExprList(char separator) {
		string[] strs = RestAsStringArray(separator);
		if(strs == null) return null;
			
		List<Expr> exprs = new List<Expr>();
		for(int i = 0, n = strs.Length; i < n; ++i) {
			exprs.Add(ParseExpr(strs[i]));
		}
		return exprs;
	}
	
	static public Expr ParseExpr(string exprstr) {
		return Qoogie.ParseExpr(exprstr);
	}
	
	#region IEnumerable<string!> Members

	public IEnumerator<string> GetEnumerator()
    {
        yield return NextAsString();
    }
    
    IEnumerator IEnumerable.GetEnumerator()
    {
        yield return NextAsString();
    }

    #endregion


    public MoverType NextAsMoverType()
    {
        return MoverType.Parse(NextAsString());
    }
} // end class CmdInput


} // end namespace QED