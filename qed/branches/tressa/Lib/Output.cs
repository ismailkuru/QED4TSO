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
using Type = Microsoft.Boogie.Type;
using System.Diagnostics;
  
	/// <summary>
	/// The class used for debugging purposes...
	/// </summary>
	public class Output
	{
		public static void ApplyConfiguration(Configuration config) {
			DebugEnabled = config.GetBool("Output", "DebugEnabled", true);
			AssertEnabled = config.GetBool("Output", "AssertEnabled", true);
			output_to_file = config.GetBool("Output", "OutputToFile", false);
			outputFileName = config.GetStr("Output", "OutputFileName", "qet_debug.txt");

            if (File.Exists(outputFileName))
            {
                File.Delete(outputFileName);
            }
		}

		/// <summary>
		/// Name of the output file.
		/// All outputs written to Debug are also written to the file.
		/// </summary>
		public static string outputFileName = "qet_debug.txt";
		/// <summary>
		/// The text writer for the debug comments to be added.
		/// !!! All the prints whether regular or error are directed to this writer object
		/// </summary>
        protected static TextWriter output; // default is Console

        protected static TokenTextWriter writer; // default is Console
		
		/// <summary>
		/// Is debugging enabled?
		/// !!! This controls all the regular outputs.
		/// </summary>
		protected static bool debugEnabled = true;
		/// <summary>
		/// Is assertions enabled?
		/// !!! MUST be enabled.
		/// </summary>
		protected static bool assertEnabled = true;

		public static bool output_to_file = false;

        // set Target first, before starting to use this class
		public static TextWriter Target {
			get {
				return output;
			}
			set{
				Stream s = File.Create(outputFileName);
				s.Close();
				output = value;
				writer = new TokenTextWriter(output);
			}
		}

		public static bool DebugEnabled {
			get {
				return debugEnabled;
			}
			set{
				debugEnabled = value;
			}
		}

		public static bool AssertEnabled{
			get {
				return assertEnabled;
			}
			set{
				assertEnabled = value;
			}
		}
		
		public static void Add(string msg){
			add(msg);
		}
		
		public static void Add(bool enable, string msg) {
			if(enable) {
				Add(msg);
			}
		}
		
		public static void AddLine(){
			AddLine("");
		}
		
		/// <summary>
		/// Add a single comment line.
		/// </summary>
		/// <param name="msg">Message to be displayed</param>
		public static void AddLine(string msg){
			Add(msg + "\n");
		}

		/// <summary>
		/// Ass a single comment line
		/// Controled by a boolean variable, defined in other classes that prints the comment
		/// </summary>
		/// <param name="enable">Enables/Disables the print operation</param>
		/// <param name="msg">Message to be displayed</param>
		public static void AddLine(bool enable, string msg) {
			if(enable) {
				AddLine(msg);
			}
		}
		
		public static void Log(string msg){
			log(msg);
		}
		
		public static void LogLine(string msg){
			log(msg + "\n");
		}
		
		public static void LogLine(){
			log("\n");
		}

		/// <summary>
		/// Add an error comment line.
		/// </summary>
		/// <param name="msg">Message describing the error.</param>
		public static void AddError(string msg){
			string m = "ERROR: " + msg + "!!!";
			AddLine(m);
		}


		/// <summary>
		/// Ass an error line
		/// Controled by a boolean variable, defined in other classes that prints the comment
		/// </summary>
		/// <param name="enable">Enables/Disables the print operation</param>
		/// <param name="msg">Message describing the error</param>
		
		public static void AddError(bool enable, string msg){
			if(enable){
				AddError(msg);
			}
		}

		/// <summary>
		/// Add a fatal error comment line, and exists the program.
		/// </summary>
		/// <param name="msg">Message describing the fatal error.</param>
		public static void AddFatalError(string msg){
			string m = "FATAL ERROR: " + msg + "!!!";
			AddLine(m);
			AddLine(Environment.StackTrace);
			Environment.Exit(1);
		}

		/// <summary>
		/// Adds an assertion to in the code
		/// </summary>
		/// <param name="assertion">Assertion to be checked</param>
		public static void Assert(bool assertion) {
			if (assertEnabled) {
				throw new Exception("Assertion failed");
			}	
		}

		/// <summary>
		/// Waits for the user to press any key
		/// </summary>
		public static void WaitForUser() {
			AddLine("Press enter any key...");
			Console.Read(); // !!! associated with the console
		}
		
		/// <summary>
		/// The primitive message adder, called by all the methods in this class
		/// </summary>
		/// <param name="msg">Message to be printed</param>
		protected static void add(string msg){
			if(debugEnabled) {
				// print to the standart output stream
				output.Write(msg);
                // add the text to log as well
                log(msg);
			}
		}
		
		protected static void log(string msg){
			if(debugEnabled) {
                if(output_to_file) {
					// print to the output file
					using(StreamWriter sw = File.AppendText(outputFileName)) {
						sw.Write(msg);
					}
				}
			}
		}
		
		public static void PrintExpr(Expr expr) {
			expr.Emit(writer);
		}
		
		public static string ToString(Expr expr) {
			StringWriter strw = new StringWriter();
			TokenTextWriter tkw = new TokenTextWriter(strw);
			expr.Emit(tkw);
            return TrimLastLine(strw.ToString());
		}
		
		public static string ToString(Type type) {
			StringWriter strw = new StringWriter();
			TokenTextWriter tkw = new TokenTextWriter(strw);
			type.Emit(tkw);
			return TrimLastLine(strw.ToString());
		}
		
		public static string ToString(Cmd cmd) {
			StringWriter strw = new StringWriter();
			TokenTextWriter tkw = new TokenTextWriter(strw);
			cmd.Emit(tkw,0);
            return TrimLastLine(strw.ToString());
		}

        public static string TrimLastLine(string str)
        {
            int ll = str.LastIndexOf("\r\n");
            return ll > 0 ? str.Substring(0, ll) : str;
        }

		public static void PrintBplFile (string filename, Program program) {
		#if false
				//writer.WriteLine("// " + CommandLineOptions.Version);
				//writer.WriteLine("// " + CommandLineOptions.Clo.Environment);
				writer.WriteLine();
				program.Emit(writer);
		#endif
		}

        public static void Add(Exception e)
        {
            AddLine(e.Message);
            AddLine(e.StackTrace);
        }
    }

} // end namespace QED

