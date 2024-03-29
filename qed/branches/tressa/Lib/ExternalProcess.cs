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
	/// A static class that provides methods to run batch and executable files.
	/// </summary>
	public class ExternalProcess
	{
		/// <summary>
		/// This points to the root directory from which the relative paths will be handled.
		/// </summary>
		public static string HOME = Environment.CurrentDirectory;

		/// <summary>
		/// This must be called before using any other static methods of BatchFiles.
		/// </summary>
		/// <param name="home">The root directory that will sit in HOME variable.</param>
		public static void Init(string home) {
			HOME = (string)home.Clone();
		}

		protected static Process current_process = null;

		public static void KillCurrentProcess() {
			if(current_process != null) {
				current_process.Kill();
				current_process = null;
			}
		}

		public static int Run(string file_name) {
			Process batch_file = new Process();
			current_process = batch_file;
			batch_file.EnableRaisingEvents=false;
			batch_file.StartInfo.FileName=file_name;
			batch_file.Start();
			batch_file.WaitForExit();
			return batch_file.ExitCode;
		}

		public static int Run(string file_name, TextWriter stream_out) {
			StreamReader reader = null;
			char[] buffer = new char[1024];
			int count;
			Process batch_file = Start(file_name, out reader);
			current_process = batch_file;
			while((count = reader.Read(buffer, 0, buffer.Length)) > 0) {
				stream_out.Write(buffer, 0, count);
			}
			int ret = batch_file.ExitCode;
			batch_file.Close();
			return ret;
		}

		public static int Run(string file_name, string arguments, TextWriter stream_out) {
			StreamReader reader = null;
			char[] buffer = new char[1024];
			int count;
			Process batch_file = Start(file_name, arguments, out reader);
			current_process = batch_file;
			while((count = reader.Read(buffer, 0, buffer.Length)) > 0) {
				stream_out.Write(buffer, 0, count);
			}
			int ret = batch_file.ExitCode;
			batch_file.Close();
			return ret;
		}
		
		public static int Run(string file_name, string arguments, string inputs, TextWriter stream_out) {
			StreamReader reader = null;
			StreamWriter writer = null;
			char[] buffer = new char[1024];
			int count;
			Process batch_file = Start(file_name, arguments, out reader, out writer);
			current_process = batch_file;
			
			writer.WriteLine(inputs);
			
			if((count = reader.Read(buffer, 0, buffer.Length)) > 0) {
				stream_out.Write(buffer, 0, count);
			}
			
			Kill(batch_file);
			int ret = 0; // batch_file.ExitCode;
			return ret;
		}

		public static Process Start(string file_name, out StreamReader out_stream) {
			Process batch_file = new Process();
			current_process = batch_file;
			batch_file.EnableRaisingEvents=false;
			batch_file.StartInfo.FileName=file_name;
			batch_file.StartInfo.RedirectStandardOutput=true;
			batch_file.StartInfo.UseShellExecute=false;
			batch_file.StartInfo.CreateNoWindow=true;
			batch_file.Start();
			out_stream=batch_file.StandardOutput;
			return batch_file;
		}

		public static Process Start(string file_name, string arguments, out StreamReader out_stream) {
			Process batch_file = new Process();
			current_process = batch_file;
			batch_file.EnableRaisingEvents=false;
			batch_file.StartInfo.FileName=file_name;
			batch_file.StartInfo.Arguments=arguments;
			batch_file.StartInfo.RedirectStandardOutput=true;
			batch_file.StartInfo.UseShellExecute=false;
			batch_file.StartInfo.CreateNoWindow=true;
			batch_file.Start();
			out_stream=batch_file.StandardOutput;
			return batch_file;
		}
		
		public static Process Start(string file_name, string arguments, out StreamReader out_stream, out StreamWriter in_stream) {
			Process batch_file = new Process();
			current_process = batch_file;
			batch_file.EnableRaisingEvents=false;
			batch_file.StartInfo.FileName=file_name;
			batch_file.StartInfo.Arguments=arguments;
			batch_file.StartInfo.RedirectStandardOutput=true;
			batch_file.StartInfo.RedirectStandardInput=true;
			batch_file.StartInfo.UseShellExecute=false;
			batch_file.StartInfo.CreateNoWindow=true;
			batch_file.Start();
			out_stream=batch_file.StandardOutput;
			in_stream=batch_file.StandardInput;
			return batch_file;
		}

		public static int Run(string file_name, string arguments) {
			Process batch_file = new Process();
			current_process = batch_file;
			batch_file.EnableRaisingEvents=false;
			batch_file.StartInfo.FileName=file_name;
			batch_file.StartInfo.Arguments=arguments;
			batch_file.Start();
			batch_file.WaitForExit();
			return batch_file.ExitCode;
		}
		
		public static void Kill(Process process)
		{
			if (process != null) 
			{
			  if (!process.HasExited)
			  {
				try { process.Kill(); process.WaitForExit(); } catch (InvalidOperationException) { /* already exited */ }
			  }
			  process.Close();			  
			}
		}
		
	}

} // end namespace QED