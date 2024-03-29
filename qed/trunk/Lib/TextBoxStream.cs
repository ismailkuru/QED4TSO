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
using System.Drawing;
using System.ComponentModel;
using System.Windows.Forms;
using System.Text;
  

	/// <summary>
	/// TextBoxStream is used to add outputs of a externally executed program into a text-box.
	/// The output stream of the program is redirected to a TextBoxStream instance.
	/// </summary>
	public class TextBoxStream : TextWriter {

		protected TextBoxBase txt_box;

		public TextBoxStream(TextBoxBase tb) {
			this.txt_box = tb;
			this.txt_box.Clear();
		}

        delegate void AppendTextCallback(string text);

		public override void Write(char[] buffer, int index, int count) {
			string line = new string(buffer, index, count);
            line = Util.ToGuiString(line);
            if(line.StartsWith("evil input from z3:")) return;

            AppendText(line);
		}

        void AppendText(string text)
        {
            if (txt_box.InvokeRequired)
            {
                // It's on a different thread, so use Invoke.
                AppendTextCallback d = new AppendTextCallback(AppendText);
                txt_box.Parent.Invoke(d, new object[] { text } );
            }
            else
            {
                // It's on the same thread, no need for Invoke
                txt_box.AppendText(text);
            }
        }

		public override Encoding Encoding {
			get {
				return Encoding.Unicode;
			}
		}
	}

} // end namespace QED