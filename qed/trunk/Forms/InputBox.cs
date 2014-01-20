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

using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace QED
{
    public partial class InputBox : System.Windows.Forms.Form
    {
        public string title;
        public string message;
        public string defstr;
        public string strMessage;

        public InputBox(string title, string message, string defstr)
        {
            this.title = title;
            this.message = message;
            this.defstr = defstr;

            InitializeComponent();

            this.SuspendLayout();
            this.Text = this.title;
            this.label1.Text = this.message;
            this.txtMessage.Text = this.defstr;
            this.ResumeLayout(false);
            this.PerformLayout();
        }
        
        public string Message
        {
            get { return strMessage; }
            set
            {
                strMessage = value;
                txtMessage.Text = strMessage;
            }
        }
        
        public static string Show(string title, string message, string defstr)
        {
            InputBox box = new InputBox(title, message, defstr);
            box.ShowDialog();
            return box.strMessage;
        }

        public static string Show(string title, string message)
        {
            InputBox box = new InputBox(title, message, "");
            box.ShowDialog();
            return box.strMessage;
        }
    }
}