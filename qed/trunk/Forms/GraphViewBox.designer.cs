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

namespace QED
{
    partial class GraphViewBox
    {
        //private System.ComponentModel.Container components;

        //protected override void Dispose(bool disposing)
        //{
        //    if (disposing)
        //    {
        //        if (components != null)
        //        {
        //            components.Dispose();
        //        }
        //    }
        //    base.Dispose(disposing);
        //}


        #region Windows Form Designer generated code
        private void InitializeComponent()
        {
            this.viewer = new Microsoft.Glee.GraphViewerGdi.GViewer(); 
            this.SuspendLayout();
            // 
            // graph viewer
            // 
            viewer.Graph = GraphTranslator.Translate(this.graph);
            //associate the viewer with the form
            viewer.Dock = System.Windows.Forms.DockStyle.Fill;
            //viewer.SelectionChanged += new System.EventHandler(this.graph_Viewer_SelectionChanged);
            //viewer.Click += new System.EventHandler(this.graph_Viewer_SelectionChanged);

            // 
            // GraphViewBox
            // 
            this.AutoScaleBaseSize = new System.Drawing.Size(5, 13);
            this.ClientSize = new System.Drawing.Size(672, 531);
            this.Controls.Add(this.viewer);
            this.MaximizeBox = true;
            this.MinimizeBox = true;
            this.Name = "GraphViewBox";
            this.Text = this.title;
            this.StartPosition = System.Windows.Forms.FormStartPosition.CenterParent;
            this.ResumeLayout(false);
            this.PerformLayout();
        }
        #endregion

        private Microsoft.Glee.GraphViewerGdi.GViewer viewer;
        
    }
}