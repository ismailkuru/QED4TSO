using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace QED
{
    public partial class ViewBox : Form
    {
        public ViewBox()
        {
            InitializeComponent();
        }

        static public void Show(IWin32Window owner, string title, string info, List<myGraph> glist)
        {
            ViewBox vbox = new ViewBox();
            vbox.Text = title;
            vbox.txt_Info.Text = info;

            vbox.tab_Panel.Controls.Clear();

            vbox.SuspendLayout();
            foreach (myGraph g in glist)
            {
                TabPage tp = new TabPage(g.Name);

                //create a viewer object
                Microsoft.Glee.GraphViewerGdi.GViewer viewer = new Microsoft.Glee.GraphViewerGdi.GViewer();
                viewer.Graph = GraphTranslator.Translate(g);
                //associate the viewer with the form
                viewer.Dock = System.Windows.Forms.DockStyle.Fill;
                tp.Controls.Add(viewer);

                vbox.tab_Panel.Controls.Add(tp);
            }
            vbox.ResumeLayout();

            vbox.Show(owner);
        }
    }
}