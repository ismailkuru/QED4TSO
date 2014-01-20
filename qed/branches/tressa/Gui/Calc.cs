using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using Microsoft.Boogie;
using BoogiePL;


namespace QED
{
    public partial class Calc : Form
    {
        ProofState proofState;

        public Calc(ProofState pstate)
        {
            this.proofState = pstate;
            InitializeComponent();
        }

        private void btn_parse_Click(object sender, EventArgs e)
        {
            string strformula = txt_formula.Text;
            int idx = strformula.IndexOf(':');
            string procname = strformula.Substring(0, idx).Trim();
            strformula = strformula.Substring(idx + 1).Trim();

            Expr formula = Logic.ParseFormula(proofState, procname, strformula, false);

            txt_parsed.Text = Output.ToString(formula);
        }

        private void Calc_Load(object sender, EventArgs e)
        {
            txt_help.Text =
@"Formula format:  procname : formula
procname: A procedure name
formula: the formula

Formula format:
Use atomic_block_name() to refer to its transition predicate.
Use Inv() to refer to the invariant.
Use InvPrime() to refer to the invariant primed.";
        }

        private void btn_check_Click(object sender, EventArgs e)
        {
            string strformula = txt_formula.Text;
            int idx = strformula.IndexOf(':');
            string procname = strformula.Substring(0, idx).Trim();
            strformula = strformula.Substring(idx + 1).Trim();

            Expr formula = Logic.ParseFormula(proofState, procname, strformula, false);

            bool valid = Prover.GetInstance().CheckValid(formula);
            
            MessageBox.Show("The formula for " + procname + " is " + (valid ? "VALID" : "INVALID") + "\n" + strformula, "Check Valid", MessageBoxButtons.OK, MessageBoxIcon.Information);
        }

        private void btn_close_Click(object sender, EventArgs e)
        {
            this.Close();
        }

    }
}
