namespace QED
{
    partial class Calc
    {
        /// <summary>
        /// Required designer variable.
        /// </summary>
        private System.ComponentModel.IContainer components = null;

        /// <summary>
        /// Clean up any resources being used.
        /// </summary>
        /// <param name="disposing">true if managed resources should be disposed; otherwise, false.</param>
        protected override void Dispose(bool disposing)
        {
            if (disposing && (components != null))
            {
                components.Dispose();
            }
            base.Dispose(disposing);
        }

        #region Windows Form Designer generated code

        /// <summary>
        /// Required method for Designer support - do not modify
        /// the contents of this method with the code editor.
        /// </summary>
        private void InitializeComponent()
        {
            this.panel1 = new System.Windows.Forms.Panel();
            this.txt_parsed = new System.Windows.Forms.TextBox();
            this.btn_close = new System.Windows.Forms.Button();
            this.btn_check = new System.Windows.Forms.Button();
            this.btn_parse = new System.Windows.Forms.Button();
            this.panel2 = new System.Windows.Forms.Panel();
            this.txt_help = new System.Windows.Forms.Label();
            this.txt_formula = new System.Windows.Forms.TextBox();
            this.panel1.SuspendLayout();
            this.panel2.SuspendLayout();
            this.SuspendLayout();
            // 
            // panel1
            // 
            this.panel1.Controls.Add(this.txt_parsed);
            this.panel1.Controls.Add(this.btn_close);
            this.panel1.Controls.Add(this.btn_check);
            this.panel1.Controls.Add(this.btn_parse);
            this.panel1.Dock = System.Windows.Forms.DockStyle.Bottom;
            this.panel1.Location = new System.Drawing.Point(0, 249);
            this.panel1.Name = "panel1";
            this.panel1.Size = new System.Drawing.Size(665, 137);
            this.panel1.TabIndex = 1;
            // 
            // txt_parsed
            // 
            this.txt_parsed.Dock = System.Windows.Forms.DockStyle.Top;
            this.txt_parsed.Location = new System.Drawing.Point(0, 0);
            this.txt_parsed.Multiline = true;
            this.txt_parsed.Name = "txt_parsed";
            this.txt_parsed.Size = new System.Drawing.Size(665, 76);
            this.txt_parsed.TabIndex = 3;
            // 
            // btn_close
            // 
            this.btn_close.Location = new System.Drawing.Point(495, 82);
            this.btn_close.Name = "btn_close";
            this.btn_close.Size = new System.Drawing.Size(158, 39);
            this.btn_close.TabIndex = 2;
            this.btn_close.Text = "Close";
            this.btn_close.UseVisualStyleBackColor = true;
            this.btn_close.Click += new System.EventHandler(this.btn_close_Click);
            // 
            // btn_check
            // 
            this.btn_check.Location = new System.Drawing.Point(254, 82);
            this.btn_check.Name = "btn_check";
            this.btn_check.Size = new System.Drawing.Size(151, 39);
            this.btn_check.TabIndex = 1;
            this.btn_check.Text = "Check Valid";
            this.btn_check.UseVisualStyleBackColor = true;
            this.btn_check.Click += new System.EventHandler(this.btn_check_Click);
            // 
            // btn_parse
            // 
            this.btn_parse.Location = new System.Drawing.Point(36, 82);
            this.btn_parse.Name = "btn_parse";
            this.btn_parse.Size = new System.Drawing.Size(141, 39);
            this.btn_parse.TabIndex = 0;
            this.btn_parse.Text = "Parse Formula";
            this.btn_parse.UseVisualStyleBackColor = true;
            this.btn_parse.Click += new System.EventHandler(this.btn_parse_Click);
            // 
            // panel2
            // 
            this.panel2.Controls.Add(this.txt_help);
            this.panel2.Dock = System.Windows.Forms.DockStyle.Top;
            this.panel2.Location = new System.Drawing.Point(0, 0);
            this.panel2.Name = "panel2";
            this.panel2.Size = new System.Drawing.Size(665, 152);
            this.panel2.TabIndex = 3;
            // 
            // txt_help
            // 
            this.txt_help.AutoSize = true;
            this.txt_help.Dock = System.Windows.Forms.DockStyle.Fill;
            this.txt_help.Location = new System.Drawing.Point(0, 0);
            this.txt_help.Name = "txt_help";
            this.txt_help.Size = new System.Drawing.Size(35, 13);
            this.txt_help.TabIndex = 3;
            this.txt_help.Text = "label1";
            // 
            // txt_formula
            // 
            this.txt_formula.Dock = System.Windows.Forms.DockStyle.Fill;
            this.txt_formula.Location = new System.Drawing.Point(0, 152);
            this.txt_formula.Multiline = true;
            this.txt_formula.Name = "txt_formula";
            this.txt_formula.Size = new System.Drawing.Size(665, 97);
            this.txt_formula.TabIndex = 4;
            // 
            // Calc
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.ClientSize = new System.Drawing.Size(665, 386);
            this.Controls.Add(this.txt_formula);
            this.Controls.Add(this.panel2);
            this.Controls.Add(this.panel1);
            this.Name = "Calc";
            this.Text = "Quick Calculator";
            this.Load += new System.EventHandler(this.Calc_Load);
            this.panel1.ResumeLayout(false);
            this.panel1.PerformLayout();
            this.panel2.ResumeLayout(false);
            this.panel2.PerformLayout();
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.Panel panel1;
        private System.Windows.Forms.Button btn_parse;
        private System.Windows.Forms.Button btn_close;
        private System.Windows.Forms.Button btn_check;
        private System.Windows.Forms.TextBox txt_parsed;
        private System.Windows.Forms.Panel panel2;
        private System.Windows.Forms.Label txt_help;
        private System.Windows.Forms.TextBox txt_formula;
    }
}