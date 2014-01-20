namespace QED
{
    partial class ViewBox
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
            this.tab_Panel = new System.Windows.Forms.TabControl();
            this.txt_Info = new System.Windows.Forms.TextBox();
            this.SuspendLayout();
            // 
            // tab_Panel
            // 
            this.tab_Panel.Location = new System.Drawing.Point(4, 82);
            this.tab_Panel.Name = "tab_Panel";
            this.tab_Panel.SelectedIndex = 0;
            this.tab_Panel.Size = new System.Drawing.Size(671, 525);
            this.tab_Panel.TabIndex = 0;
            // 
            // txt_Info
            // 
            this.txt_Info.Location = new System.Drawing.Point(4, 3);
            this.txt_Info.Multiline = true;
            this.txt_Info.Name = "txt_Info";
            this.txt_Info.ScrollBars = System.Windows.Forms.ScrollBars.Both;
            this.txt_Info.Size = new System.Drawing.Size(671, 73);
            this.txt_Info.TabIndex = 1;
            // 
            // ViewBox
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.ClientSize = new System.Drawing.Size(678, 609);
            this.Controls.Add(this.txt_Info);
            this.Controls.Add(this.tab_Panel);
            this.Name = "ViewBox";
            this.Text = "ViewBox";
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.TabControl tab_Panel;
        private System.Windows.Forms.TextBox txt_Info;
    }
}