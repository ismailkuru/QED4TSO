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

using System;
using System.IO;
using System.Drawing;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel;
using System.Windows.Forms;
using System.Diagnostics;
using System.Threading;
using Microsoft.Glee.Drawing;
using Microsoft.Boogie;
using BoogiePL;
using System.Text;

	/// <summary>
    /// Summary description for QETGui.
	/// </summary>
	public class QETGui : System.Windows.Forms.Form
    {
        private Panel panel_right;
        private MenuStrip menuStrip1;
        private ToolStripMenuItem configurationToolStripMenuItem;
        private ToolStripMenuItem setHomeToolStripMenuItem;
        private ToolStripMenuItem loadConfigurationToolStripMenuItem;
        private ToolStripMenuItem saveConfigurationToolStripMenuItem;
        private ToolStripMenuItem showConfigurationToolStripMenuItem;
        private ToolStripMenuItem exitQETToolStripMenuItem;
        private ToolStripMenuItem programToolStripMenuItem;
        private ToolStripMenuItem loadProgramToolStripMenuItem;
        private ToolStripMenuItem saveProgramToolStripMenuItem;
        private ToolStripMenuItem saveCurrentProgramToolStripMenuItem;
        private ToolStripMenuItem parseResolveTypeCheckProgramToolStripMenuItem;
        private ToolStripMenuItem saveLoadCurrentProgramToolStripMenuItem;
        private ToolStripMenuItem proofScriptToolStripMenuItem;
        private ToolStripMenuItem loadScriptToolStripMenuItem;
        private ToolStripMenuItem saveScriptToolStripMenuItem;
        private ToolStripMenuItem saveCommandHistoryToolStripMenuItem;
        private ToolStripMenuItem appendCommandHistoryToolStripMenuItem;
        private ToolStripMenuItem clearProofScriptToolStripMenuItem;
        private ToolStripMenuItem clearCommandHistoryToolStripMenuItem;
        private ToolStripMenuItem reportToolStripMenuItem;
        private ToolStripMenuItem previousToolStripMenuItem;
        private ToolStripMenuItem nextToolStripMenuItem;
        private ToolStripMenuItem firstToolStripMenuItem;
        private ToolStripMenuItem lastToolStripMenuItem;
        private ToolStripMenuItem showStatisticsToolStripMenuItem;
        private ToolStripMenuItem loadProgramToolStripMenuItem1;
        private ToolStripMenuItem clearProofHistoryToolStripMenuItem;
        private ToolStripMenuItem runToolStripMenuItem;
        private ToolStripMenuItem runEntireScriptToolStripMenuItem;
        private ToolStripMenuItem resetProofToolStripMenuItem;
        private ToolStripMenuItem saveProofToolStripMenuItem;
        private ToolStripMenuItem utilsToolStripMenuItem;
        private ToolStripMenuItem checkValidToolStripMenuItem;
        private ToolStripMenuItem scriptStatisticsToolStripMenuItem;
        private ToolStripMenuItem searchToolStripMenuItem;
        private ToolStripMenuItem infoToolStripMenuItem1;
        private ToolStripMenuItem showTransitionPredicateToolStripMenuItem;
        private ToolStripMenuItem showLastMoverReportToolStripMenuItem;
        private ToolStripMenuItem showLastErrorTraceToolStripMenuItem;
        private ToolStripMenuItem showLoopInformationToolStripMenuItem;
        private ToolStripMenuItem copySelectedAtomicCodeToolStripMenuItem;
        private ToolStripMenuItem viewToolStripMenuItem;
        private ToolStripMenuItem viewLogToolStripMenuItem;
        private ToolStripMenuItem clearConsoleToolStripMenuItem;
        private ToolStripMenuItem changeTextFontToolStripMenuItem;
        private TextBox txt_Output;
        private TabControl tab_ControlPanel;
        private TabPage tabPage4;
        private TextBox txt_ProofState;
        private TabPage tabPage1;
        private ListBox lst_Script;
        private Button btn_DeleteCommand;
        private Button btn_InsertCommand;
        private TabPage tabPage2;
        private ListBox lst_Commands;
        private TabPage tabPage3;
        private ListBox lst_history;
        private TabPage tabPage5;
        private TextBox txt_Statistics;
        private TabPage tabPage6;
        private CheckBox checkBox8;
        private CheckBox checkBox7;
        private CheckBox checkBox6;
        private CheckBox checkBox5;
        private CheckBox checkBox4;
        private CheckBox checkBox3;
        private CheckBox checkBox2;
        private CheckBox checkBox1;
        private TabControl tab_Panel;
        private Panel panel_command;
        private Panel panel_buttons;
        private Button btn_RunNext;
        private Button btn_RunMultiple;
        private ComboBox cmb_commands;
        private RichTextBox txt_Command;
		/// <summary>
		/// Required designer variable.
		/// </summary>
		private System.ComponentModel.Container components = null;

        public QETGui()
		{
			//
			// Required for Windows Form Designer support
			//
			InitializeComponent();
		}

		/// <summary>
		/// Clean up any resources being used.
		/// </summary>
		protected override void Dispose( bool disposing )
		{
			if( disposing )
			{
				if(components != null)
				{
					components.Dispose();
				}
			}
			base.Dispose( disposing );
		}

		#region Windows Form Designer generated code
		/// <summary>
		/// Required method for Designer support - do not modify
		/// the contents of this method with the code editor.
		/// </summary>
		private void InitializeComponent()
		{
			System.ComponentModel.ComponentResourceManager resources = new System.ComponentModel.ComponentResourceManager(typeof(QETGui));
			this.panel_right = new System.Windows.Forms.Panel();
			this.panel_command = new System.Windows.Forms.Panel();
			this.txt_Command = new System.Windows.Forms.RichTextBox();
			this.panel_buttons = new System.Windows.Forms.Panel();
			this.btn_RunNext = new System.Windows.Forms.Button();
			this.btn_RunMultiple = new System.Windows.Forms.Button();
			this.cmb_commands = new System.Windows.Forms.ComboBox();
			this.tab_ControlPanel = new System.Windows.Forms.TabControl();
			this.tabPage4 = new System.Windows.Forms.TabPage();
			this.txt_ProofState = new System.Windows.Forms.TextBox();
			this.tabPage1 = new System.Windows.Forms.TabPage();
			this.lst_Script = new System.Windows.Forms.ListBox();
			this.btn_DeleteCommand = new System.Windows.Forms.Button();
			this.btn_InsertCommand = new System.Windows.Forms.Button();
			this.tabPage2 = new System.Windows.Forms.TabPage();
			this.lst_Commands = new System.Windows.Forms.ListBox();
			this.tabPage3 = new System.Windows.Forms.TabPage();
			this.lst_history = new System.Windows.Forms.ListBox();
			this.tabPage5 = new System.Windows.Forms.TabPage();
			this.txt_Statistics = new System.Windows.Forms.TextBox();
			this.tabPage6 = new System.Windows.Forms.TabPage();
			this.checkBox8 = new System.Windows.Forms.CheckBox();
			this.checkBox7 = new System.Windows.Forms.CheckBox();
			this.checkBox6 = new System.Windows.Forms.CheckBox();
			this.checkBox5 = new System.Windows.Forms.CheckBox();
			this.checkBox4 = new System.Windows.Forms.CheckBox();
			this.checkBox3 = new System.Windows.Forms.CheckBox();
			this.checkBox2 = new System.Windows.Forms.CheckBox();
			this.checkBox1 = new System.Windows.Forms.CheckBox();
			this.txt_Output = new System.Windows.Forms.TextBox();
			this.menuStrip1 = new System.Windows.Forms.MenuStrip();
			this.configurationToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.setHomeToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.loadConfigurationToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.saveConfigurationToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.showConfigurationToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.exitQETToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.programToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.loadProgramToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.saveProgramToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.saveCurrentProgramToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.parseResolveTypeCheckProgramToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.saveLoadCurrentProgramToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.proofScriptToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.loadScriptToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.saveScriptToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.saveCommandHistoryToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.appendCommandHistoryToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.clearProofScriptToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.clearCommandHistoryToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.reportToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.previousToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.nextToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.firstToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.lastToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.showStatisticsToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.loadProgramToolStripMenuItem1 = new System.Windows.Forms.ToolStripMenuItem();
			this.clearProofHistoryToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.runToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.runEntireScriptToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.resetProofToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.saveProofToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.utilsToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.checkValidToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.scriptStatisticsToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.searchToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.infoToolStripMenuItem1 = new System.Windows.Forms.ToolStripMenuItem();
			this.showTransitionPredicateToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.showLastMoverReportToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.showLastErrorTraceToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.showLoopInformationToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.copySelectedAtomicCodeToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.viewToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.viewLogToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.clearConsoleToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.changeTextFontToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
			this.tab_Panel = new System.Windows.Forms.TabControl();
			this.panel_right.SuspendLayout();
			this.panel_command.SuspendLayout();
			this.panel_buttons.SuspendLayout();
			this.tab_ControlPanel.SuspendLayout();
			this.tabPage4.SuspendLayout();
			this.tabPage1.SuspendLayout();
			this.tabPage2.SuspendLayout();
			this.tabPage3.SuspendLayout();
			this.tabPage5.SuspendLayout();
			this.tabPage6.SuspendLayout();
			this.menuStrip1.SuspendLayout();
			this.SuspendLayout();
			// 
			// panel_right
			// 
			this.panel_right.Controls.Add(this.panel_command);
			this.panel_right.Controls.Add(this.tab_ControlPanel);
			this.panel_right.Controls.Add(this.txt_Output);
			this.panel_right.Controls.Add(this.menuStrip1);
			this.panel_right.Dock = System.Windows.Forms.DockStyle.Right;
			this.panel_right.Location = new System.Drawing.Point(658, 0);
			this.panel_right.Name = "panel_right";
			this.panel_right.Size = new System.Drawing.Size(570, 763);
			this.panel_right.TabIndex = 28;
			// 
			// panel_command
			// 
			this.panel_command.Controls.Add(this.txt_Command);
			this.panel_command.Controls.Add(this.panel_buttons);
			this.panel_command.Controls.Add(this.cmb_commands);
			this.panel_command.Dock = System.Windows.Forms.DockStyle.Fill;
			this.panel_command.Location = new System.Drawing.Point(0, 321);
			this.panel_command.Name = "panel_command";
			this.panel_command.Size = new System.Drawing.Size(570, 137);
			this.panel_command.TabIndex = 87;
			// 
			// txt_Command
			// 
			this.txt_Command.BackColor = System.Drawing.Color.FromArgb(((int)(((byte)(255)))), ((int)(((byte)(255)))), ((int)(((byte)(128)))));
			this.txt_Command.Dock = System.Windows.Forms.DockStyle.Fill;
			this.txt_Command.Font = new System.Drawing.Font("Microsoft Sans Serif", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(162)));
			this.txt_Command.Location = new System.Drawing.Point(0, 65);
			this.txt_Command.Name = "txt_Command";
			this.txt_Command.Size = new System.Drawing.Size(570, 72);
			this.txt_Command.TabIndex = 90;
			this.txt_Command.Text = "Write the proof command here...";
			this.txt_Command.TextChanged += new System.EventHandler(this.txt_Command_TextChanged);
			this.txt_Command.GotFocus += new System.EventHandler(this.txt_Command_GotFocus);
			this.txt_Command.KeyDown += new System.Windows.Forms.KeyEventHandler(this.txt_Command_KeyPressed);
			this.txt_Command.LostFocus += new System.EventHandler(this.txt_Command_LostFocus);
			// 
			// panel_buttons
			// 
			this.panel_buttons.Controls.Add(this.btn_RunNext);
			this.panel_buttons.Controls.Add(this.btn_RunMultiple);
			this.panel_buttons.Dock = System.Windows.Forms.DockStyle.Top;
			this.panel_buttons.Location = new System.Drawing.Point(0, 23);
			this.panel_buttons.Name = "panel_buttons";
			this.panel_buttons.Size = new System.Drawing.Size(570, 42);
			this.panel_buttons.TabIndex = 89;
			// 
			// btn_RunNext
			// 
			this.btn_RunNext.BackColor = System.Drawing.SystemColors.Control;
			this.btn_RunNext.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(162)));
			this.btn_RunNext.Location = new System.Drawing.Point(6, 5);
			this.btn_RunNext.Name = "btn_RunNext";
			this.btn_RunNext.Size = new System.Drawing.Size(147, 33);
			this.btn_RunNext.TabIndex = 86;
			this.btn_RunNext.Text = "Run Next";
			this.btn_RunNext.UseVisualStyleBackColor = false;
			this.btn_RunNext.Click += new System.EventHandler(this.btn_RunNext_Click);
			// 
			// btn_RunMultiple
			// 
			this.btn_RunMultiple.BackColor = System.Drawing.SystemColors.Control;
			this.btn_RunMultiple.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(162)));
			this.btn_RunMultiple.Location = new System.Drawing.Point(159, 5);
			this.btn_RunMultiple.Name = "btn_RunMultiple";
			this.btn_RunMultiple.Size = new System.Drawing.Size(147, 33);
			this.btn_RunMultiple.TabIndex = 88;
			this.btn_RunMultiple.Text = "Run Multiple";
			this.btn_RunMultiple.UseVisualStyleBackColor = false;
			this.btn_RunMultiple.Click += new System.EventHandler(this.btn_RunMultiple_Click);
			// 
			// cmb_commands
			// 
			this.cmb_commands.BackColor = System.Drawing.SystemColors.Window;
			this.cmb_commands.Dock = System.Windows.Forms.DockStyle.Top;
			this.cmb_commands.DropDownStyle = System.Windows.Forms.ComboBoxStyle.DropDownList;
			this.cmb_commands.Font = new System.Drawing.Font("Microsoft Sans Serif", 9F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(162)));
			this.cmb_commands.FormattingEnabled = true;
			this.cmb_commands.Location = new System.Drawing.Point(0, 0);
			this.cmb_commands.Name = "cmb_commands";
			this.cmb_commands.Size = new System.Drawing.Size(570, 23);
			this.cmb_commands.TabIndex = 77;
			this.cmb_commands.SelectedIndexChanged += new System.EventHandler(this.cmb_commands_SelectedIndexChanged);
			// 
			// tab_ControlPanel
			// 
			this.tab_ControlPanel.Controls.Add(this.tabPage4);
			this.tab_ControlPanel.Controls.Add(this.tabPage1);
			this.tab_ControlPanel.Controls.Add(this.tabPage2);
			this.tab_ControlPanel.Controls.Add(this.tabPage3);
			this.tab_ControlPanel.Controls.Add(this.tabPage5);
			this.tab_ControlPanel.Controls.Add(this.tabPage6);
			this.tab_ControlPanel.Dock = System.Windows.Forms.DockStyle.Bottom;
			this.tab_ControlPanel.Location = new System.Drawing.Point(0, 458);
			this.tab_ControlPanel.Name = "tab_ControlPanel";
			this.tab_ControlPanel.SelectedIndex = 0;
			this.tab_ControlPanel.Size = new System.Drawing.Size(570, 305);
			this.tab_ControlPanel.TabIndex = 86;
			// 
			// tabPage4
			// 
			this.tabPage4.Controls.Add(this.txt_ProofState);
			this.tabPage4.Location = new System.Drawing.Point(4, 22);
			this.tabPage4.Name = "tabPage4";
			this.tabPage4.Size = new System.Drawing.Size(562, 279);
			this.tabPage4.TabIndex = 3;
			this.tabPage4.Text = "Proof State";
			this.tabPage4.UseVisualStyleBackColor = true;
			// 
			// txt_ProofState
			// 
			this.txt_ProofState.Dock = System.Windows.Forms.DockStyle.Fill;
			this.txt_ProofState.Location = new System.Drawing.Point(0, 0);
			this.txt_ProofState.Multiline = true;
			this.txt_ProofState.Name = "txt_ProofState";
			this.txt_ProofState.ScrollBars = System.Windows.Forms.ScrollBars.Both;
			this.txt_ProofState.Size = new System.Drawing.Size(562, 279);
			this.txt_ProofState.TabIndex = 0;
			// 
			// tabPage1
			// 
			this.tabPage1.Controls.Add(this.lst_Script);
			this.tabPage1.Controls.Add(this.btn_DeleteCommand);
			this.tabPage1.Controls.Add(this.btn_InsertCommand);
			this.tabPage1.Location = new System.Drawing.Point(4, 22);
			this.tabPage1.Name = "tabPage1";
			this.tabPage1.Padding = new System.Windows.Forms.Padding(3);
			this.tabPage1.Size = new System.Drawing.Size(562, 279);
			this.tabPage1.TabIndex = 0;
			this.tabPage1.Text = "Proof Script";
			this.tabPage1.UseVisualStyleBackColor = true;
			// 
			// lst_Script
			// 
			this.lst_Script.Dock = System.Windows.Forms.DockStyle.Bottom;
			this.lst_Script.Font = new System.Drawing.Font("Microsoft Sans Serif", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(162)));
			this.lst_Script.FormattingEnabled = true;
			this.lst_Script.ItemHeight = 16;
			this.lst_Script.Location = new System.Drawing.Point(3, 48);
			this.lst_Script.Name = "lst_Script";
			this.lst_Script.SelectionMode = System.Windows.Forms.SelectionMode.MultiExtended;
			this.lst_Script.Size = new System.Drawing.Size(556, 228);
			this.lst_Script.TabIndex = 47;
			this.lst_Script.SelectedIndexChanged += new System.EventHandler(this.lst_Script_SelectedIndexChanged);
			this.lst_Script.DoubleClick += new System.EventHandler(this.lst_Script_DoubleClick);
			this.lst_Script.KeyDown += new System.Windows.Forms.KeyEventHandler(this.lst_Script_KeyPressed);
			// 
			// btn_DeleteCommand
			// 
			this.btn_DeleteCommand.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(162)));
			this.btn_DeleteCommand.Location = new System.Drawing.Point(114, 6);
			this.btn_DeleteCommand.Name = "btn_DeleteCommand";
			this.btn_DeleteCommand.Size = new System.Drawing.Size(102, 27);
			this.btn_DeleteCommand.TabIndex = 53;
			this.btn_DeleteCommand.Text = "Delete";
			this.btn_DeleteCommand.UseVisualStyleBackColor = true;
			this.btn_DeleteCommand.Click += new System.EventHandler(this.btn_DeleteCommand_Click);
			// 
			// btn_InsertCommand
			// 
			this.btn_InsertCommand.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(162)));
			this.btn_InsertCommand.Location = new System.Drawing.Point(6, 6);
			this.btn_InsertCommand.Name = "btn_InsertCommand";
			this.btn_InsertCommand.Size = new System.Drawing.Size(102, 27);
			this.btn_InsertCommand.TabIndex = 50;
			this.btn_InsertCommand.Text = "Insert New";
			this.btn_InsertCommand.UseVisualStyleBackColor = true;
			this.btn_InsertCommand.Click += new System.EventHandler(this.btn_InsertCommand_Click);
			// 
			// tabPage2
			// 
			this.tabPage2.Controls.Add(this.lst_Commands);
			this.tabPage2.Location = new System.Drawing.Point(4, 22);
			this.tabPage2.Name = "tabPage2";
			this.tabPage2.Padding = new System.Windows.Forms.Padding(3);
			this.tabPage2.Size = new System.Drawing.Size(562, 279);
			this.tabPage2.TabIndex = 1;
			this.tabPage2.Text = "Command History";
			this.tabPage2.UseVisualStyleBackColor = true;
			// 
			// lst_Commands
			// 
			this.lst_Commands.Dock = System.Windows.Forms.DockStyle.Fill;
			this.lst_Commands.Font = new System.Drawing.Font("Microsoft Sans Serif", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(162)));
			this.lst_Commands.FormattingEnabled = true;
			this.lst_Commands.ItemHeight = 16;
			this.lst_Commands.Location = new System.Drawing.Point(3, 3);
			this.lst_Commands.Name = "lst_Commands";
			this.lst_Commands.SelectionMode = System.Windows.Forms.SelectionMode.MultiExtended;
			this.lst_Commands.Size = new System.Drawing.Size(556, 273);
			this.lst_Commands.TabIndex = 70;
			this.lst_Commands.SelectedIndexChanged += new System.EventHandler(this.lst_Commands_SelectedIndexChanged);
			this.lst_Commands.DoubleClick += new System.EventHandler(this.lst_Commands_DoubleClicked);
			this.lst_Commands.KeyDown += new System.Windows.Forms.KeyEventHandler(this.lst_Commands_KeyPressed);
			// 
			// tabPage3
			// 
			this.tabPage3.Controls.Add(this.lst_history);
			this.tabPage3.Location = new System.Drawing.Point(4, 22);
			this.tabPage3.Name = "tabPage3";
			this.tabPage3.Size = new System.Drawing.Size(562, 279);
			this.tabPage3.TabIndex = 2;
			this.tabPage3.Text = "Proof History";
			this.tabPage3.UseVisualStyleBackColor = true;
			// 
			// lst_history
			// 
			this.lst_history.Dock = System.Windows.Forms.DockStyle.Fill;
			this.lst_history.Font = new System.Drawing.Font("Microsoft Sans Serif", 9.75F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(162)));
			this.lst_history.FormattingEnabled = true;
			this.lst_history.ItemHeight = 16;
			this.lst_history.Location = new System.Drawing.Point(0, 0);
			this.lst_history.Name = "lst_history";
			this.lst_history.Size = new System.Drawing.Size(562, 279);
			this.lst_history.TabIndex = 65;
			this.lst_history.DoubleClick += new System.EventHandler(this.lst_history_DoubleClick);
			this.lst_history.KeyDown += new System.Windows.Forms.KeyEventHandler(this.lst_history_KeyPressed);
			// 
			// tabPage5
			// 
			this.tabPage5.Controls.Add(this.txt_Statistics);
			this.tabPage5.Location = new System.Drawing.Point(4, 22);
			this.tabPage5.Name = "tabPage5";
			this.tabPage5.Padding = new System.Windows.Forms.Padding(3);
			this.tabPage5.Size = new System.Drawing.Size(562, 279);
			this.tabPage5.TabIndex = 4;
			this.tabPage5.Text = "Statistics";
			this.tabPage5.UseVisualStyleBackColor = true;
			// 
			// txt_Statistics
			// 
			this.txt_Statistics.Dock = System.Windows.Forms.DockStyle.Fill;
			this.txt_Statistics.Location = new System.Drawing.Point(3, 3);
			this.txt_Statistics.Multiline = true;
			this.txt_Statistics.Name = "txt_Statistics";
			this.txt_Statistics.Size = new System.Drawing.Size(556, 273);
			this.txt_Statistics.TabIndex = 0;
			// 
			// tabPage6
			// 
			this.tabPage6.Controls.Add(this.checkBox8);
			this.tabPage6.Controls.Add(this.checkBox7);
			this.tabPage6.Controls.Add(this.checkBox6);
			this.tabPage6.Controls.Add(this.checkBox5);
			this.tabPage6.Controls.Add(this.checkBox4);
			this.tabPage6.Controls.Add(this.checkBox3);
			this.tabPage6.Controls.Add(this.checkBox2);
			this.tabPage6.Controls.Add(this.checkBox1);
			this.tabPage6.Location = new System.Drawing.Point(4, 22);
			this.tabPage6.Name = "tabPage6";
			this.tabPage6.Size = new System.Drawing.Size(562, 279);
			this.tabPage6.TabIndex = 5;
			this.tabPage6.Text = "Options";
			this.tabPage6.UseVisualStyleBackColor = true;
			// 
			// checkBox8
			// 
			this.checkBox8.AutoSize = true;
			this.checkBox8.Location = new System.Drawing.Point(3, 164);
			this.checkBox8.Name = "checkBox8";
			this.checkBox8.Size = new System.Drawing.Size(106, 17);
			this.checkBox8.TabIndex = 7;
			this.checkBox8.Text = "Color Text Boxes";
			this.checkBox8.UseVisualStyleBackColor = true;
			this.checkBox8.CheckedChanged += new System.EventHandler(this.checkBox8_CheckedChanged);
			// 
			// checkBox7
			// 
			this.checkBox7.AutoSize = true;
			this.checkBox7.Location = new System.Drawing.Point(3, 141);
			this.checkBox7.Name = "checkBox7";
			this.checkBox7.Size = new System.Drawing.Size(107, 17);
			this.checkBox7.TabIndex = 6;
			this.checkBox7.Text = "Show Block CFG";
			this.checkBox7.UseVisualStyleBackColor = true;
			this.checkBox7.CheckedChanged += new System.EventHandler(this.checkBox7_CheckedChanged);
			// 
			// checkBox6
			// 
			this.checkBox6.AutoSize = true;
			this.checkBox6.Location = new System.Drawing.Point(3, 118);
			this.checkBox6.Name = "checkBox6";
			this.checkBox6.Size = new System.Drawing.Size(89, 17);
			this.checkBox6.TabIndex = 5;
			this.checkBox6.Text = "Line numbers";
			this.checkBox6.UseVisualStyleBackColor = true;
			this.checkBox6.CheckedChanged += new System.EventHandler(this.checkBox6_CheckedChanged);
			// 
			// checkBox5
			// 
			this.checkBox5.AutoSize = true;
			this.checkBox5.Location = new System.Drawing.Point(3, 95);
			this.checkBox5.Name = "checkBox5";
			this.checkBox5.Size = new System.Drawing.Size(148, 17);
			this.checkBox5.TabIndex = 4;
			this.checkBox5.Text = "Disable merging branches";
			this.checkBox5.UseVisualStyleBackColor = true;
			this.checkBox5.CheckedChanged += new System.EventHandler(this.checkBox5_CheckedChanged);
			// 
			// checkBox4
			// 
			this.checkBox4.AutoSize = true;
			this.checkBox4.Location = new System.Drawing.Point(3, 72);
			this.checkBox4.Name = "checkBox4";
			this.checkBox4.Size = new System.Drawing.Size(138, 17);
			this.checkBox4.TabIndex = 3;
			this.checkBox4.Text = "Auto-save configuration";
			this.checkBox4.UseVisualStyleBackColor = true;
			this.checkBox4.CheckedChanged += new System.EventHandler(this.checkBox4_CheckedChanged);
			// 
			// checkBox3
			// 
			this.checkBox3.AutoSize = true;
			this.checkBox3.Location = new System.Drawing.Point(3, 49);
			this.checkBox3.Name = "checkBox3";
			this.checkBox3.Size = new System.Drawing.Size(175, 17);
			this.checkBox3.TabIndex = 2;
			this.checkBox3.Text = "Auto-save executed commands";
			this.checkBox3.UseVisualStyleBackColor = true;
			this.checkBox3.CheckedChanged += new System.EventHandler(this.checkBox3_CheckedChanged);
			// 
			// checkBox2
			// 
			this.checkBox2.AutoSize = true;
			this.checkBox2.Location = new System.Drawing.Point(3, 26);
			this.checkBox2.Name = "checkBox2";
			this.checkBox2.Size = new System.Drawing.Size(127, 17);
			this.checkBox2.TabIndex = 1;
			this.checkBox2.Text = "Do iterative reduction";
			this.checkBox2.UseVisualStyleBackColor = true;
			this.checkBox2.CheckedChanged += new System.EventHandler(this.checkBox2_CheckedChanged);
			// 
			// checkBox1
			// 
			this.checkBox1.AutoSize = true;
			this.checkBox1.Location = new System.Drawing.Point(3, 3);
			this.checkBox1.Name = "checkBox1";
			this.checkBox1.Size = new System.Drawing.Size(134, 17);
			this.checkBox1.TabIndex = 0;
			this.checkBox1.Text = "Merge returning blocks";
			this.checkBox1.UseVisualStyleBackColor = true;
			this.checkBox1.CheckedChanged += new System.EventHandler(this.checkBox1_CheckedChanged);
			// 
			// txt_Output
			// 
			this.txt_Output.BackColor = System.Drawing.Color.Black;
			this.txt_Output.Dock = System.Windows.Forms.DockStyle.Top;
			this.txt_Output.Font = new System.Drawing.Font("Courier New", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(162)));
			this.txt_Output.ForeColor = System.Drawing.Color.White;
			this.txt_Output.Location = new System.Drawing.Point(0, 24);
			this.txt_Output.Multiline = true;
			this.txt_Output.Name = "txt_Output";
			this.txt_Output.ReadOnly = true;
			this.txt_Output.ScrollBars = System.Windows.Forms.ScrollBars.Both;
			this.txt_Output.Size = new System.Drawing.Size(570, 297);
			this.txt_Output.TabIndex = 85;
			this.txt_Output.WordWrap = false;
			// 
			// menuStrip1
			// 
			this.menuStrip1.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.configurationToolStripMenuItem,
            this.programToolStripMenuItem,
            this.proofScriptToolStripMenuItem,
            this.reportToolStripMenuItem,
            this.runToolStripMenuItem,
            this.utilsToolStripMenuItem,
            this.infoToolStripMenuItem1,
            this.viewToolStripMenuItem});
			this.menuStrip1.Location = new System.Drawing.Point(0, 0);
			this.menuStrip1.Name = "menuStrip1";
			this.menuStrip1.Size = new System.Drawing.Size(570, 24);
			this.menuStrip1.TabIndex = 64;
			this.menuStrip1.Text = "menuStrip1";
			// 
			// configurationToolStripMenuItem
			// 
			this.configurationToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.setHomeToolStripMenuItem,
            this.loadConfigurationToolStripMenuItem,
            this.saveConfigurationToolStripMenuItem,
            this.showConfigurationToolStripMenuItem,
            this.exitQETToolStripMenuItem});
			this.configurationToolStripMenuItem.Name = "configurationToolStripMenuItem";
			this.configurationToolStripMenuItem.Size = new System.Drawing.Size(84, 20);
			this.configurationToolStripMenuItem.Text = "Configuration";
			// 
			// setHomeToolStripMenuItem
			// 
			this.setHomeToolStripMenuItem.Name = "setHomeToolStripMenuItem";
			this.setHomeToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.setHomeToolStripMenuItem.Text = "Set Home";
			this.setHomeToolStripMenuItem.Click += new System.EventHandler(this.setHomeToolStripMenuItem_Click);
			// 
			// loadConfigurationToolStripMenuItem
			// 
			this.loadConfigurationToolStripMenuItem.Name = "loadConfigurationToolStripMenuItem";
			this.loadConfigurationToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.loadConfigurationToolStripMenuItem.Text = "Load Configuration";
			this.loadConfigurationToolStripMenuItem.Click += new System.EventHandler(this.loadConfigurationToolStripMenuItem_Click);
			// 
			// saveConfigurationToolStripMenuItem
			// 
			this.saveConfigurationToolStripMenuItem.Name = "saveConfigurationToolStripMenuItem";
			this.saveConfigurationToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.saveConfigurationToolStripMenuItem.Text = "Save Configuration";
			// 
			// showConfigurationToolStripMenuItem
			// 
			this.showConfigurationToolStripMenuItem.Name = "showConfigurationToolStripMenuItem";
			this.showConfigurationToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.showConfigurationToolStripMenuItem.Text = "Show Configuration";
			this.showConfigurationToolStripMenuItem.Click += new System.EventHandler(this.showConfigurationToolStripMenuItem_Click);
			// 
			// exitQETToolStripMenuItem
			// 
			this.exitQETToolStripMenuItem.Name = "exitQETToolStripMenuItem";
			this.exitQETToolStripMenuItem.Size = new System.Drawing.Size(179, 22);
			this.exitQETToolStripMenuItem.Text = "Exit QED";
			this.exitQETToolStripMenuItem.Click += new System.EventHandler(this.exitQETToolStripMenuItem_Click);
			// 
			// programToolStripMenuItem
			// 
			this.programToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.loadProgramToolStripMenuItem,
            this.saveProgramToolStripMenuItem,
            this.saveCurrentProgramToolStripMenuItem,
            this.parseResolveTypeCheckProgramToolStripMenuItem,
            this.saveLoadCurrentProgramToolStripMenuItem});
			this.programToolStripMenuItem.Name = "programToolStripMenuItem";
			this.programToolStripMenuItem.Size = new System.Drawing.Size(59, 20);
			this.programToolStripMenuItem.Text = "Program";
			// 
			// loadProgramToolStripMenuItem
			// 
			this.loadProgramToolStripMenuItem.Name = "loadProgramToolStripMenuItem";
			this.loadProgramToolStripMenuItem.Size = new System.Drawing.Size(254, 22);
			this.loadProgramToolStripMenuItem.Text = "Load Program";
			this.loadProgramToolStripMenuItem.Click += new System.EventHandler(this.loadProgramToolStripMenuItem_Click);
			// 
			// saveProgramToolStripMenuItem
			// 
			this.saveProgramToolStripMenuItem.Name = "saveProgramToolStripMenuItem";
			this.saveProgramToolStripMenuItem.Size = new System.Drawing.Size(254, 22);
			this.saveProgramToolStripMenuItem.Text = "Save Input Program";
			this.saveProgramToolStripMenuItem.Click += new System.EventHandler(this.saveProgramToolStripMenuItem_Click);
			// 
			// saveCurrentProgramToolStripMenuItem
			// 
			this.saveCurrentProgramToolStripMenuItem.Name = "saveCurrentProgramToolStripMenuItem";
			this.saveCurrentProgramToolStripMenuItem.Size = new System.Drawing.Size(254, 22);
			this.saveCurrentProgramToolStripMenuItem.Text = "Save Current Program";
			this.saveCurrentProgramToolStripMenuItem.Click += new System.EventHandler(this.saveCurrentProgramToolStripMenuItem_Click);
			// 
			// parseResolveTypeCheckProgramToolStripMenuItem
			// 
			this.parseResolveTypeCheckProgramToolStripMenuItem.Name = "parseResolveTypeCheckProgramToolStripMenuItem";
			this.parseResolveTypeCheckProgramToolStripMenuItem.Size = new System.Drawing.Size(254, 22);
			this.parseResolveTypeCheckProgramToolStripMenuItem.Text = "Parse/Resolve/TypeCheck Program";
			this.parseResolveTypeCheckProgramToolStripMenuItem.Click += new System.EventHandler(this.parseResolveTypeCheckProgramToolStripMenuItem_Click);
			// 
			// saveLoadCurrentProgramToolStripMenuItem
			// 
			this.saveLoadCurrentProgramToolStripMenuItem.Name = "saveLoadCurrentProgramToolStripMenuItem";
			this.saveLoadCurrentProgramToolStripMenuItem.Size = new System.Drawing.Size(254, 22);
			this.saveLoadCurrentProgramToolStripMenuItem.Text = "Save+Load Current Program";
			this.saveLoadCurrentProgramToolStripMenuItem.Click += new System.EventHandler(this.saveLoadCurrentProgramToolStripMenuItem_Click);
			// 
			// proofScriptToolStripMenuItem
			// 
			this.proofScriptToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.loadScriptToolStripMenuItem,
            this.saveScriptToolStripMenuItem,
            this.saveCommandHistoryToolStripMenuItem,
            this.appendCommandHistoryToolStripMenuItem,
            this.clearProofScriptToolStripMenuItem,
            this.clearCommandHistoryToolStripMenuItem});
			this.proofScriptToolStripMenuItem.Name = "proofScriptToolStripMenuItem";
			this.proofScriptToolStripMenuItem.Size = new System.Drawing.Size(72, 20);
			this.proofScriptToolStripMenuItem.Text = "ProofScript";
			// 
			// loadScriptToolStripMenuItem
			// 
			this.loadScriptToolStripMenuItem.Name = "loadScriptToolStripMenuItem";
			this.loadScriptToolStripMenuItem.Size = new System.Drawing.Size(209, 22);
			this.loadScriptToolStripMenuItem.Text = "Load Script";
			this.loadScriptToolStripMenuItem.Click += new System.EventHandler(this.loadScriptToolStripMenuItem_Click);
			// 
			// saveScriptToolStripMenuItem
			// 
			this.saveScriptToolStripMenuItem.Name = "saveScriptToolStripMenuItem";
			this.saveScriptToolStripMenuItem.Size = new System.Drawing.Size(209, 22);
			this.saveScriptToolStripMenuItem.Text = "Save Script";
			this.saveScriptToolStripMenuItem.Click += new System.EventHandler(this.saveScriptToolStripMenuItem_Click);
			// 
			// saveCommandHistoryToolStripMenuItem
			// 
			this.saveCommandHistoryToolStripMenuItem.Name = "saveCommandHistoryToolStripMenuItem";
			this.saveCommandHistoryToolStripMenuItem.Size = new System.Drawing.Size(209, 22);
			this.saveCommandHistoryToolStripMenuItem.Text = "Save Command History";
			this.saveCommandHistoryToolStripMenuItem.Click += new System.EventHandler(this.saveCommandHistoryToolStripMenuItem_Click);
			// 
			// appendCommandHistoryToolStripMenuItem
			// 
			this.appendCommandHistoryToolStripMenuItem.Name = "appendCommandHistoryToolStripMenuItem";
			this.appendCommandHistoryToolStripMenuItem.Size = new System.Drawing.Size(209, 22);
			this.appendCommandHistoryToolStripMenuItem.Text = "Append Command History";
			this.appendCommandHistoryToolStripMenuItem.Click += new System.EventHandler(this.appendCommandHistoryToolStripMenuItem_Click);
			// 
			// clearProofScriptToolStripMenuItem
			// 
			this.clearProofScriptToolStripMenuItem.Name = "clearProofScriptToolStripMenuItem";
			this.clearProofScriptToolStripMenuItem.Size = new System.Drawing.Size(209, 22);
			this.clearProofScriptToolStripMenuItem.Text = "Clear Proof Script";
			this.clearProofScriptToolStripMenuItem.Click += new System.EventHandler(this.clearProofScriptToolStripMenuItem_Click);
			// 
			// clearCommandHistoryToolStripMenuItem
			// 
			this.clearCommandHistoryToolStripMenuItem.Name = "clearCommandHistoryToolStripMenuItem";
			this.clearCommandHistoryToolStripMenuItem.Size = new System.Drawing.Size(209, 22);
			this.clearCommandHistoryToolStripMenuItem.Text = "Clear Command History";
			this.clearCommandHistoryToolStripMenuItem.Click += new System.EventHandler(this.clearCommandHistoryToolStripMenuItem_Click);
			// 
			// reportToolStripMenuItem
			// 
			this.reportToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.previousToolStripMenuItem,
            this.nextToolStripMenuItem,
            this.firstToolStripMenuItem,
            this.lastToolStripMenuItem,
            this.showStatisticsToolStripMenuItem,
            this.loadProgramToolStripMenuItem1,
            this.clearProofHistoryToolStripMenuItem});
			this.reportToolStripMenuItem.Name = "reportToolStripMenuItem";
			this.reportToolStripMenuItem.Size = new System.Drawing.Size(53, 20);
			this.reportToolStripMenuItem.Text = "History";
			// 
			// previousToolStripMenuItem
			// 
			this.previousToolStripMenuItem.Name = "previousToolStripMenuItem";
			this.previousToolStripMenuItem.Size = new System.Drawing.Size(176, 22);
			this.previousToolStripMenuItem.Text = "Previous";
			this.previousToolStripMenuItem.Click += new System.EventHandler(this.previousToolStripMenuItem_Click);
			// 
			// nextToolStripMenuItem
			// 
			this.nextToolStripMenuItem.Name = "nextToolStripMenuItem";
			this.nextToolStripMenuItem.Size = new System.Drawing.Size(176, 22);
			this.nextToolStripMenuItem.Text = "Next";
			this.nextToolStripMenuItem.Click += new System.EventHandler(this.nextToolStripMenuItem_Click);
			// 
			// firstToolStripMenuItem
			// 
			this.firstToolStripMenuItem.Name = "firstToolStripMenuItem";
			this.firstToolStripMenuItem.Size = new System.Drawing.Size(176, 22);
			this.firstToolStripMenuItem.Text = "First";
			this.firstToolStripMenuItem.Click += new System.EventHandler(this.firstToolStripMenuItem_Click);
			// 
			// lastToolStripMenuItem
			// 
			this.lastToolStripMenuItem.Name = "lastToolStripMenuItem";
			this.lastToolStripMenuItem.Size = new System.Drawing.Size(176, 22);
			this.lastToolStripMenuItem.Text = "Last";
			this.lastToolStripMenuItem.Click += new System.EventHandler(this.lastToolStripMenuItem_Click);
			// 
			// showStatisticsToolStripMenuItem
			// 
			this.showStatisticsToolStripMenuItem.Name = "showStatisticsToolStripMenuItem";
			this.showStatisticsToolStripMenuItem.Size = new System.Drawing.Size(176, 22);
			this.showStatisticsToolStripMenuItem.Text = "Show Statistics";
			this.showStatisticsToolStripMenuItem.Click += new System.EventHandler(this.showStatisticsToolStripMenuItem_Click);
			// 
			// loadProgramToolStripMenuItem1
			// 
			this.loadProgramToolStripMenuItem1.Name = "loadProgramToolStripMenuItem1";
			this.loadProgramToolStripMenuItem1.Size = new System.Drawing.Size(176, 22);
			this.loadProgramToolStripMenuItem1.Text = "Load Program";
			this.loadProgramToolStripMenuItem1.Click += new System.EventHandler(this.loadProgramToolStripMenuItem1_Click);
			// 
			// clearProofHistoryToolStripMenuItem
			// 
			this.clearProofHistoryToolStripMenuItem.Name = "clearProofHistoryToolStripMenuItem";
			this.clearProofHistoryToolStripMenuItem.Size = new System.Drawing.Size(176, 22);
			this.clearProofHistoryToolStripMenuItem.Text = "Clear Proof History";
			this.clearProofHistoryToolStripMenuItem.Click += new System.EventHandler(this.clearProofHistoryToolStripMenuItem_Click);
			// 
			// runToolStripMenuItem
			// 
			this.runToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.runEntireScriptToolStripMenuItem,
            this.resetProofToolStripMenuItem,
            this.saveProofToolStripMenuItem});
			this.runToolStripMenuItem.Name = "runToolStripMenuItem";
			this.runToolStripMenuItem.Size = new System.Drawing.Size(45, 20);
			this.runToolStripMenuItem.Text = "Proof";
			// 
			// runEntireScriptToolStripMenuItem
			// 
			this.runEntireScriptToolStripMenuItem.Name = "runEntireScriptToolStripMenuItem";
			this.runEntireScriptToolStripMenuItem.Size = new System.Drawing.Size(165, 22);
			this.runEntireScriptToolStripMenuItem.Text = "Run Entire Script";
			this.runEntireScriptToolStripMenuItem.Click += new System.EventHandler(this.runEntireScriptToolStripMenuItem_Click);
			// 
			// resetProofToolStripMenuItem
			// 
			this.resetProofToolStripMenuItem.Name = "resetProofToolStripMenuItem";
			this.resetProofToolStripMenuItem.Size = new System.Drawing.Size(165, 22);
			this.resetProofToolStripMenuItem.Text = "Reset Proof";
			this.resetProofToolStripMenuItem.Click += new System.EventHandler(this.resetProofToolStripMenuItem_Click);
			// 
			// saveProofToolStripMenuItem
			// 
			this.saveProofToolStripMenuItem.Name = "saveProofToolStripMenuItem";
			this.saveProofToolStripMenuItem.Size = new System.Drawing.Size(165, 22);
			this.saveProofToolStripMenuItem.Text = "Save Proof";
			this.saveProofToolStripMenuItem.Click += new System.EventHandler(this.saveProofToolStripMenuItem_Click);
			// 
			// utilsToolStripMenuItem
			// 
			this.utilsToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.checkValidToolStripMenuItem,
            this.scriptStatisticsToolStripMenuItem,
            this.searchToolStripMenuItem});
			this.utilsToolStripMenuItem.Name = "utilsToolStripMenuItem";
			this.utilsToolStripMenuItem.Size = new System.Drawing.Size(44, 20);
			this.utilsToolStripMenuItem.Text = "Tools";
			// 
			// checkValidToolStripMenuItem
			// 
			this.checkValidToolStripMenuItem.Name = "checkValidToolStripMenuItem";
			this.checkValidToolStripMenuItem.Size = new System.Drawing.Size(158, 22);
			this.checkValidToolStripMenuItem.Text = "Check Valid";
			this.checkValidToolStripMenuItem.Click += new System.EventHandler(this.checkValidToolStripMenuItem_Click);
			// 
			// scriptStatisticsToolStripMenuItem
			// 
			this.scriptStatisticsToolStripMenuItem.Name = "scriptStatisticsToolStripMenuItem";
			this.scriptStatisticsToolStripMenuItem.Size = new System.Drawing.Size(158, 22);
			this.scriptStatisticsToolStripMenuItem.Text = "Script Statistics";
			this.scriptStatisticsToolStripMenuItem.Click += new System.EventHandler(this.scriptStatisticsToolStripMenuItem_Click);
			// 
			// searchToolStripMenuItem
			// 
			this.searchToolStripMenuItem.Name = "searchToolStripMenuItem";
			this.searchToolStripMenuItem.Size = new System.Drawing.Size(158, 22);
			this.searchToolStripMenuItem.Text = "Search";
			this.searchToolStripMenuItem.Click += new System.EventHandler(this.searchToolStripMenuItem_Click);
			// 
			// infoToolStripMenuItem1
			// 
			this.infoToolStripMenuItem1.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.showTransitionPredicateToolStripMenuItem,
            this.showLastMoverReportToolStripMenuItem,
            this.showLastErrorTraceToolStripMenuItem,
            this.showLoopInformationToolStripMenuItem,
            this.copySelectedAtomicCodeToolStripMenuItem});
			this.infoToolStripMenuItem1.Name = "infoToolStripMenuItem1";
			this.infoToolStripMenuItem1.Size = new System.Drawing.Size(39, 20);
			this.infoToolStripMenuItem1.Text = "Info";
			// 
			// showTransitionPredicateToolStripMenuItem
			// 
			this.showTransitionPredicateToolStripMenuItem.Name = "showTransitionPredicateToolStripMenuItem";
			this.showTransitionPredicateToolStripMenuItem.Size = new System.Drawing.Size(209, 22);
			this.showTransitionPredicateToolStripMenuItem.Text = "Show Transition Predicate";
			this.showTransitionPredicateToolStripMenuItem.Click += new System.EventHandler(this.showTransitionPredicateToolStripMenuItem_Click);
			// 
			// showLastMoverReportToolStripMenuItem
			// 
			this.showLastMoverReportToolStripMenuItem.Name = "showLastMoverReportToolStripMenuItem";
			this.showLastMoverReportToolStripMenuItem.Size = new System.Drawing.Size(209, 22);
			this.showLastMoverReportToolStripMenuItem.Text = "Show Last Mover Report";
			this.showLastMoverReportToolStripMenuItem.Click += new System.EventHandler(this.showLastMoverReportToolStripMenuItem_Click);
			// 
			// showLastErrorTraceToolStripMenuItem
			// 
			this.showLastErrorTraceToolStripMenuItem.Name = "showLastErrorTraceToolStripMenuItem";
			this.showLastErrorTraceToolStripMenuItem.Size = new System.Drawing.Size(209, 22);
			this.showLastErrorTraceToolStripMenuItem.Text = "Show Last Error Trace";
			this.showLastErrorTraceToolStripMenuItem.Click += new System.EventHandler(this.showLastErrorTraceToolStripMenuItem_Click);
			// 
			// showLoopInformationToolStripMenuItem
			// 
			this.showLoopInformationToolStripMenuItem.Name = "showLoopInformationToolStripMenuItem";
			this.showLoopInformationToolStripMenuItem.Size = new System.Drawing.Size(209, 22);
			this.showLoopInformationToolStripMenuItem.Text = "Show Loop Information";
			this.showLoopInformationToolStripMenuItem.Click += new System.EventHandler(this.showLoopInformationToolStripMenuItem_Click);
			// 
			// copySelectedAtomicCodeToolStripMenuItem
			// 
			this.copySelectedAtomicCodeToolStripMenuItem.Name = "copySelectedAtomicCodeToolStripMenuItem";
			this.copySelectedAtomicCodeToolStripMenuItem.Size = new System.Drawing.Size(209, 22);
			this.copySelectedAtomicCodeToolStripMenuItem.Text = "Copy Atomic Code";
			this.copySelectedAtomicCodeToolStripMenuItem.Click += new System.EventHandler(this.copySelectedAtomicCodeToolStripMenuItem_Click);
			// 
			// viewToolStripMenuItem
			// 
			this.viewToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.viewLogToolStripMenuItem,
            this.clearConsoleToolStripMenuItem,
            this.changeTextFontToolStripMenuItem});
			this.viewToolStripMenuItem.Name = "viewToolStripMenuItem";
			this.viewToolStripMenuItem.Size = new System.Drawing.Size(41, 20);
			this.viewToolStripMenuItem.Text = "View";
			// 
			// viewLogToolStripMenuItem
			// 
			this.viewLogToolStripMenuItem.Name = "viewLogToolStripMenuItem";
			this.viewLogToolStripMenuItem.Size = new System.Drawing.Size(184, 22);
			this.viewLogToolStripMenuItem.Text = "View Log";
			this.viewLogToolStripMenuItem.Click += new System.EventHandler(this.viewLogToolStripMenuItem_Click);
			// 
			// clearConsoleToolStripMenuItem
			// 
			this.clearConsoleToolStripMenuItem.Name = "clearConsoleToolStripMenuItem";
			this.clearConsoleToolStripMenuItem.Size = new System.Drawing.Size(184, 22);
			this.clearConsoleToolStripMenuItem.Text = "Clear Console";
			// 
			// changeTextFontToolStripMenuItem
			// 
			this.changeTextFontToolStripMenuItem.Name = "changeTextFontToolStripMenuItem";
			this.changeTextFontToolStripMenuItem.Size = new System.Drawing.Size(184, 22);
			this.changeTextFontToolStripMenuItem.Text = "Change Text Font...";
			this.changeTextFontToolStripMenuItem.Click += new System.EventHandler(this.changeTextFontToolStripMenuItem_Click);
			// 
			// tab_Panel
			// 
			this.tab_Panel.Dock = System.Windows.Forms.DockStyle.Fill;
			this.tab_Panel.Location = new System.Drawing.Point(0, 0);
			this.tab_Panel.Name = "tab_Panel";
			this.tab_Panel.SelectedIndex = 0;
			this.tab_Panel.Size = new System.Drawing.Size(658, 763);
			this.tab_Panel.TabIndex = 29;
			// 
			// QETGui
			// 
			this.AutoScaleBaseSize = new System.Drawing.Size(5, 13);
			this.ClientSize = new System.Drawing.Size(1228, 763);
			this.Controls.Add(this.tab_Panel);
			this.Controls.Add(this.panel_right);
			this.Icon = ((System.Drawing.Icon)(resources.GetObject("$this.Icon")));
			this.Name = "QETGui";
			this.StartPosition = System.Windows.Forms.FormStartPosition.CenterScreen;
			this.Text = "QED";
			this.Load += new System.EventHandler(this.QETGui_Load);
			this.panel_right.ResumeLayout(false);
			this.panel_right.PerformLayout();
			this.panel_command.ResumeLayout(false);
			this.panel_buttons.ResumeLayout(false);
			this.tab_ControlPanel.ResumeLayout(false);
			this.tabPage4.ResumeLayout(false);
			this.tabPage4.PerformLayout();
			this.tabPage1.ResumeLayout(false);
			this.tabPage2.ResumeLayout(false);
			this.tabPage3.ResumeLayout(false);
			this.tabPage5.ResumeLayout(false);
			this.tabPage5.PerformLayout();
			this.tabPage6.ResumeLayout(false);
			this.tabPage6.PerformLayout();
			this.menuStrip1.ResumeLayout(false);
			this.menuStrip1.PerformLayout();
			this.ResumeLayout(false);

		}

		void txt_Command_LostFocus(object sender, EventArgs e)
		{
			if (txt_Command.Text.Trim() == "")
			{
				txt_Command.Text = "Write the proof command here...";
			}
		}

		void txt_Command_GotFocus(object sender, EventArgs e)
		{
			if (txt_Command.Text.Trim() == "Write the proof command here...")
			{
				txt_Command.Text = "";
			}
		}
		#endregion

		public void QetStart() {
			ExternalProcess.Run(ExternalProcess.HOME + "\\QETApp.exe", config_file_name, current_textbox_stream);
		}

        //----------------------------------------------------------
        //----------------------------------------------------------
        // Global variables

		protected string config_file_name = null;
        protected string script_file_name = null;
        protected string program_file_name = null;

        protected Configuration config = null;

        protected bool commandFromList = false;

        protected Verifier verifier = null;
        protected ProofScript proofScript = null;

		protected TextBoxStream current_textbox_stream = null;

        protected RichTextBox currentProgramTextBox;
        protected RichTextBox inputProgramTextBox;
        protected TabPage programTabPage;
        protected TabPage editorTabPage;

        protected Microsoft.Glee.GraphViewerGdi.GViewer viewer;
        protected ToolTip viewerTip;

        protected Node selectedNode = null;

        protected Font textFont = new System.Drawing.Font("Courier New", 9F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(162)));

        //----------------------------------------------------------
        //----------------------------------------------------------

        private void btn_LoadConfFile_Click(object sender, System.EventArgs e) {
			// Show the open file dialog
			OpenFileDialog ofd = new OpenFileDialog();
			ofd.Title = "Select a configuration file";
			ofd.Filter = "Configuration Files (*.conf)|*.conf";
			ofd.InitialDirectory = WorkingDir;
			if (ofd.ShowDialog() == DialogResult.OK) {
                config_file_name = ofd.FileName; // ofd.FileName.Substring(ofd.FileName.LastIndexOf("\\") + 1);

                LoadConfig(config_file_name, null);
			}
		}

        private void LoadConfig(string configfile, string bplfile){
            config_file_name = configfile;
            
            // parse the config
            config = new Configuration(configfile == null ? null : new string[] { configfile });

            Output.ApplyConfiguration(config);
            Statistics.ApplyConfiguration(config);

            verifier = new Verifier(config);

            string scriptfile = config.GetStr("Input", "ScriptFile");
            if (scriptfile != null)
            {
                LoadScriptFile(scriptfile);
            }
            else
            {
                ResetScriptFile();
            }

            string programfile = config.GetStr("Input", "BplFile", bplfile);
            if (programfile != null)
            {
                LoadProgram(programfile);
            }

            CheckOutHistory();

            lst_Commands.Items.Clear();

            // get the command usages
            cmb_commands.Items.Clear();
            cmb_commands.Items.Add("-- Available Proof Commands --");
            cmb_commands.Sorted = true;
            cmb_commands.Items.AddRange(CmdFactory.AvailableCommands.ToArray());
            cmb_commands.SelectedIndex = 0;
        }

        private void LoadScriptFile(string filename)
        {
            Debug.Assert(filename != null);
            script_file_name = filename;

            proofScript = ProofScript.Parse(filename);

            LoadScript(proofScript);
        }

        private void LoadScript(ProofScript proofScript)
        {
            lst_Script.Items.Clear();
            txt_Command.Text = "";

            foreach (ProofCommand command in proofScript)
            {
                lst_Script.Items.Add(command);
            }

            if (proofScript.Count > 0)
            {
                lst_Script.SelectedIndex = 0;
                SelectCommandFromList(lst_Script);
            }
        }

        private void ResetScriptFile()
        {
            if (script_file_name != null)
            {
                lst_Script.Items.Clear();
                txt_Command.Text = "";
                LoadScriptFile(script_file_name);
            }
            else
            {
                proofScript = new ProofScript("");
            }
        }

        private void LoadProgram(string filename)
        {
            Debug.Assert(filename != null);

            program_file_name = filename;

            // todo: get rid of CommandLineOptions
            CommandLineOptions.Clo.Files.Clear();
            string[] filenames = filename.Split(new char[] { ',' }, StringSplitOptions.RemoveEmptyEntries);
            foreach (string fname in filenames)
            {
                CommandLineOptions.Clo.Files.Add(fname.Trim());
            }

            // config.Set("Input", "LoadPrelude", (MessageBox.Show("Load prelude?", "QED", MessageBoxButtons.YesNo) == DialogResult.Yes));

            if (!verifier.LoadProgram())
            {
                return;
            }

            AfterLoadProgram();
        }

        private void AfterLoadProgram()
        {
            CheckOutHistory();

            if (proofScript == null)
            {
                ResetScriptFile();
            }

            DisplayProgram();

            txt_ProofState.Text = verifier.ProofState.CurrentStateInfo();

            txt_Statistics.Text = Util.ToGuiString(Statistics.Print());
        }

        private void CheckOutHistory()
        {
            lst_history.Items.Clear();
            foreach (HistoryItem item in verifier.history)
            {
                lst_history.Items.Add(item);
            }
            if (verifier.history.CurrentIndex >= 0)
            {
                lst_history.SelectedIndex = verifier.history.CurrentIndex;
            }
        }


        private void ColorTextBox(RichTextBox txtBox)
        {
            if (!verifier.config.GetBool("View", "ColorCode", false))
            {
                txtBox.SelectAll();
                txtBox.SelectionColor = System.Drawing.Color.Black;
                txtBox.SelectionStart = 0;
                txtBox.SelectionLength = 0; 
                return;
            }

            txtBox.BackColor = System.Drawing.Color.WhiteSmoke;
            
            System.Drawing.Color color = System.Drawing.Color.Black;

            // color everything to black
            txtBox.SelectionStart = 0;
            txtBox.SelectionLength = txtBox.Text.Length;
            txtBox.SelectionColor = color;
            
            int start = 0;
            int found = 0;

            foreach (string keyword in TextHighligtingOptions.ColorOptions.Keys)
            {
                color = TextHighligtingOptions.ColorOptions[keyword];

                start = 0;
                found = 0;
                while (found >= 0 && start < txtBox.Text.Length)
                {
                    found = txtBox.Find(keyword, start, RichTextBoxFinds.WholeWord | RichTextBoxFinds.MatchCase);
                    if (found >= 0)
                    {
                        txtBox.SelectionStart = found;
                        txtBox.SelectionLength = keyword.Length;
                        txtBox.SelectionColor = color;
                        start = found + keyword.Length;
                    }
                }
            }

            color = TextHighligtingOptions.charSetColor;

            start = 0;
            found = 0;
            while (found >= 0 && start < txtBox.Text.Length)
            {
                found = txtBox.Find(TextHighligtingOptions.charSet, start);
                if (found >= 0)
                {
                    txtBox.SelectionStart = found;
                    txtBox.SelectionLength = 1;
                    txtBox.SelectionColor = color;
                    start = found + 1;
                }
            }

            txtBox.SelectionStart = 0;
            txtBox.SelectionLength = 0;
        }

       
        private void DisplayProgram()
        {
            HistoryItem item = verifier.history.Current;
            
            if (item != null)
            {

                tab_Panel.Controls.Clear();

                List<myGraph> glist = item.graphs;

                this.SuspendLayout();

                //-------------------------------

                if (programTabPage == null)
                {
                    programTabPage = new TabPage("Current program");
                    currentProgramTextBox = new RichTextBox();
                    currentProgramTextBox.Dock = System.Windows.Forms.DockStyle.Fill;
                    currentProgramTextBox.Multiline = true;
                    currentProgramTextBox.Font = textFont;
                    currentProgramTextBox.ScrollBars = System.Windows.Forms.RichTextBoxScrollBars.Both;
                    currentProgramTextBox.WordWrap = false;

                    programTabPage.Controls.Add(currentProgramTextBox);
                }

                currentProgramTextBox.Text = CheckAddLineNumbers(item.program, true);
                ColorTextBox(currentProgramTextBox);
                tab_Panel.Controls.Add(programTabPage);

                //------------------------------

                if (editorTabPage == null)
                {
                    editorTabPage = new TabPage(program_file_name.Substring(program_file_name.LastIndexOf("\\") + 1));
                    inputProgramTextBox = new RichTextBox();
                    inputProgramTextBox.Dock = System.Windows.Forms.DockStyle.Fill;
                    inputProgramTextBox.Multiline = true;
                    inputProgramTextBox.Font = textFont;
                    inputProgramTextBox.ScrollBars = System.Windows.Forms.RichTextBoxScrollBars.Both;
                    inputProgramTextBox.WordWrap = false;
                    
                    string lines = Util.ReadFromFile(program_file_name);
                    inputProgramTextBox.Text = CheckAddLineNumbers(lines, true);
                    ColorTextBox(inputProgramTextBox);
                    editorTabPage.Controls.Add(inputProgramTextBox);
                }

                tab_Panel.Controls.Add(editorTabPage);

                //------------------------------

                if (verifier.config.GetBool("View", "ShowBlockCFG", false))
                {
                    foreach (myGraph g in glist)
                    {
                        TabPage tp = new TabPage(g.Name);

                        //create a viewer object
                        viewer = new Microsoft.Glee.GraphViewerGdi.GViewer();
                        viewer.Graph = GraphTranslator.Translate(g);
                        //associate the viewer with the form
                        viewer.Dock = System.Windows.Forms.DockStyle.Fill;
                        //viewer.SelectionChanged += new System.EventHandler(this.graph_Viewer_SelectionChanged);
                        viewer.Click += new System.EventHandler(this.graph_Viewer_SelectionChanged);

                        viewerTip = new ToolTip();
                        viewerTip.InitialDelay = 0;
                        viewerTip.AutomaticDelay = 1000;
                        viewerTip.AutoPopDelay = 10000;

                        tp.Controls.Add(viewer);

                        tab_Panel.Controls.Add(tp);
                    }
                }

                //------------------------------

                // show the history's statistics
                Debug.Assert(item.statistics != null);
                txt_Statistics.Text = Util.ToGuiString(item.statistics);

                //------------------------------
                
                this.ResumeLayout();
            }
        }

        private string CheckAddLineNumbers(string s, bool output_rn)
        {
            return config.GetBool("View", "LineNumbers", false) ? Util.AddLineNumbers(s, output_rn) : s;
        }

        private string CheckRemoveLineNumbers(string s, bool output_rn)
        {
            return config.GetBool("View", "LineNumbers", false) ? Util.RemoveLineNumbers(s, output_rn) : s;
        }

        private List<string> ReadLinesFromFile(string filename) {
            return Util.ReadLinesFromFile(filename);
        }

        private void WriteLinesToFile(string filename, List<string> lines)
        {
            Util.WriteLinesToFile(filename, lines);
        }

        private void WriteToFile(string filename, string lines)
        {
            Util.WriteToFile(filename, lines);
        }

		private void btn_run_qet_Click(object sender, System.EventArgs e) {
            ThreadStart start = new ThreadStart(this.QetStart);
			Thread thr = new Thread(start);
			thr.Start();
		}

		private void btn_kill_Click(object sender, System.EventArgs e) {
			ExternalProcess.KillCurrentProcess();
			current_textbox_stream.WriteLine();
			current_textbox_stream.WriteLine("Killed current process");
			current_textbox_stream.WriteLine();
		}

        private void QETGui_Load(object sender, EventArgs e)
        {
            // we should have at least one config
            config = new Configuration();

            ExternalProcess.Init(Environment.CurrentDirectory);

            // redirect output to the text box
            current_textbox_stream = new TextBoxStream(this.txt_Output);

            Console.SetOut(current_textbox_stream);
            Output.Target = current_textbox_stream;

            // load the default configuration
            LoadConfig("qed_default.conf", null);

            Form.CheckForIllegalCrossThreadCalls = false;
        }
        
        private void btn_To_Console_Click(object sender, EventArgs e)
        {
            // todo implement
        }

        private void btn_LoadScript_Click(object sender, EventArgs e)
        {
            // Show the open file dialog
            OpenFileDialog ofd = new OpenFileDialog();
            ofd.Title = "Select a script file";
            ofd.Filter = "Script Files (*.qet)|*.qet";
            ofd.InitialDirectory = WorkingDir;
            if (ofd.ShowDialog() == DialogResult.OK)
            {
                script_file_name = ofd.FileName; // ofd.FileName.Substring(ofd.FileName.LastIndexOf("\\") + 1);

                LoadScriptFile(script_file_name);
            }
        }

        private void btn_SaveScript_Click(object sender, EventArgs e)
        {
            // Show the open file dialog
            SaveFileDialog ofd = new SaveFileDialog();
            ofd.Title = "Select a script file";
            ofd.Filter = "Script Files (*.qet)|*.qet";
            ofd.InitialDirectory = WorkingDir;
            if (ofd.ShowDialog() == DialogResult.OK)
            {
                script_file_name = ofd.FileName; // ofd.FileName.Substring(ofd.FileName.LastIndexOf("\\") + 1);

                using (StreamWriter writer = new StreamWriter(script_file_name))
                {
                    foreach (ProofCommand command in lst_Script.Items)
                    {
                        writer.WriteLine(command.ToString());
                    }
                }
            }            
        }

        //Semaphore semRunCmd = new Semaphore(1, 1); 

        public void RunCommand()
        {
            //semRunCmd.WaitOne();

            this.RunCommandThreadProc();

            //ThreadStart start = new ThreadStart(this.RunCommandThreadProc);
            //Thread thr = new Thread(start);
            //thr.Start();
        }

        private void RunCommandThreadProc()
        {
            ProofCommand command = null;
            try
            {
                if (txt_Command.Text == "")
                {
                    MessageBox.Show("Command text is empty! Please select a command!");
                }
                else
                {
                    string commandStr = CurrentCommandStr();

                    command = ProofScript.ParseCommand(commandStr);
                    if (command != null)
                    {
                        //---------------
                        verifier.RunProofCommand(command);

                        //---------------
                        // updates on the gui after each command execution
                        CheckOutHistory();
                        DisplayProgram();
                        // add command to command history
                        lst_Commands.Items.Add(command);
                        // refresh proof state
                        txt_ProofState.Text = verifier.ProofState.CurrentStateInfo();
                        // refresh statistics
                        txt_Statistics.Text = Util.ToGuiString(Statistics.Print());
                        //---------------

                        // if auto-save option is chosen, then sutosave the executed commands
                        if (verifier.config.GetBool("Script", "AutoSave", false))
                        {
                            SaveCommandHistory(script_file_name, false);
                        }

                        if (verifier.config.GetBool("", "AutoSave", false))
                        {
                            SaveConfiguration(config_file_name);
                        }
                    }
                    else
                    {
                        MessageBox.Show("Command is wrong: " + txt_Command.Text);
                    }
                }
            }
            catch (Exception e)
            {
                if (command != null) { Output.AddError("GUI: Error while running the command " + command.ToString()); }
                Output.Add(e);
            }
            finally
            {
                BoogiePL.Errors.count = 0;

                txt_Command.Focus();

                this.Refresh();

                //semRunCmd.Release(1);
            }

        }

        private void btn_RunNext_Click(object sender, EventArgs e)
        {
            RunCommand();
            if (commandFromList)
            {
                SelectNextCommandFromList();
            }
        }

        private void runEntireScriptToolStripMenuItem_Click(object sender, EventArgs e)
        {
            SelectCommandFromList(lst_Script);
            do
            {
                RunCommand();

            } while (SelectNextCommandFromList());
        }

        private void lst_Script_DoubleClick(object sender, EventArgs e)
        {
            if (lst_Script.Items.Count > 0 && lst_Script.SelectedIndex >= 0)
            {
                ProofCommand command = (ProofCommand)lst_Script.SelectedItem;

                txt_Command.Text = command.ToString();

                commandFromList = true;

                RunCommand();

                SelectNextCommandFromList();
            }
        }

        private void lst_Script_KeyPressed(object sender, KeyEventArgs e)
        {
            if (lst_Script.Items.Count > 0 && lst_Script.SelectedIndex >= 0)
            {
                if (e.KeyCode == Keys.Delete)
                {
                    proofScript.RemoveCommand((ProofCommand)lst_Script.SelectedItem); // ! this should go first
                    lst_Script.Items.Remove(lst_Script.SelectedItem);
                }
            }
        }


        private void btn_LoadProgram_Click(object sender, EventArgs e)
        {
            // Show the open file dialog
            OpenFileDialog ofd = new OpenFileDialog();
            ofd.Title = "Select a BoogiePL file";
            ofd.Filter = "BPL Files (*.bpl)|*.bpl";
            ofd.InitialDirectory = WorkingDir;
            if (ofd.ShowDialog() == DialogResult.OK)
            {
                program_file_name = ofd.FileName; // ofd.FileName.Substring(ofd.FileName.LastIndexOf("\\") + 1);

                LoadProgram(program_file_name);
            }
        }

        private void setHomeToolStripMenuItem_Click(object sender, EventArgs e)
        {
            // Show the open file dialog
            FolderBrowserDialog ofd = new FolderBrowserDialog();
            ofd.SelectedPath = Environment.CurrentDirectory;
            if (ofd.ShowDialog() == DialogResult.OK)
            {
                WorkingDir = (string)ofd.SelectedPath;
                ExternalProcess.Init(WorkingDir);
                
                Output.AddLine("Home directory set to " + WorkingDir);
            }	
        }

        private void loadConfigurationToolStripMenuItem_Click(object sender, EventArgs e)
        {
            // Show the open file dialog
            OpenFileDialog ofd = new OpenFileDialog();
            ofd.Title = "Select a configuration file";
            ofd.Filter = "Configuration Files (*.conf)|*.conf";
            ofd.InitialDirectory = WorkingDir;
            if (ofd.ShowDialog() == DialogResult.OK)
            {
                config_file_name = ofd.FileName; // ofd.FileName.Substring(ofd.FileName.LastIndexOf("\\") + 1);

                WorkingDir = ofd.FileName.Substring(0, ofd.FileName.LastIndexOf("\\"));
                ExternalProcess.Init(WorkingDir);
                
                Output.AddLine("Home directory set to " + WorkingDir);
                
                LoadConfig(config_file_name, null);
            }
        }

        private void SaveConfiguration(string filename)
        {

            if (filename == null)
            {
                // Show the open file dialog
                SaveFileDialog ofd = new SaveFileDialog();
                ofd.Title = "Select a configuration file";
                ofd.Filter = "Configuration Files (*.conf)|*.conf";
                ofd.InitialDirectory = WorkingDir;
                if (ofd.ShowDialog() == DialogResult.OK)
                {
                    filename = ofd.FileName; // ofd.FileName.Substring(ofd.FileName.LastIndexOf("\\") + 1);
                }
                else
                {
                    return;
                }
            }

            using (StreamWriter writer = new StreamWriter(filename))
            {
                writer.WriteLine(verifier.config.Print());
            }
        }

        private void loadProgramToolStripMenuItem_Click(object sender, EventArgs e)
        {
            // Show the open file dialog
            OpenFileDialog ofd = new OpenFileDialog();
            ofd.Title = "Select a BoogiePL file";
            ofd.Filter = "BPL Files (*.bpl)|*.bpl";
            ofd.InitialDirectory = WorkingDir;
            if (ofd.ShowDialog() == DialogResult.OK)
            {
                program_file_name = ofd.FileName; // ofd.FileName.Substring(ofd.FileName.LastIndexOf("\\") + 1);

                if (config_file_name == null)
                {
                    LoadConfig(null, program_file_name);
                }
                else 
                {
                    LoadProgram(program_file_name);
                }
            }
        }

        private void loadScriptToolStripMenuItem_Click(object sender, EventArgs e)
        {
            // Show the open file dialog
            OpenFileDialog ofd = new OpenFileDialog();
            ofd.Title = "Select a script file";
            ofd.Filter = "Script Files (*.qet)|*.qet";
            ofd.InitialDirectory = WorkingDir;
            if (ofd.ShowDialog() == DialogResult.OK)
            {
                script_file_name = ofd.FileName; // ofd.FileName.Substring(ofd.FileName.LastIndexOf("\\") + 1);

                LoadScriptFile(script_file_name);
            }
        }

        private void saveScriptToolStripMenuItem_Click(object sender, EventArgs e)
        {
            // Show the open file dialog
            SaveFileDialog ofd = new SaveFileDialog();
            ofd.Title = "Select a script file";
            ofd.Filter = "Script Files (*.qet)|*.qet";
            ofd.InitialDirectory = WorkingDir;
            if (ofd.ShowDialog() == DialogResult.OK)
            {
                script_file_name = ofd.FileName; // ofd.FileName.Substring(ofd.FileName.LastIndexOf("\\") + 1);

                using (StreamWriter writer = new StreamWriter(script_file_name))
                {
                    foreach (ProofCommand command in lst_Script.Items)
                    {
                        writer.WriteLine(command.ToString());
                    }
                }

                // LoadScriptFile(script_file_name);
            }         
        }

        /*
         * The below code is not supposed to be used
        private void runQETToolStripMenuItem_Click(object sender, EventArgs e)
        {
            ThreadStart start = new ThreadStart(this.QetStart);
            Thread thr = new Thread(start);
            thr.Start();
        }

        private void killProcessToolStripMenuItem_Click(object sender, EventArgs e)
        {
            ExternalProcess.KillCurrentProcess();
            current_textbox_stream.WriteLine();
            current_textbox_stream.WriteLine("Killed current process");
            current_textbox_stream.WriteLine();
        }
         */

        private void exitQETToolStripMenuItem_Click(object sender, EventArgs e)
        {
            Environment.Exit(0);
        }

        private void btn_DeleteCommand_Click(object sender, EventArgs e)
        {
            if (lst_Script.Items.Count > 0)
            {
                proofScript.RemoveCommand((ProofCommand)lst_Script.SelectedItem);
                lst_Script.Items.Remove(lst_Script.SelectedItem);
            }
        }

        private void SelectCommandFromList(ListBox lstBox)
        {
            if (lstBox.SelectedItems != null && lstBox.SelectedItems.Count > 0)
            {
                ProofCommand command = (ProofCommand)lstBox.SelectedItems[0];

                txt_Command.Text = command.ToString();

                for (int i = 1; i < lstBox.SelectedItems.Count; ++i)
                {
                    command = (ProofCommand)lstBox.SelectedItems[i];

                    txt_Command.Text = txt_Command.Text + ";\r\n" + command.ToString();
                }

                commandFromList = true;
            }
        }

        private bool SelectNextCommandFromList()
        {
            bool result = false;

            if (lst_Script.SelectedIndex < (lst_Script.Items.Count - 1))
            {
                int i = lst_Script.SelectedIndex;
                lst_Script.SelectedIndices.Clear();
                lst_Script.SelectedIndex = i + 1;
                result = true;
            }
            else
            {
                Output.AddLine("Proof script ended!");
                lst_Script.SelectedIndices.Clear();
                lst_Script.SelectedIndex = 0;
                result = false;
            }
            SelectCommandFromList(lst_Script);
            return result;
        }

        private void txt_Command_TextChanged(object sender, EventArgs e)
        {
            commandFromList = false;
        }

        private void txt_Command_KeyPressed(object sender, KeyEventArgs e)
        {
            if (e.KeyCode == Keys.Enter && e.Shift)
            {
                commandFromList = false;

                RunCommand();

                e.Handled = true;
            }
        }

        private void btn_mover_Click(object sender, EventArgs e)
        {
            string label = InputBox.Show("mover", "Enter the labels of the atomic blocks (\"*\" for all):", "*");

            if (label == null)
            {
                return;
            }

            txt_Command.Text = "mover " + label;

            commandFromList = false;

            RunCommand();
        }

        private void btn_merge_Click(object sender, EventArgs e)
        {
            txt_Command.Text = "merge";

            if (MessageBox.Show("Repetitive application ?", "merge",
                                MessageBoxButtons.YesNo, MessageBoxIcon.Question)
                == DialogResult.Yes)
            {
                txt_Command.Text += " *";
            }

            commandFromList = false;

            RunCommand();
        }

        private void btn_reduce_Click(object sender, EventArgs e)
        {
            txt_Command.Text = "reduce";

            commandFromList = false;

            RunCommand();
        }

        private void btn_refine_mutex_Click(object sender, EventArgs e)
        {

            string auxVarName = InputBox.Show("refine mutex", "Enter the name of the auxiliary variable:");

            if (auxVarName == null)
            {
                return;
            }

            string syncPred = InputBox.Show("refine mutex", "Enter the synchronization predicate:");

            if (syncPred == null)
            {
                return;
            }

            txt_Command.Text = "refine mutex " + auxVarName + " " + syncPred;

            commandFromList = false;

            RunCommand();
        }

        private void btn_refine_progress_Click(object sender, EventArgs e)
        {
            string auxVarName = InputBox.Show("refine progress", "Enter the name of the auxiliary variable:");

            if (auxVarName == null)
            {
                return;
            }

            string syncPred = InputBox.Show("refine progress", "Enter the synchronization predicates:");

            if (syncPred == null)
            {
                return;
            }

            txt_Command.Text = "refine progress " + auxVarName + " " + syncPred;

            commandFromList = false;

            RunCommand();
        }

        private void btn_refine_rw_Click(object sender, EventArgs e)
        {
            string auxVarName = InputBox.Show("refine rw", "Enter the name of the auxiliary variable:");

            if (auxVarName == null)
            {
                return;
            }

            string syncPredRead = InputBox.Show("refine rw", "Enter the synchronization predicate for read accesses:");

            if (syncPredRead == null)
            {
                return;
            }

            string syncPredWrite = InputBox.Show("refine rw", "Enter the synchronization predicate for write accesses:");

            if (syncPredWrite == null)
            {
                return;
            }

            txt_Command.Text = "refine rw " + auxVarName + " " + syncPredRead + "#" + syncPredWrite;

            commandFromList = false;

            RunCommand();
        }

        private void btn_abstract_Click(object sender, EventArgs e)
        {
            string rw = InputBox.Show("abstract", "Enter the type of the abstraction (r: read, w: write):", "rw");

            if (rw == null)
            {
                return;
            }

            string vars = InputBox.Show("abstract", "Enter the names of the variables");

            if (vars == null)
            {
                return;
            }

            string blocks = InputBox.Show("abstract", "Enter the labels of the atomic blocks (\"*\" for all):", "*");

            if (blocks == null)
            {
                return;
            }

            txt_Command.Text = "abstract " + rw + " " + vars + " " + blocks;

            commandFromList = false;

            RunCommand();
        }

        private void btn_invariant_Click(object sender, EventArgs e)
        {
            string formula = InputBox.Show("invariant", "Enter the invariant formula:");

            if (formula == null)
            {
                return;
            }

            txt_Command.Text = "invariant " + formula;

            commandFromList = false;

            RunCommand();
        }

        private void btn_purify_Click(object sender, EventArgs e)
        {
            txt_Command.Text = "purify";

            commandFromList = false;

            RunCommand();
        }

        private void btn_check_Click(object sender, EventArgs e)
        {

            string label = InputBox.Show("check", "Enter the label of the procedures to check (\"*\" for all):", "*");

            if (label == null)
            {
                return;
            }
            
            txt_Command.Text = "check " + label;

            commandFromList = false;

            RunCommand();
        }

        private void btn_Verify_Click(object sender, EventArgs e)
        {
            string label = InputBox.Show("verify", "Enter the label of the procedures to check (\"*\" for all):", "*");

            if (label == null)
            {
                return;
            }

            txt_Command.Text = "verify " + label;

            commandFromList = false;

            RunCommand();
        }

        private void btn_Clone_Click(object sender, EventArgs e)
        {
            string blockLabel = InputBox.Show("clone", "Enter the labels of the atomic block to clone", "");

            if (blockLabel == null)
            {
                return;
            }

            string branchLabel = InputBox.Show("clone", "Enter the labels of the atomic block to at the branch", "");

            if (branchLabel == null)
            {
                return;
            }


            txt_Command.Text = "clone " + blockLabel + " " + branchLabel;

            commandFromList = false;

            RunCommand();
        }


        private void resetProofToolStripMenuItem_Click(object sender, EventArgs e)
        {
            ProofState.ResetInstance();
            txt_Output.Text = "";
            LoadConfig(config_file_name, null);
        }

        private void showProofStateToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (verifier != null && verifier.proofState != null)
            {
                MessageBox.Show(verifier.ProofState.CurrentStateInfo(), "Proof State", MessageBoxButtons.OK, MessageBoxIcon.Information);
            }
        }

        private void previousToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (verifier.history.ShiftPrevious())
            {
                if (verifier.history.CurrentIndex != -1)
                {
                    lst_history.SelectedIndex = verifier.history.CurrentIndex;
                }
                DisplayProgram();
            }
        }

        private void nextToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (verifier.history.ShiftNext())
            {
                if (verifier.history.CurrentIndex != -1)
                {
                    lst_history.SelectedIndex = verifier.history.CurrentIndex;
                }
                DisplayProgram();
            }
        }

        private void firstToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (verifier.history.ShiftFirst())
            {
                if (verifier.history.CurrentIndex != -1)
                {
                    lst_history.SelectedIndex = verifier.history.CurrentIndex;
                }
                DisplayProgram();
            }
        }

        private void lastToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (verifier.history.ShiftLast())
            {
                if (verifier.history.CurrentIndex != -1)
                {
                    lst_history.SelectedIndex = verifier.history.CurrentIndex;
                }
                DisplayProgram();
            }
        }

        private void lst_history_DoubleClick(object sender, EventArgs e)
        {
            if (lst_history.Items.Count > 0 && lst_history.SelectedIndex >= 0)
            {
                int index = lst_history.SelectedIndex;
                verifier.history.Shift(index);

                if (index == 0)
                {
                    LoadProgram(program_file_name);
                }
                else
                {
                    // save history
                    HistoryItem hitem = verifier.history.Current;
                    StringBuilder strb = new StringBuilder();
                    strb.AppendLine("/*").AppendLine(hitem.ToString()).AppendLine("*/");
                    strb.AppendLine(hitem.program);

                    string filename = WorkingDir + "\\qed_history.bpl";

                    WriteToFile(filename, strb.ToString());

                    // load history
                    LoadProgram(filename);
                }
            }
        }

        private void showConfigurationToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (verifier == null || verifier.config == null)
            {
                MessageBox.Show(this, "No configuration has been loaded!", "Configuration", MessageBoxButtons.OK, MessageBoxIcon.Asterisk);
                return;
            }
            
            MessageBox.Show(this, verifier.config.Print(), "Configuration", MessageBoxButtons.OK, MessageBoxIcon.Information);
        }

        private void showTransitionPredicateToolStripMenuItem_Click(object sender, EventArgs e)
        {
            string label = InputBox.Show("Show Transition Predicate", "Enter the labels of the atomic blocks (\"*\" for all):", "*");

            if (label == null)
            {
                return;
            }

            List<APLBlock> aplBlocks = new List<APLBlock>();

            if (label == "" || label.StartsWith("*"))
            {
                List<AtomicBlock> atomicBlocks = verifier.proofState.AtomicBlocks;
                foreach (AtomicBlock atomicBlock in atomicBlocks)
                {
                    aplBlocks.Add(atomicBlock);
                }
            }
            else
            {
                string[] labels = label.Split(new char[] { ',' }, StringSplitOptions.RemoveEmptyEntries);
                foreach (string item in labels)
                {
                    aplBlocks.Add(verifier.proofState.GetAPLBlockByLabel(item));
                }
            }

            StringBuilder strb = new StringBuilder();

            foreach (APLBlock aplBlock in aplBlocks)
            {
                strb.Append(aplBlock.Label).Append(" : ").AppendLine(Output.ToString(aplBlock.TransitionPredicate));
            }

            MessageBox.Show(this, strb.ToString(), "Transition Predicates", MessageBoxButtons.OK);
        }

        private void lst_Commands_DoubleClicked(object sender, EventArgs e)
        {
            if (lst_Commands.Items.Count > 0 && lst_Commands.SelectedIndex >= 0)
            {
                ProofCommand command = (ProofCommand)lst_Commands.SelectedItem;
                
                txt_Command.Text = command.ToString();

                commandFromList = false;

                RunCommand();
            }
        }

        private void lst_Commands_KeyPressed(object sender, KeyEventArgs e)
        {
            if (lst_Commands.Items.Count > 0 && lst_Commands.SelectedIndex >= 0)
            {
                if (e.KeyCode == Keys.Delete)
                {
                    lst_Commands.Items.Remove(lst_Commands.SelectedItem);
                }
            }
        }

        private void lst_history_KeyPressed(object sender, KeyEventArgs e)
        {
            if (lst_history.Items.Count > 0 && lst_history.SelectedIndex >= 0)
            {
                if (e.KeyCode == Keys.Delete)
                {
                    verifier.history.RemoveAt(lst_history.SelectedIndex); // ! this should go first
                    lst_history.Items.Remove(lst_history.SelectedItem);
                }
            }
        }

        private void btn_InsertCommand_Click(object sender, EventArgs e)
        {
            ProofCommand command = ProofScript.ParseCommand(txt_Command.Text);

            if (lst_Script.Items.Count > 0)
            {
                int index = lst_Script.SelectedIndex + 1;
                lst_Script.Items.Insert(index, command);
                proofScript.InsertCommand(index, command);
            }
            else
            {
                lst_Script.Items.Add(command);
                proofScript.AddCommand(command);
            }
        }

        private void showStatisticsToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (verifier != null && verifier.proofState != null)
            {
                MessageBox.Show(Util.ToGuiString(Statistics.Print()), "Statistics", MessageBoxButtons.OK, MessageBoxIcon.Information);
            }
        }

        private void btn_Cleanup_Click(object sender, EventArgs e)
        {
            string label = InputBox.Show("cleanup", "Enter the names of the auxiliary variables:");

            if (label == null)
            {
                return;
            }

            txt_Command.Text = "cleanup " + label;

            commandFromList = false;

            RunCommand();
        }

        private void btn_TransInv_Click(object sender, EventArgs e)
        {
            string formula = InputBox.Show("transinv", "Enter the transition invariant formula:");

            if (formula == null)
            {
                return;
            }

            txt_Command.Text = "transinv " + formula;

            commandFromList = false;

            RunCommand();
        }

        private void btn_refine_stable_Click(object sender, EventArgs e)
        {
            string auxVarName = InputBox.Show("refine stable", "Enter the name of the auxiliary variable:");

            if (auxVarName == null)
            {
                return;
            }

            string syncPred = InputBox.Show("refine stable", "Enter the synchronization predicate:");

            if (syncPred == null)
            {
                return;
            }

            txt_Command.Text = "refine stable " + auxVarName + " " + syncPred;

            commandFromList = false;

            RunCommand();
        }

        private void lst_Commands_SelectedIndexChanged(object sender, EventArgs e)
        {
            if (lst_Commands.Items.Count > 0 && lst_Commands.SelectedItem != null)
            {
                SelectCommandFromList(lst_Commands);
            }
        }

        private void lst_Script_SelectedIndexChanged(object sender, EventArgs e)
        {
            if (lst_Script.Items.Count > 0 && lst_Script.SelectedItem != null)
            {
                SelectCommandFromList(lst_Script);
            }
        }

        private void saveProgramToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (editorTabPage != null)
            {
                RichTextBox textBox = editorTabPage.Controls[0] as RichTextBox;
                Debug.Assert(textBox != null);
                List<string> lines = new List<string>();
                lines.Add(textBox.Text);
                WriteLinesToFile(program_file_name, lines);
                Output.AddLine("Saved the current program to the file " + program_file_name);
            }
        }

        
        private void graph_Viewer_SelectionChanged(object sender, EventArgs e)
        {
            if (viewer.SelectedObject != null && viewer.SelectedObject is Node)
            {
                if (selectedNode != null)
                {
                    selectedNode.Attr.LineWidth = 1;
                }
                selectedNode = (Node)viewer.SelectedObject;
                APLBlock atomicBlock = (APLBlock)selectedNode.UserData;

                // TODO: uncomment later
                // viewer.SetToolTip(viewerTip, atomicBlock.UniqueLabel + " : " + atomicBlock.Mover.ToString());
                
                selectedNode.Attr.LineWidth = 7;
                viewer.Refresh();

                // let's copy the label to the clipboard
                Util.CopyToClipboard(atomicBlock.Label + "@" + atomicBlock.procState.Name);
            }
        }

        private void saveCommandHistoryToolStripMenuItem_Click(object sender, EventArgs e)
        {
            SaveCommandHistory(null, false);
        }

        private void SaveCommandHistory(string filename, bool append)
        {
            if (filename == null)
            {
                // Show the open file dialog
                SaveFileDialog ofd = new SaveFileDialog();
                ofd.Title = "Select command history";
                ofd.Filter = "Script Files (*.qet)|*.qet";
                ofd.InitialDirectory = WorkingDir;
                if (ofd.ShowDialog() == DialogResult.OK)
                {
                    filename = ofd.FileName; // ofd.FileName.Substring(ofd.FileName.LastIndexOf("\\") + 1);
                }
                else
                {
                    return;
                }
            }

            using (StreamWriter writer = new StreamWriter(filename, append))
            {
                foreach (ProofCommand command in lst_Commands.Items)
                {
                    writer.WriteLine(command.ToString());
                }
            }
        }


        private void btn_reach_Click(object sender, EventArgs e)
        {
            string label = InputBox.Show("reach", "Enter the label of the procedures to check (\"*\" for all):", "*");

            if (label == null)
            {
                return;
            }

            txt_Command.Text = "reach " + label;

            commandFromList = false;

            RunCommand();
        }

        private void btn_loop_Click(object sender, EventArgs e)
        {
            string label = InputBox.Show("loop", "Enter the label of the procedures to check (\"*\" for all):", "*");

            if (label == null)
            {
                return;
            }

            txt_Command.Text = "loop " + label;

            commandFromList = false;

            RunCommand();
        }

        private void showLastErrorTraceToolStripMenuItem_Click(object sender, EventArgs e)
        {
            ErrorTrace errorTrace = verifier.ProofState.LastErrorTrace;
            if (errorTrace != null)
            {
                MessageBox.Show(errorTrace.Report, "Error trace");
            }
        }

        private void btn_localinv_Click(object sender, EventArgs e)
        {
            string procname = InputBox.Show("localinv", "Enter the name of the procedure:");

            if (procname == null)
            {
                return;
            }

            string formula = InputBox.Show("localinv", "Enter the invariant formula:");

            if (formula == null)
            {
                return;
            }

            txt_Command.Text = "localinv " + procname + " " + formula;

            commandFromList = false;

            RunCommand();
        }

        private void showLoopInformationToolStripMenuItem_Click(object sender, EventArgs e)
        {
#if false
             string label = InputBox.Show("Loop Information", "Enter the label of the atomic loop block:");

            if (label == null)
            {
                return;
            }

            LoopBlock loopBlock = verifier.ProofState.GetAtomicBlock(label) as LoopBlock;
            if (loopBlock == null)
            {
                MessageBox.Show("The block is not a loop block!", "Loop Information", MessageBoxButtons.OK, MessageBoxIcon.Error);
                return;
            }

            LoopInfo loopInfo = loopBlock.LoopInfo;

            MessageBox.Show(loopInfo.ToString(), "Loop Information for " + label, MessageBoxButtons.OK, MessageBoxIcon.Information);
#endif
        }

        private void btn_thrlocal_Click(object sender, EventArgs e)
        {
            string procname = InputBox.Show("thrlocal", "Enter the name of the procedure:");

            if (procname == null)
            {
                return;
            }

            string varnames = InputBox.Show("thrlocal", "Enter the name of the variables:");

            if (varnames == null)
            {
                return;
            }

            txt_Command.Text = "thrlocal " + procname + " " + varnames;

            commandFromList = false;

            RunCommand();
        }

        private void checkValidToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (verifier == null || verifier.proofState == null)
            {
                MessageBox.Show("You cannot use the calculator before initializing the proof state!");
                return;
            }

            new Calc(verifier.proofState).Show();

        }

        private void parseResolveTypeCheckProgramToolStripMenuItem_Click(object sender, EventArgs e)
        {
            // Show the open file dialog
            OpenFileDialog ofd = new OpenFileDialog();
            ofd.Title = "Select a BoogiePL file";
            ofd.Filter = "BPL Files (*.bpl)|*.bpl";
            ofd.InitialDirectory = WorkingDir;
            if (ofd.ShowDialog() == DialogResult.OK)
            {
                Output.AddLine("----------- Parse/Resolve/Typecheck " + ofd.FileName + "------------------");

                if (TryLoadProgram(ofd.FileName))
                {
                    MessageBox.Show("The program is successfully parsed/resolved/typechecked !", "Try load program", MessageBoxButtons.OK, MessageBoxIcon.Information);
                }
                else
                {
                    MessageBox.Show("The program failed to parse/resolve/typecheck !", "Try load program", MessageBoxButtons.OK, MessageBoxIcon.Error);
                }
            }
        }

        private bool TryLoadProgram(string filename)
        {
            Microsoft.Boogie.Program program = Qoogie.ParseFile(filename);
            if (program == null)
            {
                Output.Log("Error parsing the program.");
                return false;
            }

            // load the prelude
            if (config.GetBool("Input", "LoadPrelude", true))
            {
                Microsoft.Boogie.Program prelude = Prelude.GetPrelude();
                if (prelude == null)
                {
                    Output.Log("Error parsing the prelude.");
                    return false;
                }
                program.TopLevelDeclarations.AddRange(prelude.TopLevelDeclarations);
            }

            if (!Verifier.ResolveTypeCheck(program))
            {
                Output.LogLine("Failed in resolving/tyechecking the program");
                return false;
            }

            return true;
        }

        private void showLastMoverReportToolStripMenuItem_Click(object sender, EventArgs e)
        {
            string moverReport = verifier.ProofState.LastMoverReport;
            if (moverReport != null)
            {
                MessageBox.Show(moverReport, "Last mover report");
            }
        }

        private void btn_fixmover_Click(object sender, EventArgs e)
        {
            string rl = InputBox.Show("fixmover", "Enter the type of the mover (r: right, l: left):", "rl");

            if (rl == null)
            {
                return;
            }

            string blocks = InputBox.Show("fixmover", "Enter the labels of the atomic blocks (\"*\" for all):", "*");

            if (blocks == null)
            {
                return;
            }

            txt_Command.Text = "fixmover " + rl + " " + blocks;

            commandFromList = false;

            RunCommand();
        }

        private void btn_refine_ptr_Click(object sender, EventArgs e)
        {
            string auxVarName = InputBox.Show("refine pointer", "Enter the name of the auxiliary variable:");

            if (auxVarName == null)
            {
                return;
            }

            string syncPred = InputBox.Show("refine pointer", "Enter the synchronization predicate:");

            if (syncPred == null)
            {
                return;
            }

            txt_Command.Text = "refine pointer " + auxVarName + " " + syncPred;

            commandFromList = false;

            RunCommand();
        }

        private void cmb_commands_SelectedIndexChanged(object sender, EventArgs e)
        {
            if (cmb_commands.Items.Count > 1 && cmb_commands.SelectedIndex > 0)
            {
                txt_Command.Text = (string) cmb_commands.SelectedItem;

                commandFromList = false;
            }
        }

        private void checkBox1_CheckedChanged(object sender, EventArgs e)
        {
            verifier.config.Set("Reduction", "MergeReturningBranch", checkBox1.Checked);
        }

        private void checkBox2_CheckedChanged(object sender, EventArgs e)
        {
            verifier.config.Set("Reduction", "Iterative", checkBox2.Checked);
        }

        private void checkBox3_CheckedChanged(object sender, EventArgs e)
        {
            verifier.config.Set("Script", "AutoSave", checkBox3.Checked);
        }

        private void checkBox4_CheckedChanged(object sender, EventArgs e)
        {
            verifier.config.Set("", "AutoSave", checkBox4.Checked);
        }

        private void checkBox5_CheckedChanged(object sender, EventArgs e)
        {
            verifier.config.Set("Reduction", "MergeBranch", checkBox5.Checked);
        }

        private void checkBox6_CheckedChanged(object sender, EventArgs e)
        {
            bool oldValue = verifier.config.GetBool("View", "LineNumbers", false);
            verifier.config.Set("View", "LineNumbers", checkBox6.Checked);
            if (checkBox6.Checked != oldValue)
            {
                DisplayProgram();
            }
        }

        private void viewLogToolStripMenuItem_Click(object sender, EventArgs e)
        {
            List<string> lines = ReadLinesFromFile(Output.outputFileName);
            StringBuilder sb = new StringBuilder();
            foreach (string line in lines)
            {
                sb.Append(line + "\r\n");
            }
            DisplayBox.Show("Log", sb.ToString());
        }

        private void clearConsoleToolStripMenuItem_Click(object sender, EventArgs e)
        {
            txt_Output.Text = "";
        }

        private void saveProofToolStripMenuItem_Click(object sender, EventArgs e)
        {
            List<string> lines = new List<string>();
            lines.Add("Proof steps of program: " + program_file_name);
            // save proof history
            foreach (HistoryItem hitem in verifier.history)
            {
                lines.Add("#########################################################################");
                lines.Add("#########################################################################");

                lines.Add(hitem.info);
                if (hitem.command != null) lines.Add("Command: " + hitem.command.ToString());

                lines.Add("#########################################################################");

                lines.Add(hitem.program);
            }

            // Show the open file dialog
            SaveFileDialog ofd = new SaveFileDialog();
            ofd.Title = "Select a history file";
            ofd.Filter = "History Files (*.txt)|*.txt";
            ofd.InitialDirectory = WorkingDir;
            if (ofd.ShowDialog() == DialogResult.OK)
            {
                WriteLinesToFile(ofd.FileName, lines);
                Output.AddLine("History file saved to " + ofd.FileName);
            }   
        }

        private void saveCurrentProgramToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (programTabPage != null)
            {
                Debug.Assert(currentProgramTextBox != null);
                List<string> lines = new List<string>();
                lines.Add(CheckRemoveLineNumbers(currentProgramTextBox.Text, false));
                
                // Show the open file dialog
                SaveFileDialog ofd = new SaveFileDialog();
                ofd.Title = "Select a file to save current program";
                ofd.Filter = "Program Files (*.bpl)|*.bpl";
                ofd.InitialDirectory = WorkingDir;
                if (ofd.ShowDialog() == DialogResult.OK)
                {
                    WriteLinesToFile(ofd.FileName, lines);
                    Output.AddLine("Current program was saved to " + ofd.FileName);
                }   
            }
        }

        private void btn_RunMultiple_Click(object sender, EventArgs e)
        {
            string origCommand = txt_Command.Text;

            string[] commands = origCommand.Split(new string[] {"\r\n", "\n"}, StringSplitOptions.RemoveEmptyEntries);
            for (int i = 0; i < commands.Length; ++i)
            {
                string command = commands[i];
                txt_Command.Text = command;
                RunCommand();
            }

            txt_Command.Text = origCommand;
        }

        private string CurrentCommandStr()
        {
            string commandStr = txt_Command.Text.Trim();

            commandStr = commandStr.Replace("\r\n", " ");
            commandStr = commandStr.Replace("\n", " ");
            
            commandStr = commandStr.Replace("\t", " ");
            return commandStr;
        }

        private void saveLoadCurrentProgramToolStripMenuItem_Click(object sender, EventArgs e)
        {
            SaveLoadCurrentProgramText();
        }

        private void SaveLoadCurrentProgramText()
        {
            if (programTabPage != null)
            {
                Debug.Assert(currentProgramTextBox != null);
                List<string> lines = new List<string>();
                lines.Add(CheckRemoveLineNumbers(currentProgramTextBox.Text, false));

                string file_name = WorkingDir + "\\qed_temp.bpl";

                WriteLinesToFile(file_name, lines);

                LoadProgram(file_name);
            }
        }

        private string WorkingDir
        {
            get
            {
                return Environment.CurrentDirectory;
            }
            set
            {
                Environment.CurrentDirectory = value;
            }
        }

        private void copySelectedAtomicCodeToolStripMenuItem_Click(object sender, EventArgs e)
        {
            string label = InputBox.Show("Copy code", "Enter the atomic block label(blockLabel@procedureName): ");

            if (label == null)
            {
                return;
            }

            AtomicBlock atomicBlock = verifier.proofState.GetAtomicBlockByLabel(label);
            if (atomicBlock == null)
            {
                Output.AddError("Could not find the block: " + label);
                return;
            }

            AtomicStmt atom = atomicBlock.parent;
            StringWriter strw = new StringWriter();

            using (TokenTextWriter writer = new TokenTextWriter(strw))
            {
                atom.body.Emit(writer, 0);
            }
            strw.Flush();

            Util.CopyToClipboard(strw.ToString());
        }

        private void loadProgramToolStripMenuItem1_Click(object sender, EventArgs e)
        {
            if (lst_history.Items.Count > 0)
            {
                int index = lst_history.SelectedIndex;
                verifier.history.Shift(index);
                DisplayProgram();
                SaveLoadCurrentProgramText();
            }
        }

        private void appendCommandHistoryToolStripMenuItem_Click(object sender, EventArgs e)
        {
            SaveCommandHistory(null, true);
            lst_Commands.Items.Clear();
        }

        private void clearProofScriptToolStripMenuItem_Click(object sender, EventArgs e)
        {
            lst_Script.Items.Clear();
        }

        private void clearCommandHistoryToolStripMenuItem_Click(object sender, EventArgs e)
        {
            lst_Commands.Items.Clear();
        }

        private void clearProofHistoryToolStripMenuItem_Click(object sender, EventArgs e)
        {
            lst_history.Items.Clear();
            verifier.history.Clear();
        }

        private void changeTextFontToolStripMenuItem_Click(object sender, EventArgs e)
        {
            FontDialog fontDialog = new FontDialog();
            fontDialog.Font = textFont;

            if (fontDialog.ShowDialog(this) == DialogResult.OK)
            {
                textFont = fontDialog.Font;
                currentProgramTextBox.Font = textFont;
                inputProgramTextBox.Font = textFont;
                Output.AddLine("New font selected: " + textFont.ToString());

                DisplayProgram();
            }
        }

        private void scriptStatisticsToolStripMenuItem_Click(object sender, EventArgs e)
        {
            // Show the open file dialog
            OpenFileDialog ofd = new OpenFileDialog();
            ofd.Title = "Select a script file";
            ofd.Filter = "Script Files (*.qet)|*.qet";
            ofd.InitialDirectory = WorkingDir;
            if (ofd.ShowDialog() == DialogResult.OK)
            {
                ProofScript script = ProofScript.Parse(ofd.FileName);
                MessageBox.Show(this, script.Report(), "Script statistics");
            }         
        }

        private void checkBox7_CheckedChanged(object sender, EventArgs e)
        {
            bool oldValue = verifier.config.GetBool("View", "ShowBlockCFG", false);
            verifier.config.Set("View", "ShowBlockCFG", checkBox7.Checked);
            if (checkBox7.Checked != oldValue)
            {
                DisplayProgram();
            }
        }

        private void checkBox8_CheckedChanged(object sender, EventArgs e)
        {
            bool oldValue = verifier.config.GetBool("View", "ColorCode", false);
            verifier.config.Set("View", "ColorCode", checkBox8.Checked);
            if (checkBox8.Checked != oldValue)
            {
                DisplayProgram();
            }
        }

        private void searchToolStripMenuItem_Click(object sender, EventArgs e)
        {
            string label = InputBox.Show("Search for text", "Enter the text:");

            if (label == null)
            {
                return;
            }

            int index = currentProgramTextBox.Find(label, RichTextBoxFinds.None);
            if (index >= 0)
            {
                currentProgramTextBox.Select(index, label.Length);
                currentProgramTextBox.ScrollToCaret();
            }
        }
	}
}
