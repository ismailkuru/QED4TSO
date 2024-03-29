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
using System.Text;
using System.Diagnostics;

public class ErrorTrace {

	protected Set<string> labels;
	protected ProcedureState procState;

	public ErrorTrace(Set<string> l, ProcedureState p) {
		this.labels = new Set<string>(l);
		this.procState = p;	
	}
	
	public string Report {
		get {
			StringBuilder strb = new StringBuilder();

            foreach (string label in labels)
            {
                Absy node = LabeledExpr.GetAbsyByLabel(label);

                if (LabeledExprHelper.IsInvariant(label))
                {
                    strb.AppendLine("Invariant violation: " + ((node as APLBlock)).UniqueLabel);
                }
                else
                    if (LabeledExprHelper.IsGuar(label))
                    {
                        strb.AppendLine("Guarantee violation: " + ((node as APLBlock)).UniqueLabel);
                    }
                    else
                        if (LabeledExprHelper.IsPostCond(label))
                        {
                            strb.AppendLine("Post condition violation: " + ((node as APLBlock)).UniqueLabel);
                        }
                        else
                            if (LabeledExprHelper.IsNegAssert(label))
                            {
                                strb.AppendLine("Assertion violation: " + Output.ToString(((node as AssertCmd)).Expr));
                            }
                            else
                                if (LabeledExprHelper.IsAssert(label))
                                {
                                    strb.AppendLine("Assertion violation: " + Output.ToString(((node as AssertCmd)).Expr));
                                }
                                else
                                    if (LabeledExprHelper.IsAtomicBlock(label))
                                    {
                                        strb.AppendLine("Atomic Block WP: " + ((node as APLBlock)).UniqueLabel);
                                    }
                                    else
                                        if (LabeledExprHelper.IsAPLBlock(label))
                                        {
                                            strb.AppendLine("APLBlock WP: " + ((node as APLBlock)).UniqueLabel);
                                        }
                                        else
                                            if (LabeledExprHelper.IsBlock(label))
                                            {
                                                strb.AppendLine("Block WP: " + ((node as Block)).Label);
                                            }
                                            else
                                            {
                                                strb.AppendLine("Other label: " + label);
                                            }
            }
			
			return strb.ToString();
		}
	}
	
	public Counterexample CreateCounterexample() {
		Hashtable traceNodes = new Hashtable();
        foreach (string s in labels) {
          Absy node = (Absy) LabeledExpr.GetAbsyByLabel(s);
          traceNodes.Add(node, null);
        }
        
        BlockSeq trace = new BlockSeq();
        Block entryBlock = procState.impl.Blocks[0];
        Debug.Assert(traceNodes.Contains(entryBlock));
        trace.Add(entryBlock);
        Counterexample newCounterexample = TraceCounterexample(entryBlock, traceNodes, trace);
        
        return newCounterexample;
	}
	
	private Counterexample TraceCounterexample(Block b, Hashtable traceNodes, BlockSeq trace)
    {
      // After translation, all potential errors come from asserts.
      CmdSeq cmds = b.Cmds;
      TransferCmd transferCmd = b.TransferCmd;
      for (int i = 0; i < cmds.Length; i++)
      {
        Cmd cmd = cmds[i];
        
        // Skip if 'cmd' not contained in the trace or not an assert
        if (!(cmd is AssertCmd) || !traceNodes.Contains(cmd))
          continue;

        AssertCounterexample ac = new AssertCounterexample(trace, (AssertCmd)cmd);
        ac.relatedInformation = new List<string>();
        return ac;
      }
      
      GotoCmd gotoCmd = transferCmd as GotoCmd;
      if (gotoCmd != null)
      {
        foreach (Block bb in gotoCmd.labelTargets)
        {
          if (traceNodes.Contains(bb)){
            trace.Add(bb);
            return TraceCounterexample(bb, traceNodes, trace);
          }
        }
      }
      
      Output.AddError("Could not find failing node.");
      Debug.Assert(false);
      return null;
    }

} // end class ErrorTrace

} // end namespace QED

