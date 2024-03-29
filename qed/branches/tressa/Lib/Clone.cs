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


    public class HoistCommand : ProofCommand
    {
        string atomLabel;

        string afterbefore;

        public HoistCommand(string block, string branch)
            : base("hoist")
        {
            this.atomLabel = block;
            this.afterbefore = branch;
            desc = "hoist " + atomLabel + " " + afterbefore;
        }

        public static string Usage()
        {
            return "hoist atomicBlockLabel@procedureName before|after";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("hoist"))
            {
                string blocklabel = parser.NextAsString();
                string afterbefore = parser.NextAsString();
                return new HoistCommand(blocklabel, afterbefore);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;

            if (!CodeTransformations.Hoist(procState, atomicBlock.parent, afterbefore == "after"))
            {
                Output.AddError("Error in hoisting " + atomLabel);
            }
            else
            {
                procState.MarkAsTransformed();
            }

            return false;

        }
    } // end class Hoist

    public class SplitCommand : ProofCommand
    {
        string atomLabel;
        public Kind kind;
        public enum Kind { If, While }

        public SplitCommand(string block, Kind k)
            : base("split")
        {
            this.atomLabel = block;
            this.kind = k;
            desc = "split " + (kind == Kind.If ? "if" : "while") + " " + atomLabel;
        }

        public static string Usage()
        {
            return "split if|while atomicBlockLabel@procedureName";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("split"))
            {
                string kind = parser.NextAsString();
                string blocklabel = parser.NextAsString();
                
                return new SplitCommand(blocklabel, kind == "if" ? Kind.If : Kind.While);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(atomLabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + atomLabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;

            if (this.kind == Kind.If)
            {
                if (!CodeTransformations.SplitIf(procState, atomicBlock.parent))
                {
                    Output.AddError("Error in splitting if: " + atomLabel);
                }
                else
                {
                    procState.MarkAsTransformed();
                }
            }

            return false;

        }
    } // end class Hoist


    public class PeelOutCommand : ProofCommand
    {
        string blocklabel;

        public PeelOutCommand(string name)
            : base("peelout")
        {
            this.blocklabel = name;
            desc = "peelout " + blocklabel;
        }

        public static string Usage()
        {
            return "peelout atomicBlockLabel@procedureName";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("peelout"))
            {
                string blocklabel = parser.NextAsString();
                return new PeelOutCommand(blocklabel);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);
            if (atomicBlock == null)
            {
                Output.AddError("Atomic block does not exists: " + blocklabel);
                return false;
            }

            ProcedureState procState = atomicBlock.procState;

            //------------------------------------------------------
            // check if the atomic block is the body of a loop
            AtomicStmt atom = atomicBlock.parent;
            BigBlock bb = atom.body.ParentContext.ParentBigBlock;
            if (bb.ec == null || !(bb.ec is WhileCmd))
            {
                Output.AddError("Given atomic block is not in the body of a while loop!");
                return false;
            }

            DoRun(proofState, atomicBlock.procState, bb);

            procState.MarkAsTransformed();

            return false;
        }

        static public void DoRun(ProofState proofState, ProcedureState procState, BigBlock bb)
        {
            WhileCmd whileCmd = bb.ec as WhileCmd;
            Debug.Assert(whileCmd != null);

            int index;
            StmtList parentStmt = Qoogie.GetParentContext(bb, procState.Body, out index);
            StmtList body = whileCmd.Body;

            //---------------------------
            StmtList S1 = body;
            StmtList S2 = Qoogie.DuplicateStatement(body);

            //---------------------------
            // S1
            CodeTransformations.ReplaceBreakWithThrow(S1);
            bool hasContinue = CodeTransformations.ReplaceContinueWithThrow(S1);
            CodeTransformations.ReplaceReturnWithThrow(S1);
            if (hasContinue)
            {
                S1 = Qoogie.SkipEx(S1, null, proofState.exContinueExpr);
            }
            S1 = Qoogie.SuppressEx(S1, null); // , proofState.exBreakExpr, proofState.exReturnExpr);

            if (whileCmd.Guard != null)
            {
                // make while(e) while(*)
                if (MergeCommand.IsAtomic(S1))
                {
                    AtomicStmt atom = S1.BigBlocks[0].ec as AtomicStmt;
                    CodeTransformations.InstrumentEntry(atom.body, new CmdSeq(new AssumeCmd(Token.NoToken, whileCmd.Guard)), true);
                }
                else
                {
                    CodeTransformations.InstrumentEntry(S1, new CmdSeq(new AssumeCmd(Token.NoToken, whileCmd.Guard)), false);
                }
            }

            whileCmd.Body = S1;

            //---------------------------
            // S2
            S2 = Qoogie.Suppress(S2);
            hasContinue = CodeTransformations.ReplaceContinueWithThrow(S2);
            if (hasContinue)
            {
                S2 = Qoogie.SuppressEx(S2, null, proofState.exContinueExpr);
            }
            bool hasBreak = CodeTransformations.ReplaceBreakWithThrow(S2);
            if (hasBreak)
            {
                S2 = Qoogie.SkipEx(S2, null, proofState.exBreakExpr);
            }
            
            Expr guard = whileCmd.Guard == null ? null : Qoogie.DuplicateExpr(whileCmd.Guard);
            IfCmd ifCmd = new IfCmd(Token.NoToken, guard, S2, null, null);
            BigBlock ifbb = new BigBlock(Token.NoToken, null, new CmdSeq(), ifCmd, null);
            parentStmt.BigBlocks.Insert(index + 1, ifbb);

            //---------------------------
            whileCmd.Guard = null;
            
            procState.MarkAsTransformed();
        }
    } // end class PeelOutCommand
  
#if false
public class CloneCommand : ProofCommand
{
	string blockLabel;
	
	string branchLabel;
	
	public CloneCommand(string block, string branch)
		: base("clone")
	{
		blockLabel = block;
		branchLabel = branch;
		desc = "clone " + blockLabel + " " + branchLabel;
	}
	
	override public bool Run(ProofState proofState) {

        if (!proofState.AtomicBlockExists(blockLabel))
        {
            Output.AddError("Block " + blockLabel + " does not exist!");
            return false;
        }


		AtomicBlock atomicBlock = proofState.GetAtomicBlock(blockLabel);
		
		if(!atomicBlock.IsClonable) {
			return false;
		}
		
		if(branchLabel == "*") {
		
			CloneAtomicBlock(atomicBlock, proofState);
		
		} else {
		
			AtomicBlock otherBlock = proofState.GetAtomicBlock(branchLabel);

            if (!proofState.AtomicBlockExists(branchLabel))
            {
                Output.AddError("Block " + branchLabel + " does not exist!");
                return false;
            }
			
			if(atomicBlock.Successors.Contains(otherBlock)) {
				CloneAfter(proofState, atomicBlock, otherBlock);
			} else {
                if (!otherBlock.Successors.Contains(atomicBlock))
                {
                    Output.AddError("Blocks " + blockLabel + " and " + branchLabel + " are not connected!");
                    return false;
                }
				CloneBefore(proofState, atomicBlock, otherBlock);
			}
		}
		
		return false;
	}
	
	private void CloneAfter(ProofState proofState, AtomicBlock atomicBlock, AtomicBlock successor) {
		Debug.Assert(atomicBlock.Successors.Count > 1);
		
		AtomicBlock cloneBlock = atomicBlock.Clone(new Dictionary<Block, Block>());
		
		//--------------------------------------------
		
		Set<Block> exitBlocks = cloneBlock.ExitBlocks;
		
		Debug.Assert(exitBlocks.Count == 1); // we cannot handle more complicated cases
		
		Block exitBlock = exitBlocks.PickOne();
		
		exitBlock.TransferCmd = new GotoCmd(Token.NoToken, new BlockSeq(successor.startBlock));
		
		//--------------------------------------------
		
		foreach(Block predBlock in atomicBlock.startBlock.Predecessors) {
			GotoCmd predGotoCmd = (predBlock.TransferCmd as GotoCmd);
			predGotoCmd.AddTarget(cloneBlock.startBlock);		
		}
		
		//--------------------------------------------
		
		exitBlocks = atomicBlock.ExitBlocks;
		
		Debug.Assert(exitBlocks.Count == 1); // we cannot handle more complicated cases
		
		exitBlock = exitBlocks.PickOne();
		
		GotoCmd exitGotoCmd = exitBlock.TransferCmd as GotoCmd;
		if(exitGotoCmd != null) {
			BlockSeq newTargets = new BlockSeq();
			foreach(Block target in exitGotoCmd.labelTargets) {
				if(target != successor.startBlock) {
					newTargets.Add(target);
				}
			}
			exitBlock.TransferCmd = new GotoCmd(Token.NoToken, newTargets);			
		}				
		
		//--------------------------------------------
		
		// finally modify the procedure state
		ProcedureState procState = atomicBlock.procState;
		
		procState.AddAtomicBlock(cloneBlock);

        procState.CFGUpdated();
	}
	
	private void CloneBefore(ProofState proofState, AtomicBlock atomicBlock, AtomicBlock predecessor) {
		Debug.Assert(atomicBlock.startBlock.Predecessors.Length > 1);
		
		AtomicBlock cloneBlock = atomicBlock.Clone();
		
		//--------------------------------------------
		
		Set<Block> exitBlocks = predecessor.ExitBlocks;
		
		Debug.Assert(exitBlocks.Count == 1); // we cannot handle more complicated cases
		
		Block exitBlock = exitBlocks.PickOne();
		
		GotoCmd exitGotoCmd = exitBlock.TransferCmd as GotoCmd;
		BlockSeq newTargets = new BlockSeq();
		foreach(Block target in exitGotoCmd.labelTargets) {
			if(target != atomicBlock.startBlock) {
				newTargets.Add(target);
			}
		}
		newTargets.Add(cloneBlock.startBlock);
		exitBlock.TransferCmd = new GotoCmd(Token.NoToken, newTargets);			
		
		//--------------------------------------------
		
		// finally modify the procedure state
		ProcedureState procState = atomicBlock.procState;
		
		procState.AddAtomicBlock(cloneBlock);
		
		procState.CFGUpdated();
	}
	
	private void CloneAtomicBlock(AtomicBlock atomicBlock, ProofState proofState) {
		Debug.Assert(atomicBlock.Successors.Count > 1 || atomicBlock.startBlock.Predecessors.Length > 1);
		
		Block startBlock = atomicBlock.startBlock;
		
		Set<AtomicBlock> newAtomicBlocks = new Set<AtomicBlock>();
		
		// create the block in the middle
		Block middle = new Block(Token.NoToken, startBlock.Label, new CmdSeq(), new GotoCmd(Token.NoToken, new BlockSeq()));
				
		// clone for predecessors		
		if(startBlock.Predecessors.Length > 0) {
			if(startBlock.Predecessors.Length == 1) {
				Block predBlock = startBlock.Predecessors[0];
				GotoCmd gotoCmd = (predBlock.TransferCmd as GotoCmd);	
				BlockSeq newTargets = new BlockSeq();
				foreach(Block target in gotoCmd.labelTargets) {
					if(target != startBlock) {
						newTargets.Add(target);
					}
				}
				newTargets.Add(middle);
				predBlock.TransferCmd = new GotoCmd(Token.NoToken, newTargets);		
			
			} else {
			
				foreach(Block predBlock in startBlock.Predecessors) {
					
					AtomicBlock cloneBlock = atomicBlock.Clone();
					
					GotoCmd gotoCmd = (predBlock.TransferCmd as GotoCmd);	
					BlockSeq newTargets = new BlockSeq();
					foreach(Block target in gotoCmd.labelTargets) {
						if(target != startBlock) {
							newTargets.Add(target);
						}
					}
					newTargets.Add(cloneBlock.startBlock);
					predBlock.TransferCmd = new GotoCmd(Token.NoToken, newTargets);	
					
					newAtomicBlocks.Add(cloneBlock);				
				}
			
			}
		}
		
		// clone for successors
		if(atomicBlock.Successors.Count > 0) {	
			if(atomicBlock.Successors.Count == 1) {
				
				(middle.TransferCmd as GotoCmd).AddTarget(atomicBlock.Successors.PickOne().startBlock);
			
			} else {
			
				foreach(AtomicBlock successor in atomicBlock.Successors) {
					
					AtomicBlock cloneBlock = atomicBlock.Clone();
					
					Set<Block> exitBlocks = cloneBlock.ExitBlocks;
					Debug.Assert(exitBlocks.Count == 1); // we cannot handle more complicated cases
					
					Block exitBlock = exitBlocks.PickOne();
					
					exitBlock.TransferCmd = new GotoCmd(Token.NoToken, new BlockSeq(successor.startBlock));
					
					(middle.TransferCmd as GotoCmd).AddTarget(cloneBlock.startBlock);
					
					newAtomicBlocks.Add(cloneBlock);
				}	
			}
		}
		
		// create the middle atomic block
		AtomicBlock middleAtomic = new AtomicBlock(atomicBlock.procState, middle);
		newAtomicBlocks.Add(middleAtomic);
		
		// finally modify the procedure state
		ProcedureState procState = atomicBlock.procState;
		
		procState.RemoveAtomicBlock(atomicBlock);
		
		foreach(AtomicBlock newAtomicBlock in newAtomicBlocks) {
			procState.AddAtomicBlock(newAtomicBlock);
		}
		
		procState.CFGUpdated();
	}
	
} // end class CloneCommand
#endif

} // end namespace QED
