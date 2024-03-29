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
  

public class MergeCommand : ProofCommand
{

	protected bool iterate = false;
	protected bool mergedAny = false;
	
	public bool MergedAny {
		get {
			return mergedAny;
		}
	}

	bool isproc;
    string label;

	public MergeCommand(string lbl, bool isproc, bool iter)
		: base("merge")
	{
		this.label = lbl;
        this.isproc = isproc;
        this.iterate = iter;
        this.mergedAny = false;
        desc = (isproc ? ("merge proc " + label) : ("merge " + label)) + (iterate ? " *" : "");
	}

    public static string Usage()
    {
        return "merge proc procName|all";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("merge"))
        {
            string label = parser.NextAsString();
            if (label == "proc")
            {
                label = parser.NextAsString();
                return new MergeCommand(label, true, parser.NextStartsWith("*"));
            }

            return new MergeCommand(label, false, parser.NextStartsWith("*"));
        }
        return null;
    }
	
	override public bool Run(ProofState proofState) {
		
		List<ProcedureState> procStates = new List<ProcedureState>();

        if (isproc)
        {
            ProcedureState procState = proofState.GetProcedureState(label);
            procStates.Add(procState);
        }
        else if (label == "all")
        {
            procStates.AddRange(proofState.ProcedureStates);
        }
        else
        {
            Output.AddError("Label must be all or proc procedureName!");
            return false;
        }

        DoRun(proofState, procStates);

        return false;
	}

    public void DoRun(ProofState proofState, List<ProcedureState> procStates)
    {
        foreach (ProcedureState procState in procStates)
        {
            DoRun(proofState, procState);

            CodeTransformations.RemoveUnreachableLabels(procState.Body);
        }
    }

    IDictionary<string, ICollection<BigBlock>> BBPredecessorMap;

    public void DoRun(ProofState proofState, ProcedureState procState)
    {
        DoReduction(proofState, procState);
    }
	
	protected void DoReduction(ProofState proofState, ProcedureState procState) {
		bool any = false;

        this.mergedAny = false;

        do {
			any = false;
			
#if false
			if(proofState.config.GetBool("Reduction", "AutoClone", true)) {
				CheckClone(proofState, procState);
			}
#endif	
            BBPredecessorMap = Qoogie.ComputePredecessorMap(procState.Body);

			any |= Reduce(proofState, procState, procState.Body);
            mergedAny |= any;
		
		} while (iterate && any);

        procState.MarkAsTransformed();		
	}


#if false
	protected void CheckClone(ProofState proofState, ProcedureState procState) {
		bool any = false;
		do {
			any = false;
			
			CloneCommand clone = null;
			foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
				if(clone == null && atomicBlock.IsClonable && atomicBlock.Successors.Count > 1) {
					foreach(AtomicBlock successor in atomicBlock.Successors) {
						if(ComputeMoverStraight(atomicBlock.Mover, successor.Mover) != null) {
							clone = new CloneCommand(atomicBlock.Label, successor.Label); // clone after
							break;
						}
					}
				}
			}
			
			if(clone != null) {
				clone.Run(proofState);
				any = true;
			}
			
		} while (any);
	}
#endif

    protected bool Reduce(ProofState proofState, ProcedureState procState, StmtList stmtList)
    {
        bool any = false;
        bool ret = false;

        do
        {
            any = false;

            List<BigBlock> bigBlocks = stmtList.BigBlocks;

            // reduce each big block separately
            int i = 0;
            while(i < bigBlocks.Count) {
                BigBlock bb = bigBlocks[i];

                List<BigBlock> parbbs = null;
                any |= Reduce(proofState, procState, bb, out parbbs);
                ret |= any;

                if (parbbs != null)
                {
                    bigBlocks.RemoveAt(i);
                    bigBlocks.InsertRange(i, parbbs);
                }
                ++i;
            }

            // reduce blocks with transfer commands
            any |= ReduceTransfer(proofState, procState, stmtList);
            ret |= any;

            // reduce straight paths
            List<BigBlock> newbbs = new List<BigBlock>();
            for (i = 0; i < bigBlocks.Count; ++i)
            {
                BigBlock bb = bigBlocks[i];
                Debug.Assert(bb.simpleCmds.Length == 0);
                
                //---------------------------------------------
                // this is the last block, so add it and end the iteration
                if (i == bigBlocks.Count - 1)
                {
                    newbbs.Add(bb);
                    break;
                }
                
                //---------------------------------------------
                // this block if not atomic
                if (!IsAtomic(bb))
                {
                    newbbs.Add(bb);
                    continue;
                }
                
                //---------------------------------------------
                // if next block is empty (tc and ec both null, merge it)
                BigBlock nextbb = bigBlocks[i + 1];
                Debug.Assert(nextbb.simpleCmds.Length == 0);
                
                if(!IsAtomic(nextbb))
                {
                    newbbs.Add(bb);
                    continue;
                }

                //---------------------------------------------
                // now bb and nextbb are both atomic, so check if we can merge them
                AtomicStmt atom = bb.ec as AtomicStmt;
                AtomicStmt succ = nextbb.ec as AtomicStmt;

                MoverType result = MoverType.ComposeSeq(MoverType.FromEnum(atom.mover), MoverType.FromEnum(succ.mover));

                if (result != null)
                {
                    ret = any = true;

                    AtomicStmt newAtom = MakeStraightAtomicStmt(proofState, procState, atom, succ, result);

                    bb.ec = newAtom;

                    ++i; // skip next big block
                }

                // in any case add bb to newbbs
                newbbs.Add(bb);
            }

            bigBlocks.Clear();
            bigBlocks.AddRange(newbbs);

        } while (iterate && any);

        return ret;
    }

    protected bool ReduceTransfer(ProofState proofState, ProcedureState procState, StmtList stmtList)
    {
        bool any = false;
        bool ret = false;

        do
        {
            any = false;

            List<BigBlock> bigBlocks = stmtList.BigBlocks;

            // reduce straight paths
            List<BigBlock> newbbs = new List<BigBlock>();
            for (int i = 0; i < bigBlocks.Count; ++i)
            {
                BigBlock bb = bigBlocks[i];
                Debug.Assert(bb.simpleCmds.Length == 0);

                //---------------------------------------------
                // if the first block empty, then try to put this inside another atomic stmt
                if (bb.ec == null || bb.ec is BreakCmd || bb.ec is ContinueCmd)
                {
                    AtomicStmt adjAtom = null;
                    bool inserted = false;
                    if (newbbs.Count > 0 && IsAtomic(newbbs[newbbs.Count - 1]))
                    {
                        Debug.Assert(0 < i);
                        adjAtom = newbbs[newbbs.Count - 1].ec as AtomicStmt;
                        inserted = TryInsertEmptyBigBlock(bb, adjAtom, false);
                    }

                    if (!inserted && i < bigBlocks.Count - 1 && IsAtomic(bigBlocks[i + 1]))
                    {
                        adjAtom = bigBlocks[i + 1].ec as AtomicStmt;
                        inserted = TryInsertEmptyBigBlock(bb, adjAtom, true);
                    }

                    if (!inserted)
                    {
                        newbbs.Add(bb); // failure
                    }
                    else
                    {
                        ret = any = true;
                    }
                    continue;
                }

                newbbs.Add(bb);
            }

            bigBlocks.Clear();
            bigBlocks.AddRange(newbbs);

        } while (iterate && any);

        return ret;
    }

    protected bool TryInsertEmptyBigBlock(BigBlock bb, AtomicStmt adjAtom, bool atbegin)
    {
        StmtList body = adjAtom.body;

        if (BBPredecessorMap.ContainsKey(bb.LabelName))
        {
            Set<BigBlock> predbbs = BBPredecessorMap[bb.LabelName] as Set<BigBlock>;
            Set<BigBlock> atombbs = new BigBlocksCollector().Collect(body);

            if (predbbs.Difference(atombbs).Count > 0)
            {
                return false;
            }
        }

        if (atbegin)
        {
            body.BigBlocks.Insert(0, bb);
        }
        else
        {
            body.BigBlocks.Add(bb);
        }

        return true;
    }

    protected bool Reduce(ProofState proofState, ProcedureState procState, BigBlock bb, out List<BigBlock> newbbs)
    {
        bool any = false;

        newbbs = null; // set only by parallel stmt

        Debug.Assert(bb.simpleCmds.Length == 0);

        if (bb.ec == null) return any;

        if (bb.ec is AtomicStmt || bb.ec is CallStmt || bb.ec is BreakCmd || bb.ec is ContinueCmd) return any;

        AtomicStmt atom = null;
        if (bb.ec is IfCmd)
        {
            atom = ReduceIf(proofState, procState, bb.ec as IfCmd, out any);
        }
        else if (bb.ec is WhileCmd)
        {
            WhileCmd whileCmd = bb.ec as WhileCmd;
            
            any |= Reduce(proofState, procState, whileCmd.Body);
        }
        else if (bb.ec is ParallelStmt)
        {
            newbbs = ReducePar(proofState, procState, bb.ec as ParallelStmt);

            any |= (newbbs.Count > 1);
        }
        else if (bb.ec is TryCatchStmt)
        {
            atom = ReduceTryCatch(proofState, procState, bb.ec as TryCatchStmt, out any);
        }

        //-------------------------------
        if (atom != null)
        {
            Debug.Assert(atom.label == null);
            // set the label of the atom
            if (bb.Anonymous)
            {
                string atomLbl = AtomicStmt.GenerateLabel();
                bb.LabelName = atom.label = atomLbl;
                bb.Anonymous = false;
            }
            else
            {
                atom.label = bb.LabelName;
            }
            bb.ec = atom;

            any = true;
        }

        return any;
    }

    
    protected AtomicStmt ReduceIf(ProofState proofState, ProcedureState procState, IfCmd ifCmd, out bool any)
    {
        Debug.Assert(ifCmd.elseIf == null);

        // reduce parts of if
        any = Reduce(proofState, procState, ifCmd.thn);
        if(ifCmd.elseBlock != null) {
            any |= Reduce(proofState, procState, ifCmd.elseBlock);
        }

        // now check reduction
        bool isAtomic = IsAtomic(ifCmd.thn) && (ifCmd.elseBlock == null  || IsAtomic(ifCmd.elseBlock));

        if (isAtomic)
        {
            // now do reduce if
            // remove AtomicStmt from thn
            AtomicStmt thnAtom = ifCmd.thn.BigBlocks[0].ec as AtomicStmt;
            // save the big block label of the then block
            //InsertAtomLabel(thnAtom);

            InsertAt(ifCmd.thn, thnAtom.body, 0);

            MoverType thnMover = MoverType.FromEnum(thnAtom.mover);
            MoverType elsMover = MoverType.BothMover;

            // now handle else
            if (ifCmd.elseBlock != null)
            {
                // remove AtomicStmt from else
                AtomicStmt elseAtom = ifCmd.elseBlock.BigBlocks[0].ec as AtomicStmt;
                // save the big block label of the else block
                //InsertAtomLabel(elseAtom);

                InsertAt(ifCmd.elseBlock, elseAtom.body, 0);

                elsMover = MoverType.FromEnum(elseAtom.mover);

            }

            // build the new atomic newbody
            BigBlock bb = new BigBlock(ifCmd.tok, null, new CmdSeq(), ifCmd, null);
            List<BigBlock> bbs = new List<BigBlock>();
            bbs.Add(bb);
            StmtList stmtin = new StmtList(bbs, Token.NoToken);

            AtomicStmt atom = new AtomicStmt(ifCmd.tok, null, stmtin);
            atom.mover = MoverType.ComposeCho(thnMover, elsMover).ToEnum();

            any = true;

            return atom;
        } // end if isAtomic

        return null;
    }

    protected AtomicStmt ReduceTryCatch(ProofState proofState, ProcedureState procState, TryCatchStmt trycatch, out bool any)
    {
        // reduce parts of if
        any = Reduce(proofState, procState, trycatch.body);
        bool isAtomic = IsAtomic(trycatch.body);
        foreach (CatchStmt catchStmt in trycatch.catchList)
        {
            any |= Reduce(proofState, procState, catchStmt.body);
            isAtomic &= IsAtomic(catchStmt.body);
        }

        if (!isAtomic) return null;

        MoverType result = ComputeMoverTryCatch(trycatch);
        if (result == null) return null;

        // now do reduce
        // remove AtomicStmt from thn
        AtomicStmt tryAtom = trycatch.body.BigBlocks[0].ec as AtomicStmt;
        InsertAt(trycatch.body, tryAtom.body, 0);

        // now handle else
        foreach (CatchStmt catchStmt in trycatch.catchList)
        {
            AtomicStmt catchAtom = catchStmt.body.BigBlocks[0].ec as AtomicStmt;
            InsertAt(catchStmt.body, catchAtom.body, 0);
        }

        // build the new atomic newbody
        BigBlock bb = new BigBlock(trycatch.tok, trycatch.label, new CmdSeq(), trycatch, null);
        List<BigBlock> bbs = new List<BigBlock>();
        bbs.Add(bb);
        StmtList stmtin = new StmtList(bbs, Token.NoToken);

        AtomicStmt atom = new AtomicStmt(trycatch.tok, null, stmtin);
        atom.mover = result.ToEnum();

        any = true;

        return atom;
    }

    protected List<BigBlock> ReducePar(ProofState proofState, ProcedureState procState, ParallelStmt parStmt)
    {
        Debug.Assert(parStmt.bodies.Count >= 2);

        // reduce parts of parallel stmt
        foreach (StmtList body in parStmt.bodies)
        {
            Reduce(proofState, procState, body);
        }

        List<BigBlock> bbsBefore = new List<BigBlock>();
        List<BigBlock> bbsAfter = new List<BigBlock>();
        // now check reduction
        int reduced = -1;
        List<StmtList> bodies = parStmt.bodies;
        do
        {
            reduced = -1;
            if (bodies.Count == 1)
            {
                bbsBefore.AddRange(bodies[0].BigBlocks);
                reduced = 0;
            }
            else
            {
                for (int i = 0; i < bodies.Count; ++i)
                {
                    StmtList body = bodies[i];
                    if (IsAtomic(body))
                    {
                        AtomicStmt atom = body.BigBlocks[0].ec as AtomicStmt;
                        if (atom.mover == AtomicStmt.Mover.Left || atom.mover == AtomicStmt.Mover.Both)
                        {
                            bbsBefore.Add(body.BigBlocks[0]);
                            reduced = i;
                            break;
                        }
                        else if (atom.mover == AtomicStmt.Mover.Right || atom.mover == AtomicStmt.Mover.Both)
                        {
                            bbsAfter.Add(body.BigBlocks[0]);
                            reduced = i;
                            break;
                        }
                    }
                }
            }
            if (reduced > -1)
            {
                bodies.RemoveAt(reduced);
            }
        } while (reduced > -1 && bodies.Count > 0);

        List<BigBlock> bbs = new List<BigBlock>();

        bbs.AddRange(bbsBefore);

        if (bodies.Count > 0)
        {
            Debug.Assert(bodies.Count >= 2);
            bbs.AddRange(ExpandPar(proofState, procState, parStmt));
        }

        bbs.AddRange(bbsAfter);
        
        return bbs;
    }

    protected List<BigBlock> ExpandPar(ProofState proofState, ProcedureState procState, ParallelStmt parStmt)
    {
        Debug.Assert(parStmt.bodies.Count >= 2);

        List<BigBlock> bbs = new List<BigBlock>();

        List<StmtList> bodies = parStmt.bodies;

        if (parStmt.bodies.Count == 2 && IsAtomic(bodies[0]) && IsAtomic(bodies[1]))
        {
            List<BigBlock> bbsthen = new List<BigBlock>();
            bbsthen.Add(bodies[0].BigBlocks[0]);
            bbsthen.Add(bodies[1].BigBlocks[0]);
            StmtList thenStmt = new StmtList(bbsthen, Token.NoToken);

            List<BigBlock> bbselse = new List<BigBlock>();
            bbselse.Add(Qoogie.DuplicateBigBlock(bodies[1].BigBlocks[0]));
            bbselse.Add(Qoogie.DuplicateBigBlock(bodies[0].BigBlocks[0]));
            StmtList elseStmt = new StmtList(bbselse, Token.NoToken);

            IfCmd ifCmd = new IfCmd(parStmt.tok, null, thenStmt, null, elseStmt);
            BigBlock bbif = new BigBlock(parStmt.tok, parStmt.label, new CmdSeq(), ifCmd, null);
            
            bbs.Add(bbif);
        }
        else
        {
            BigBlock bb = new BigBlock(parStmt.tok, parStmt.label, new CmdSeq(), parStmt, null);
            bbs.Add(bb);
        }
        
        return bbs;
    }
    
    // insert the bigblocks of child to the bigblocks of parent at index
    // this nullifies ec of the bigblock at index !!!
    internal static void InsertAt(StmtList parent, StmtList child, int index)
    {
        BigBlock bb = parent.BigBlocks[index];
        Debug.Assert(bb.ec != null && bb.tc == null && bb.simpleCmds.Length == 0);
        bb.ec = null;
        if (bb.Anonymous)
        {
            parent.BigBlocks.RemoveAt(index);
            parent.BigBlocks.InsertRange(index, child.BigBlocks);
        }
        else
        {
            parent.BigBlocks.InsertRange(index+1, child.BigBlocks);
        }
    }

    internal static bool IsAtomic(StmtList stmtList)
    {
        return stmtList.BigBlocks.Count == 1 && stmtList.BigBlocks[0].ec is AtomicStmt;
    }

    internal static bool IsAtomic(BigBlock bb)
    {
        return bb.ec != null && bb.ec is AtomicStmt;
    }
#if false
	protected bool ReduceBranches(ProofState proofState, ProcedureState procState) {
		bool ret = false;
		bool any = false;
		
		List<AtomicBlock> atomicBlocks = new List<AtomicBlock>();
			
		Output.LogLine("Merging branches");
		
		do {
			any = false;
			
			atomicBlocks.Clear();
			atomicBlocks.AddRange(procState.atomicBlocks);
			
			foreach(AtomicBlock atomicBlock in atomicBlocks) {
			
				if(!any && atomicBlock.Successors.Count > 1) {
					List<AtomicBlock> succList = new List<AtomicBlock>(atomicBlock.Successors);
					
					for(int i = 0, n = succList.Count-1; i < n && !any; ++i) {
						AtomicBlock thisBlock = succList[i];
						if(!thisBlock.CanMerge) continue;
						
						for(int j = i+1, m = succList.Count; j < m && !any; ++j) {
							AtomicBlock thatBlock = succList[j];
							if(!thatBlock.CanMerge) continue;
							
							if(thisBlock.Successors.Equals(thatBlock.Successors)
                                || ((thisBlock.Successors.Count == 0) && (thatBlock.Successors.Count == 0))
                                || (proofState.config.GetBool("Reduction", "MergeReturningBranch", false)
                                    && ((thisBlock.Successors.Count == 0) || (thatBlock.Successors.Count == 0)))) {
							   
								// do not merge with a loop xheader
								// TODO: move this check to somewhere else
								bool xheader = false;
                                //foreach(LoopInfo loopInfo in procState.loopInfoMap.Values) {
                                //    if(loopInfo.XHeader == thisBlock.startBlock ||
                                //       loopInfo.XHeader == thatBlock.startBlock) {
                                //            xheader = true;
                                //            break;
                                //       }
                                //}
								
								if(!xheader) {
									MoverType result = ComputeMoverBranch(thisBlock.Mover, thatBlock.Mover);
									
									ret = any = true;
									
									AtomicBlock newBlock = MakeBranchAtomicBlock(proofState, procState, thisBlock, thatBlock, result);
									
									procState.RemoveAtomicBlock(thisBlock);
									procState.RemoveAtomicBlock(thatBlock);
									
									procState.AddAtomicBlock(newBlock);
								}
							}
						}
					}
				}
			}
			
		} while(iterate && any);
		
		return ret;
	}
#endif
    protected AtomicStmt MakeStraightAtomicStmt(ProofState proofState, ProcedureState procState, AtomicStmt firstAtom, AtomicStmt secondAtom, MoverType mover)
    {
		Output.LogLine("Merging atomic statements: " + firstAtom.label + " and " + secondAtom.label);
        
        // save the big block label of the second block
        InsertAtomLabel(secondAtom);

        firstAtom.body.BigBlocks.AddRange(secondAtom.body.BigBlocks);

        firstAtom.mover = mover.ToEnum();

        return firstAtom;
	}

    public void InsertAtomLabel(AtomicStmt atom)
    {
        BigBlock bb = new BigBlock(atom.tok, atom.label, new CmdSeq(), null, null);

        atom.body.BigBlocks.Insert(0, bb);
    }

#if false
	protected AtomicBlock MakeBranchAtomicBlock(ProofState proofState, ProcedureState procState, AtomicBlock firstBlock, AtomicBlock secondBlock, MoverType mover) {
		Output.LogLine("Merging atomic blocks: " + firstBlock.Label + " and " + secondBlock.Label);
	
		Set<Block> newblocks = new Set<Block>();
		newblocks.AddRange(firstBlock.blocks);
		newblocks.AddRange(secondBlock.blocks);
		
		// create the middle block
		GotoCmd gotoCmd = new GotoCmd(Token.NoToken, new BlockSeq(firstBlock.startBlock, secondBlock.startBlock));
		Block middle = new Block(Token.NoToken, firstBlock.startBlock.Label + "@" + secondBlock.startBlock.Label, new CmdSeq(), gotoCmd);
		newblocks.Add(middle);
		procState.impl.Blocks.Add(middle);
		
		BlockSeq predecessors = new BlockSeq();
		predecessors.AddRange(firstBlock.startBlock.Predecessors);
		predecessors.AddRange(secondBlock.startBlock.Predecessors);
		foreach(Block pred in predecessors) {
			GotoCmd predGoto = (pred.TransferCmd as GotoCmd);
			BlockSeq targets = new BlockSeq();
			foreach(Block succ in predGoto.labelTargets) {
				if(succ != firstBlock.startBlock && succ != secondBlock.startBlock && !targets.Has(succ)) {
					targets.Add(succ);
				}
			}
			if(!targets.Has(middle)) {
				targets.Add(middle);
			}
			pred.TransferCmd = new GotoCmd(Token.NoToken, targets);
		}
		
		AtomicBlock atomicBlock = new AtomicBlock(procState, newblocks, middle);
		
		atomicBlock.InheritAnnotations(firstBlock);
		
		atomicBlock.Mover = mover;
		
		procState.RecomputeBlockPredecessors();
		
		return atomicBlock;
	}

	protected bool RemoveSmallBlocks(ProofState proofState, ProcedureState procState, AtomicBlock newBlock) {
		Set<AtomicBlock> blocksToRemove = new Set<AtomicBlock>();
		
		foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
			if(newBlock.blocks.Includes(atomicBlock.blocks)) {
				blocksToRemove.Add(atomicBlock);
			}
		}
		
		foreach(AtomicBlock blockToRemove in blocksToRemove) {
			procState.RemoveAtomicBlock(blockToRemove);
		}
		return blocksToRemove.Count != 0;
	}
#endif
    
    protected MoverType ComputeMoverTryCatch(TryCatchStmt trycatch)
    {
        MoverType ret = null;
        AtomicStmt tryAtom = trycatch.body.BigBlocks[0].ec as AtomicStmt;
        foreach (CatchStmt catchStmt in trycatch.catchList)
        {
            AtomicStmt catchAtom = catchStmt.body.BigBlocks[0].ec as AtomicStmt;
            MoverType result = MoverType.ComposeSeq(MoverType.FromEnum(tryAtom.mover), MoverType.FromEnum(catchAtom.mover));
            if (result == null) return null;
            ret = ret == null ? result : MoverType.ComposeCho(ret, result);
        }

        return ret;
    }
	
	
} // end class MergeCommand



} // end namespace QED