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
    using System.Collections;
    using System.Collections.Generic;
    using Microsoft.Boogie;
    using BoogiePL;
    using System.Diagnostics;
    using Type = Microsoft.Boogie.Type;

#if false
    public class ProphecyIntroCommand : ProofCommand
    {
        string varname;

        public ProphecyIntroCommand(string name)
            : base("proph")
        {
            this.varname = name;

            desc = "proph " + varname;
        }

        override public bool Run(ProofState proofState)
        {

            DoRun(proofState);

            return false;
        }

        public Variable DoRun(ProofState proofState)
        {

            if (proofState.GetGlobalVar(varname) != null)
            {
                Output.AddLine("The prophecy variable already exists!");
                return null;
            }

            GlobalVariable prophVar = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, varname, BasicType.Bool));

            // add the prophecy variable as a ordinary global variable
            proofState.AddGlobalVar(prophVar);

            // annotate the blocks
            List<AtomicBlock> atomicBlocks = proofState.GetAllAtomicBlocks();
            foreach (AtomicBlock atomicBlock in atomicBlocks)
            {
                AssumeCmd assumeCmd = new AssumeCmd(Token.NoToken, Expr.Eq(new IdentifierExpr(Token.NoToken, prophVar), Expr.True));
                atomicBlock.InstrumentEntry(new CmdSeq(assumeCmd));
            }

            Output.AddLine("The prophecy variable added!");

            return prophVar;
        }

    } // end class ProphecyIntroCommand


    //-----------------------------------------------------------------------


    public class TrapPredCommand : ProofCommand
    {
        string blockName;
        Expr predicate;

        public TrapPredCommand(string b, Expr p)
            : base("trap")
        {
            this.blockName = b;
            this.predicate = p;

            desc = "trap " + blockName + " " + Output.ToString(predicate);
        }

        override public bool Run(ProofState proofState)
        {

            AtomicBlock atomicBlock = proofState.GetAtomicBlock(blockName);

            if (atomicBlock == null)
            {
                Output.AddError("Atomic block was not found: " + blockName);
                return false;
            }

            DoRun(proofState, atomicBlock);

            return false;
        }

        public void DoRun(ProofState proofState, AtomicBlock atomicBlock)
        {
            bool isTrap = true;

            ProcedureState procState = atomicBlock.procState;

            // resolve-typecheck trap predicate
            procState.ResolveTypeCheckExpr(predicate, false);

            Expr pred = Expr.Imp(predicate, procState.MakePrime(predicate));

            List<AtomicBlock> atomicBlocks = proofState.GetAllAtomicBlocks();
            foreach (AtomicBlock block in atomicBlocks)
            {
                Expr tpred = new TPGenerator(block, true).Compute(TPGenOptions.ComputeTPred);
                Expr condition = Expr.Imp(tpred, pred);

                if (! Prover.GetInstance().CheckValid(condition))
                {
                    Output.AddError("Atomic block does not preserve a true trap predicate: " + block.Label);
                    isTrap = false;
                }
            }

            if (isTrap)
            {
                Output.AddLine("Setting trap predicate for block " + blockName + " :" + Output.ToString(predicate));
                atomicBlock.TrapPredicate = predicate;
            }
            else
            {
                Output.AddError("Trap predicate could not been set for " + blockName);
            }
        }

    } // end class CheckTrapPredCommand


    //-----------------------------------------------------------------------


    public class ConsParCommand : ProofCommand
    {
        string startBlockName;
        string endBlockName;
        string prophVarName;
        Expr trapPred;

        AtomicBlock startAtomicBlock;
        AtomicBlock endAtomicBlock;

        AtomicBlock newstartAtomicBlock = null;
        AtomicBlock newendAtomicBlock = null;

        public ConsParCommand(string sb, string eb, string p, Expr t)
            : base("trap")
        {
            this.startBlockName = sb;
            this.endBlockName = eb;
            this.prophVarName = p;
            this.trapPred = t;

            desc = "conspar " + startBlockName + " " + endBlockName + " " + prophVarName + " " + Output.ToString(trapPred);
        }

        override public bool Run(ProofState proofState)
        {

            this.startAtomicBlock = proofState.GetAtomicBlock(startBlockName);
            
            if (startAtomicBlock == null)
            {
                Output.AddError("Atomic block was not found: " + startBlockName);
                return false;
            }

            this.endAtomicBlock = proofState.GetAtomicBlock(endBlockName);

            if (endAtomicBlock == null)
            {
                Output.AddError("Atomic block was not found: " + endBlockName);
                return false;
            }

            DoRun(proofState);

            return false;
        }

        public void DoRun(ProofState proofState)
        {
            // determine the blocks to clone
            Set<AtomicBlock> blocksToClone = new Set<AtomicBlock>();
            WorkQueue<AtomicBlock, Set<AtomicBlock>> wq = new WorkQueue<AtomicBlock, Set<AtomicBlock>>(new Worker<AtomicBlock, Set<AtomicBlock>>(this.GatherToClone), blocksToClone);
            wq.Enqueue(startAtomicBlock);
            wq.Run();

            Dictionary<Block, Block> blockMap = new Dictionary<Block, Block>();
            Dictionary<AtomicBlock, AtomicBlock> atomicBlockMap = new Dictionary<AtomicBlock, AtomicBlock>();
            Set<AtomicBlock> cloneBlocks = new Set<AtomicBlock>();

            ProcedureState procState = startAtomicBlock.procState;

            // resolve-typecheck trap predicate
            procState.ResolveTypeCheckExpr(trapPred, false);

            // clone the blocks
            foreach (AtomicBlock atomicBlock in blocksToClone)
            {
                AtomicBlock cloneBlock = atomicBlock.Clone(blockMap);
                cloneBlocks.Add(cloneBlock);
                atomicBlockMap.Add(atomicBlock, cloneBlock);
            }

            // remap the gotos
            foreach (AtomicBlock atomicBlock in blocksToClone)
            {
                Debug.Assert(atomicBlockMap.ContainsKey(atomicBlock));
                if (atomicBlock == endAtomicBlock) continue;

                AtomicBlock cloneBlock = atomicBlockMap[atomicBlock];
                foreach (Block newBlock in cloneBlock.blocks)
                {
                    GotoCmd gotoCmd = newBlock.TransferCmd as GotoCmd;
                    if(gotoCmd == null) continue;

                    BlockSeq newTargets = new BlockSeq();
                    foreach (Block gotoBlock in gotoCmd.labelTargets)
                    {
                        if (blockMap.ContainsKey(gotoBlock))
                        {
                            newTargets.Add(blockMap[gotoBlock]); 
                        }
                        else
                        {
                            newTargets.Add(gotoBlock);
                        }
                    }
                    newBlock.TransferCmd = new GotoCmd(Token.NoToken, newTargets);
                }
            }

            // set up the dispatcher to the start blocks
            Block middle = new Block(Token.NoToken, startAtomicBlock.startBlock.Label + "@conspar", new CmdSeq(),
                                new GotoCmd(Token.NoToken, new BlockSeq(startAtomicBlock.startBlock, atomicBlockMap[startAtomicBlock].startBlock)));
            AtomicBlock middleAtomic = new AtomicBlock(startAtomicBlock.procState, middle);
            
            // clone for predecessors		
            if (startAtomicBlock.startBlock.Predecessors.Length > 0)
            {
                foreach (Block predBlock in startAtomicBlock.startBlock.Predecessors)
                {
                    GotoCmd gotoCmd = (predBlock.TransferCmd as GotoCmd);
                    BlockSeq newTargets = new BlockSeq();
                    foreach (Block target in gotoCmd.labelTargets)
                    {
                        if (target != startAtomicBlock.startBlock)
                        {
                            newTargets.Add(target);
                        }
                    }
                    newTargets.Add(middle);
                    predBlock.TransferCmd = new GotoCmd(Token.NoToken, newTargets);
                }
            }

            // add the hang commands
            endAtomicBlock.InstrumentExit(new HangCmd(Token.NoToken, trapPred));
            atomicBlockMap[endAtomicBlock].InstrumentExit(new HangCmd(Token.NoToken, Expr.Not(trapPred)));

            // TODO: add the trap predicae using the trap command
            // set the trap predicate of the last atomic block
            endAtomicBlock.TrapPredicate = trapPred;
            atomicBlockMap[endAtomicBlock].TrapPredicate = Expr.Not(trapPred);
            
            // update the procedure
            foreach (AtomicBlock cloneBlock in cloneBlocks)
            {
                procState.AddAtomicBlock(cloneBlock);
            }
            procState.AddAtomicBlock(middleAtomic);

            procState.MarkAsTransformed();            
        }

        public void GatherToClone(AtomicBlock data, Set<AtomicBlock> blocks, WorkQueue<AtomicBlock, Set<AtomicBlock>> queue)
        {
            blocks.Add(data);

            if (data != endAtomicBlock)
            {
                foreach (AtomicBlock succ in data.Successors)
                {
                    if (!blocks.Contains(succ)) { queue.Enqueue(succ); }
                }
            }            
        }

    } // end class ConsParCommand


    //-----------------------------------------------------------------------


    public class HangCmd : AssumeCmd
    {

        public HangCmd(IToken tok, Expr e)
            : base(tok, e)
        {
            
        }

        public override void Emit(TokenTextWriter stream, int level)
        {
            stream.Write(this, level, "hang ");
            this.Expr.Emit(stream);
            stream.WriteLine(this, ";");
        }
    } // end of HangCmd

#endif

} // end namespace QED