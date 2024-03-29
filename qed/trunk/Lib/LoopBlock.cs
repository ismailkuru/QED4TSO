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
using System.Text;
using Graphing;


    public class LoopBlock : AtomicBlock
    {

        protected LoopInfo loopInfo;

        public LoopInfo LoopInfo
        {
            get
            {
                return loopInfo;
            }
        }

        public LoopBlock(ProcedureState pstate, LoopInfo info)
            : base(pstate, info.Header)
        {
            //blocks.Add(info.YHeader);

            this.loopInfo = info;
            info.loopBlock = this;

            this.mover = MoverType.NoneMover;
            this.mover.LeftFixed = true;
            this.mover.RightFixed = true;

            this.IsClonable = false;

            this.CanMerge = false;

            // create commands
            Debug.Assert(startBlock == loopInfo.Header);

            //loopInfo.Header.Cmds = new CmdSeq(loopInfo.PrefixCmds);

            //GatedAction gact = loopInfo.Spec;

            //loopInfo.YHeader.Cmds = new CmdSeq(gact);
        }

        // TODO: reimplement
        //public void UpdateSpec() {
        //    // replace call command with the gated action
        //    CmdSeq cmds = this.startBlock.Cmds;
        //    CmdSeq newCmds = new CmdSeq();

        //    for(int i = 0, n = cmds.Length; i < n; ++i) {
        //        GatedAction gact = cmds[i] as GatedAction;
        //        if(gact != null) {
        //            newCmds.Add(loopInfo.Spec);
        //        } else {
        //            newCmds.Add(cmds[i]);
        //        }
        //    }
        //    loopInfo.YHeader.Cmds = newCmds;
        //}

        public AtomicBlock GetVerifiedBlock(GatedAction spec)
        {

            Block header = loopInfo.Header;

            Debug.Assert(this.blocks.Count == 1);
            Debug.Assert(startBlock == loopInfo.Header);

            Block newHeader = new Block(header.tok, header.Label, new CmdSeq(spec), header.TransferCmd);

            AtomicBlock verifiedBlock = new AtomicBlock(procState, newHeader);
            verifiedBlock.Mover.Right = this.Mover.Right;
            verifiedBlock.Mover.Left = this.Mover.Left;

            return verifiedBlock;
        }

        override public MoverType Mover
        {
            get
            {
                return MoverType.NoneMover;
            }
        }

        #region Transition predicates
        virtual public Expr TransitionPredicate
        {
            get
            {
                Debug.Assert(false, "This should not be used !");
                return Expr.True;
            }
            set
            {
                Debug.Assert(false, "This should not be used !");
            }
        }

        virtual public Expr TransitionPredicateSeq
        {
            get
            {
                AtomicBlock atomicBlock = ComputeSeqBlock();
                return atomicBlock.TransitionPredicate;
            }
        }

        private AtomicBlock ComputeSeqBlock()
        {
            Debug.Assert(this.startBlock == this.loopInfo.Header);
            Block header = this.loopInfo.Header;

            CmdSeq topCmds = new CmdSeq();
            CmdSeq btmCmds = new CmdSeq();

            bool pred = true;
            for (int i = 0, n = header.Cmds.Length; i < n; i++)
            {
                PredicateCmd p = header.Cmds[i] as PredicateCmd;
                if (pred && p != null)
                {
                    if (p is AssumeCmd)
                    {
                        topCmds.Add(p);
                    }
                    else
                    {
                        AssertCmd a = p as AssertCmd;
                        Debug.Assert(a != null, "PredicateCmd should be either an assume or assert command!");

                        topCmds.Add(new LoopInitAssertCmd(a.tok, a.Expr));

                        btmCmds.Add(new AssumeCmd(a.tok, a.Expr));
                    }
                }
                else if (header.Cmds[i] is CommentCmd)
                {
                    // ignore
                }
                else
                {
                    pred = false;
                    btmCmds.Add(header.Cmds[i]);
                }
            }

            //----------------------------------------

            Implementation impl = procState.impl;

            IDictionary<Block, LoopInfo> loopInfoMap = new Dictionary<Block, LoopInfo>();

            impl.PruneUnreachableBlocks();

            // compute loops
            Graph<Block> g = CodeAnalyses.GraphFromImpl(impl);

            g.ComputeLoops(); // this is the call that does all of the processing
            if (!g.Reducible)
            {
                Debug.Assert(false);
            }

            //----------------------------------------

            VariableSeq modifiedVars = new VariableSeq();
            // collect modified variables
            foreach (Block backEdgeNode in g.BackEdgeNodes(header))
            {
                foreach (Block b in g.NaturalLoops(header, backEdgeNode))
                {
                    foreach (Cmd c in b.Cmds)
                    {
                        c.AddAssignedVariables(modifiedVars);
                    }
                }
            }

            IdentifierExprSeq havocExprs = new IdentifierExprSeq();
            foreach (Variable v in modifiedVars)
            {
                IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
                if (!havocExprs.Has(ie))
                    havocExprs.Add(ie);
            }

            //----------------------------------------

            // pass the token of the enclosing loop header to the HavocCmd so we can reconstruct
            // the source location for this later on
            HavocCmd hc = new HavocCmd(header.tok, havocExprs);

            //----------------------------------------

            // build the atomic block
            CmdSeq newCmds = new CmdSeq();
            newCmds.AddRange(topCmds);
            newCmds.Add(hc);
            newCmds.AddRange(btmCmds);

            //----------------------------------------

            Block newHeader = new Block(header.tok, header.Label, newCmds, header.TransferCmd);

            return new AtomicBlock(this.procState, newHeader);
        }

        virtual public Expr GatePredicate(Expr P)
        {
            Debug.Assert(false, "This should not be used !");
            return Expr.True;
        }

        virtual public Expr GatePredicateSeq(Expr P)
        {
            return base.GatePredicate(P);
        }
        #endregion Transition predicates

        override public AtomicBlock Clone(Dictionary<Block, Block> map)
        {
            Debug.Assert(false);
            return this;
        }

        virtual public myNode GraphView
        {
            get
            {

                StringBuilder strb = new StringBuilder();

                strb.Append(UniqueLabel + " : " + Mover.ToString() + "\\n");
                strb.Append(BlockStr);

                myNode node = new myNode(UniqueLabel, strb.ToString(), this.BlockStr, myColor.Black, myColor.White, myColor.Blue, myShape.Box);

                foreach (string sid in this.SuccessorIds)
                {
                    node.Edges.Add(sid);
                }

                return node;
            }
        }


        // this loop invariant is used during sequential analysis
        virtual public void AddLoopInv(Expr formula)
        {
            // add assertion to the header
            CmdSeq newCmds = new CmdSeq();
            // assert formula
            // TODO: should we add the assertion to the beginning or the end?
            newCmds.Add(new LoopInitAssertCmd(Token.NoToken, formula));
            // add existing commands
            newCmds.AddRange(this.loopInfo.Header.Cmds);

            // add assertion to back edges
            Set<Block> backEdges = CodeAnalyses.ComputeBackEdges(this);
            foreach (Block b in backEdges)
            {
                b.Cmds.Add(new LoopInvMaintainedAssertCmd(Token.NoToken, formula));
            }
        }
    }

} // end namespace QED