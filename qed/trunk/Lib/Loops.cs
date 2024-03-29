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
using Microsoft.Boogie.AbstractInterpretation;
using AI = Microsoft.AbstractInterpretationFramework;
using Microsoft.Contracts;
using Graphing;
using System.Text;


    public class LoopInvCommand : ProofCommand
    {
        string label;
        Expr formula;

        public LoopInvCommand(string l, Expr f)
            : base("annot inv")
        {
            this.label = l;
            this.formula = f;

            desc = "annot inv " + label + " " + Output.ToString(formula);
        }

        override public bool Run(ProofState proofState)
        {

            DoRun(proofState);

            return false;
        }

        public void DoRun(ProofState proofState)
        {

            LoopBlock loopBlock = (proofState.GetAtomicBlock(label) as LoopBlock);

            loopBlock.procState.ResolveTypeCheckExpr(formula, true);

            // update commands of the header

            loopBlock.AddLoopInv(formula);
        }

    } // end class LoopInvCommand


    public class LoopInfo
    {
        public LoopBlock loopBlock;
        //public Block XHeader;
        public Block Header;
        //public Block YHeader;
        //public BlockSeq ForwardEdges;
        //public CmdSeq PrefixCmds;
        //public Expr Pre;
        //public Expr Post;
        //public VariableSeq ModifiedVars;

        public LoopInfo(Block header)
        {
            this.Header = header;
            //this.ForwardEdges = new BlockSeq();
            //this.PrefixCmds = new CmdSeq();
            //this.Pre = Expr.True;
            //this.Post = Expr.True;
            //this.ModifiedVars = new VariableSeq();
        }

        //public GatedAction Spec {
        //    get {
        //        Expr gate = this.Pre;

        //        Expr action = this.Post;

        //        VariableSeq mod = this.ModifiedVars;

        //        GatedAction gact = new GatedAction(Token.NoToken, gate, action, mod, true);

        //        return gact;
        //    }
        //}

        public string ToString()
        {
            StringBuilder strb = new StringBuilder();

            strb.Append("Header: ").AppendLine(Header.Label);
            //strb.Append("XHeader: ").AppendLine(XHeader.Label);
            //strb.Append("YHeader: ").AppendLine(YHeader.Label);

            //strb.Append("Spec: ").AppendLine(this.Spec.ToString());

            //strb.Append("Forward edges: ");
            //foreach(Block b in ForwardEdges) {
            //    strb.Append(b.Label).Append(" ");
            //}
            //strb.AppendLine();

            ////strb.AppendLine("Prefix commands: ");
            //foreach(Cmd cmd in PrefixCmds) {
            //    strb.Append("\t").Append(Output.ToString(cmd));
            //}

            //strb.Append("Modified variables: ");
            //foreach(Variable v in ModifiedVars) {
            //    strb.Append(v.Name).Append(" ");
            //}
            //strb.AppendLine();

            return strb.ToString();
        }

        public void Reduce(GatedAction spec, AtomicBlock sibling)
        {
            ProcedureState procState = loopBlock.procState;

            AtomicBlock verifiedLoopBlock = loopBlock.GetVerifiedBlock(spec);

            procState.RemoveAtomicBlock(loopBlock);
            procState.RemoveAtomicBlock(sibling);

            procState.AddAtomicBlock(verifiedLoopBlock);

            //// if no other successor of the body, then safe to remove it
            //if (fatomicBlock.Successors.Count == 0)
            //{
            //    // remove the edges to forward blocks
            //    BlockSeq newTargets = new BlockSeq();
            //    GotoCmd gotoCmd = (loopBlock.startBlock.TransferCmd as GotoCmd);
            //    foreach (Block b in gotoCmd.labelTargets)
            //    {
            //        if (b != XHeader)
            //        {
            //            newTargets.Add(b);
            //        }
            //    }
            //    verifiedLoopBlock.startBlock.TransferCmd = new GotoCmd(Token.NoToken, newTargets);

            //    procState.RemoveAtomicBlock(fatomicBlock);
            //}

        }
    }



    public class Loops
    {

        static public IDictionary<Block, LoopInfo> PreProcessLoops(ProcedureState procState, Program program)
        {

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

            foreach (Block header in g.Headers)
            {
                IDictionary<Block, object> backEdgeNodes = new Dictionary<Block, object>();
                foreach (Block b in g.BackEdgeNodes(header)) { backEdgeNodes.Add(b, null); }

                //--------------------------------------------------------------
                // here we intercept the DAG computation
                Output.AddLine("Processing header: " + header.Label);

                // create and add loop header info  
                LoopInfo loopInfo = new LoopInfo(header);
                loopInfoMap.Add(header, loopInfo);

                //GotoCmd headerGoto = (header.TransferCmd as GotoCmd);
                //foreach (Block b in backEdgeNodes.Keys) { 
                //    foreach(Block f in g.NaturalLoops(header, b)) {
                //        if(headerGoto.labelTargets.Has(f)) {
                //            if(!loopInfo.ForwardEdges.Has(f)) {
                //                loopInfo.ForwardEdges.Add(f);
                //            }
                //        }
                //    }
                //}

                //BlockSeq yTargets = new BlockSeq();
                //foreach(Block b in headerGoto.labelTargets) {
                //    if(!loopInfo.ForwardEdges.Has(b)) {
                //        yTargets.Add(b);
                //    }
                //}

                //loopInfo.YHeader = new Block(header.tok, header.Label + "@yheader", new CmdSeq(), new GotoCmd(Token.NoToken, yTargets));
                //impl.Blocks.Add(loopInfo.YHeader);
                //------------------------------------------------------------------

                //CmdSeq cmdsInit = new CmdSeq();
                //CmdSeq cmdsMaintained = new CmdSeq();

                //for (int i = 0, n = header.Cmds.Length; i < n; i++)
                //{
                //    PredicateCmd p = header.Cmds[i] as PredicateCmd;
                //    if (p != null)
                //    {
                //        if (p is AssumeCmd)
                //        {

                //            //loopInfo.PrefixCmds.Add(a);

                //            cmdsInit.Cmds.Add(p);
                //            cmdsMaintained.Add(p);
                //        }
                //        else
                //        {
                //            AssertCmd a = p as AssertCmd;
                //            Debug.Assert(c != null, "PredicateCmd should be either an assume or assert command!");

                //            //loopInfo.PrefixCmds.Add(c);

                //            LoopInitAssertCmd lia = new LoopInitAssertCmd(a.tok, a.Expr);
                //            cmdsInit.Cmds.Add(lia);

                //            LoopInvMaintainedAssertCmd lma = new LoopInvMaintainedAssertCmd(a.tok, a.Expr);
                //            cmdsMaintained.Add(lma);

                //            header.Cmds[i] = new AssumeCmd(a.tok, a.Expr);

                //        }
                //    }
                //    else if (header.Cmds[i] is CommentCmd)
                //    {
                //        // ignore
                //    }
                //    else
                //    {
                //        break; // stop when any other non-predicate cmd is encountered
                //    }
                //}


                //------------------------------------------------------------------------------

                //// TODO: now we do not cut back edges !!!
                //// cut the back edges
                //foreach (Block backEdgeNode in backEdgeNodes.Keys)
                //{
                //  Debug.Assert(backEdgeNode.TransferCmd is GotoCmd,"An node was identified as the source for a backedge, but it does not have a goto command.");
                //  GotoCmd gtc = backEdgeNode.TransferCmd as GotoCmd;
                //  if (gtc != null && gtc.labelTargets != null && gtc.labelTargets.Length > 1 )
                //  {
                //    // then remove the backedge by removing the target block from the list of gotos
                //    BlockSeq remainingTargets = new BlockSeq();
                //    for (int i = 0, n = gtc.labelTargets.Length; i < n; i++)
                //    {
                //      if ( gtc.labelTargets[i] != header )
                //      {
                //        remainingTargets.Add(gtc.labelTargets[i]);
                //      }
                //    }
                //    backEdgeNode.TransferCmd = new GotoCmd(Token.NoToken, remainingTargets);
                //  }
                //  else
                //  {
                //    // This backedge is the only out-going edge from this node.
                //    // Add an "assume false" statement to the end of the statements
                //    // inside of the block and change the goto command to a return command.

                //    // Tayfun: initially disabled, only enabled for verification at the end
                //    CondAssumeCmd ac = new CondAssumeCmd(Token.NoToken,Expr.False, false);
                //    //procState.condAssumesForLoops.Add(ac);

                //    backEdgeNode.Cmds.Add(ac);
                //    backEdgeNode.TransferCmd = new ReturnCmd(Token.NoToken);
                //  }

                //  // remove the backedge node from the list of predecessor nodes in the header
                //  BlockSeq newPreds = new BlockSeq();
                //  foreach ( Block p in header.Predecessors )
                //  {
                //    if ( p != backEdgeNode )
                //      newPreds.Add(p);
                //  }
                //  header.Predecessors = newPreds;          
                //}


                //------------------------------------------------------------------------------

                // collect modified variables
                //foreach (Block backEdgeNode in g.BackEdgeNodes(header))
                //{
                //  foreach (Block b in g.NaturalLoops(header,backEdgeNode))
                //  {
                //    foreach (Cmd c in b.Cmds)
                //    {
                //      c.AddAssignedVariables(loopInfo.ModifiedVars);
                //    }
                //  }
                //}

                // reorganize the commands of the header

                //IdentifierExprSeq havocExprs = new IdentifierExprSeq();
                //foreach (Variable v in varsToHavoc)
                //{
                //  IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
                //  if(!havocExprs.Has(ie))
                //    havocExprs.Add(ie);
                //}
                //// pass the token of the enclosing loop header to the HavocCmd so we can reconstruct
                //// the source location for this later on
                //HavocCmd hc = new HavocCmd(header.tok,havocExprs);

                //CmdSeq newCmds = new CmdSeq();
                //newCmds.AddRange(cmdsInit);
                //newCmds.Add(hc);
                //newCmds.AddRange(header.Cmds);
                //header.Cmds = newCmds;

                //// attach commands maintained
                //foreach (Block b in backEdgeNodes.Keys)
                //{
                //    b.Cmds.AddRange(cmdsMaintained);
                //}

                //// change the goto of header to see xheader
                //BlockSeq newTargets = new BlockSeq(loopInfo.XHeader/*, loopInfo.YHeader*/);
                //header.TransferCmd = new GotoCmd(Token.NoToken, newTargets);

            } // end foreach header

            return loopInfoMap;
        }


    } // end class Loops


} // end namespace QED