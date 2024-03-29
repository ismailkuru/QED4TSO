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
using Microsoft.Glee.Drawing;
using Graphing;
using Type = Microsoft.Boogie.Type;
using PureCollections;
    
    public class CodeTransformations
    {
        private static int nextGuardId = 0;
        static public void CorrectGuards(ProcedureState procState, StmtList stmt, bool inAtom)
        {
            for (int i = 0; i < stmt.BigBlocks.Count; ++i)
            {
                BigBlock bb = stmt.BigBlocks[i];

                IfCmd ifCmd = bb.ec as IfCmd;
                if (ifCmd != null)
                {
                    CorrectGuards(procState, ifCmd, null, bb, inAtom);
                    
                    // the handle the parts of if
                    CorrectGuards(procState, ifCmd.thn, inAtom);
                    if (ifCmd.elseBlock != null) CorrectGuards(procState, ifCmd.elseBlock, inAtom);
                    Debug.Assert(ifCmd.elseIf == null);
                }
                else
                {
                    WhileCmd whileCmd = bb.ec as WhileCmd;
                    if (whileCmd != null)
                    {
                        CorrectGuards(procState, whileCmd, bb, inAtom);
                        
                        // add body of while
                        CorrectGuards(procState, whileCmd.Body, inAtom);
                    }
                    else
                    {
                        APLStmt aplStmt = bb.ec as APLStmt;
                        if (aplStmt != null)
                        {
                            bool isAtom = aplStmt is AtomicStmt;
                            foreach (StmtList body in aplStmt.bodies)
                            {
                                CorrectGuards(procState, body, isAtom);
                            }
                        }
                    }
                }
            }
        }

        private static void CorrectGuards(ProcedureState procState, WhileCmd whileCmd, BigBlock bb, bool inAtom)
        {
            Expr guard = whileCmd.Guard;
            if (guard != null && !inAtom && !CodeAnalyses.IsLocalExpr(guard))
            {
                BoogiePL.Errors.SemErr(whileCmd.tok, "Guard of the while statement must be a local expression!");

                Variable guardVar = procState.CreateFreshLocalVar("guard_" + (nextGuardId++).ToString(), BasicType.Bool);
                Cmd guardCmd = AssignCmd.SimpleAssign(Token.NoToken, new IdentifierExpr(Token.NoToken, guardVar), guard);
                bb.simpleCmds.Add(guardCmd);
                whileCmd.Guard = guard = new IdentifierExpr(Token.NoToken, guardVar);

                // at the end of the while body
                CodeTransformations.InstrumentContinue(whileCmd.Body, new CmdSeq(Qoogie.DuplicateCmd(guardCmd)), inAtom);
            }

            // TODO: think over this more
            // CodeTransformations.InstrumentEntry(whileCmd.Body, new CmdSeq(new AssertCmd(Token.NoToken, whileCmd.Guard)), true);

            //whileCmd.Guard = null;

            //// add assumption in body
            //AssumeCmd assumeIn = new AssumeCmd(Token.NoToken, guard);
            //StmtList body = whileCmd.Body;
            //Debug.Assert(body.BigBlocks.Count > 0);

            //CmdSeq newCmds = new CmdSeq();
            //newCmds.Add(assumeIn);
            //newCmds.AddRange(body.BigBlocks[0].simpleCmds);
            //body.BigBlocks[0].simpleCmds = newCmds;

            //newbbs.Add(bb);

            //// add assumption after body
            //AssumeCmd assumeAfter = new AssumeCmd(Token.NoToken, Expr.Not(guard));
            //// we know that bb.tc == null, so either last block or not
            //if (bb.successorBigBlock == null)
            //{
            //    BigBlock afterbb = new BigBlock(Token.NoToken, null, new CmdSeq(assumeAfter), null, null);
            //    newbbs.Add(afterbb);
            //}
            //else
            //{
            //    bb.successorBigBlock.simpleCmds.Add(assumeAfter);
            //}
        }

        private static void InstrumentContinue(StmtList whileBody, CmdSeq cmdSeq, bool inAtom)
        {
            // insert checks before continue
            Set<BigBlock> bbs = new BigBlocksCollector().Collect(whileBody);

            foreach (BigBlock bb in bbs)
            {
                if (bb.tc is ThrowCmd)
                {
                    ThrowCmd thrw = bb.tc as ThrowCmd;
                    if (thrw.ex.Equals(ProofState.GetInstance().exContinueExpr))
                    {
                        CmdSeq dupCmds = Qoogie.DuplicateCmdSeq(cmdSeq);

                        if (!inAtom)
                        {
                            AtomicStmt atom = Qoogie.MakeAtomicStmt(dupCmds, null, null);
                            bb.ec = atom; // bb.ec was previously null
                            bb.tc = null;
                            SetLabel(atom, bb);
                            BigBlock newbb = new BigBlock(Token.NoToken, null, new CmdSeq(), null, thrw);
                            CodeTransformations.InsertAfter(whileBody, bb, newbb);
                        }
                        else
                        {
                            bb.simpleCmds.AddRange(dupCmds);
                        }
                    }
                }
            }

            // insert the final check
            BigBlock lastbb = whileBody.BigBlocks[whileBody.BigBlocks.Count - 1];
            if (lastbb.tc == null) // do only if the last bb in while body does not go anywhere (if it is Continue, it was dealt with above)
            {
                BigBlock endbb;
                if (!inAtom)
                {
                    AtomicStmt endatom = Qoogie.MakeAtomicStmt(cmdSeq, null, null);
                    if (lastbb.ec == null)
                    {
                        lastbb.ec = endatom;
                        SetLabel(endatom, lastbb);
                    }
                    else
                    {
                        endbb = new BigBlock(Token.NoToken, endatom.label, new CmdSeq(), endatom, null);
                        whileBody.BigBlocks.Add(endbb);
                    }
                }
                else
                {

                    if (lastbb.ec == null)
                    {
                        lastbb.simpleCmds.AddRange(cmdSeq);
                    }
                    else
                    {
                        endbb = new BigBlock(Token.NoToken, null, cmdSeq, null, null);
                        whileBody.BigBlocks.Add(endbb);
                    }
                }
            }            
        }

        private static void SetLabel(AtomicStmt atom, BigBlock bb)
        {
            if (bb.Anonymous)
            {
                bb.LabelName = atom.label;
                bb.Anonymous = false;
            }
            else
            {
                atom.label = bb.LabelName;
            }
        }

        private static void CorrectGuards(ProcedureState procState, IfCmd currentIf, Expr parentGuard, BigBlock parentBB, bool inAtom)
        {
            Expr currentGuard = currentIf.Guard;

            if (currentGuard != null && !inAtom && !CodeAnalyses.IsLocalExpr(currentGuard))
            {
                BoogiePL.Errors.SemErr(currentIf.tok, "Guard of the if statement must be a local expression!");

                Variable guardVar = procState.CreateFreshLocalVar("guard_" + (nextGuardId++).ToString(), BasicType.Bool);
                parentBB.simpleCmds.Add(AssignCmd.SimpleAssign(Token.NoToken, new IdentifierExpr(Token.NoToken, guardVar), currentGuard));
                currentIf.Guard = currentGuard = new IdentifierExpr(Token.NoToken, guardVar);
            }

            // TODO: think over this more
            // CodeTransformations.InstrumentEntry(currentIf.thn, new CmdSeq(new AssertCmd(Token.NoToken, currentIf.Guard)), true);
            
            if (currentIf.elseBlock != null)
            {
                // TODO: think over this more
                // CodeTransformations.InstrumentEntry(currentIf.elseBlock, new CmdSeq(new AssertCmd(Token.NoToken, Expr.Not(currentIf.Guard))), true);
            }
            else
            if (currentIf.elseIf != null)
            {
                IfCmd elseIf = currentIf.elseIf;

                // reorganize to make elseif else block
                BigBlock elseIfbb = new BigBlock(elseIf.tok, null, new CmdSeq(
                    // TODO: think over this more
                    // new AssertCmd(Token.NoToken, Expr.Not(currentIf.Guard))
                    ), elseIf, null);
                List<BigBlock> elseIfbbs = new List<BigBlock>();
                elseIfbbs.Add(elseIfbb);
                StmtList elseIfstmt = new StmtList(elseIfbbs, Token.NoToken);

                currentIf.elseBlock = elseIfstmt;
                currentIf.elseIf = null;
            }
        }

        // now parentGuard is always "null" ! and does not propagate to elseIf
        private static void TranslateToIfStar(ProcedureState procState, IfCmd currentIf, Expr parentGuard, bool inAtomic, bool insertAssume)
        {
            Expr currentGuard = currentIf.Guard;

            Debug.Assert(currentGuard != null || parentGuard != null);

            currentIf.Guard = null; // reset the guard to null

            Expr thenGuard = (parentGuard == null ? currentGuard : (currentGuard == null ? parentGuard : Expr.And(parentGuard, currentGuard)));
            Expr elseGuard = (parentGuard == null ? Expr.Not(currentGuard) : (currentGuard == null ? parentGuard : Expr.And(parentGuard, Expr.Not(currentGuard))));

            if (insertAssume)
            {
                AssumeCmd assumeThn = new AssumeCmd(Token.NoToken, thenGuard);
                InstrumentEntry(currentIf.thn, new CmdSeq(assumeThn), inAtomic);
            }

            Debug.Assert(currentIf.elseIf == null);

            if (currentIf.elseBlock == null)
            {
                //if (currentIf.elseIf != null)
                //{
                //    IfCmd elseIf = currentIf.elseIf;

                //    TranslateToIfStar(procState, elseIf, elseGuard, inAtomic);

                //    // reorganize to make elseif else block
                //    BigBlock elseIfbb = new BigBlock(elseIf.tok, null, new CmdSeq(), elseIf, null);
                //    List<BigBlock> elseIfbbs = new List<BigBlock>();
                //    elseIfbbs.Add(elseIfbb);
                //    StmtList elseIfstmt = new StmtList(elseIfbbs, Token.NoToken);

                //    currentIf.elseBlock = elseIfstmt;
                //    currentIf.elseIf = null;
                //}

                currentIf.elseBlock = Qoogie.SkipStmt;
            }

            if (insertAssume)
            {
                AssumeCmd assumeEls = new AssumeCmd(Token.NoToken, elseGuard);
                InstrumentEntry(currentIf.elseBlock, new CmdSeq(assumeEls), inAtomic);
            }
        }

        static public void TranslateToAPLStatements(ProcedureState procState, StmtList stmt)
        {
            Qoogie.ResolveStmt(procState, stmt);

            // ! this must be called before TranslateToAPLStatements
            CorrectGuards(procState, stmt, false);

            TranslateToAPLStatements(procState, stmt, false);
        }


        static public void TranslateToAPLStatements(ProcedureState procState, StmtList stmt, bool inAtom)
        {
            List<BigBlock> newBBs = new List<BigBlock>();
            List<BigBlock> newbbs = new List<BigBlock>();

            BigBlock bb = null;
            for (int i = 0; i < stmt.BigBlocks.Count; ++i)
            {
                bb = stmt.BigBlocks[i];

                // first add bb
                if(!inAtom)
                {
                    newbbs.Clear();
                }

                CmdSeq simpleCmds = bb.simpleCmds;
                StructuredCmd ec = bb.ec;
                TransferCmd tc = bb.tc;
                string LabelName = null;

                if(!inAtom)
                {
                    if (!bb.Anonymous)
                    {
                        // reset bb before adding it
                        if (bb.simpleCmds.Length > 0)
                        {
                            bb.simpleCmds = new CmdSeq();
                        }
                        bb.ec = null;
                        bb.tc = null;

                        newbbs.Add(bb);
                    }

                    for (int s = 0; s < simpleCmds.Length; ++s)
                    {
                        Cmd cmd = simpleCmds[s];

                        APLStmt atom;
                        if (cmd is AsyncCallCmd)
                        {
                            atom = Qoogie.MakeForkStmt(cmd as AsyncCallCmd, null, null);
                        }
                        else if (cmd is JoinCmd)
                        {
                            atom = Qoogie.MakeJoinStmt(cmd as JoinCmd, null, null);
                        }
                        else if (cmd is CallCmd)
                        {
                            atom = Qoogie.MakeCallStmt(cmd as CallCmd, null, null);
                        }
                        else
                        {
                            atom = Qoogie.MakeAtomicStmt(new CmdSeq(cmd), null, null);
                        }

                        BigBlock bbatom = new BigBlock(atom.tok, atom.label, new CmdSeq(), atom, null);
                        atom.body.ParentBigBlock = bbatom;
                        atom.body.ParentContext = stmt;

                        newbbs.Add(bbatom);
                    }
                }

                IfCmd ifCmd = ec as IfCmd;
                if (ifCmd != null)
                {
                    TranslateToAPLStatements(procState, ifCmd.thn, inAtom);
                    if (ifCmd.elseBlock != null) TranslateToAPLStatements(procState, ifCmd.elseBlock, inAtom);
                    Debug.Assert(ifCmd.elseIf == null);
                }
                else
                {
                    WhileCmd whileCmd = ec as WhileCmd;
                    if (whileCmd != null)
                    {
                        TranslateToAPLStatements(procState, whileCmd.Body, inAtom);
                    }
                    else
                    {
                        // if the aplstmt is not labeled, label it with the label of the big block
                        // if big block is not labeled, label the big block as well
                        APLStmt aplStmt = ec as APLStmt;
                        if (aplStmt != null)
                        {
                            if (aplStmt.label == null)
                            {
                                // set the label of the atomic statement
                                if (newbbs.Count == 1 && newbbs[0] == bb && !bb.Anonymous)
                                {
                                    Debug.Assert(inAtom || simpleCmds.Length == 0);
                                    aplStmt.label = bb.LabelName;
                                }
                                else
                                {
                                    LabelName = aplStmt.AssignLabel();

                                    if (inAtom) // TODO: why did I put this condition !?
                                    {
                                        bb.Anonymous = false;
                                        bb.LabelName = LabelName;
                                    }
                                }
                            }
                            else
                            {
                                LabelName = aplStmt.label;
                            }

                            foreach (StmtList body in aplStmt.bodies)
                            {
                                TranslateToAPLStatements(procState, body, (inAtom || aplStmt is AtomicStmt || aplStmt is CallStmt || aplStmt is ForkStmt || aplStmt is JoinStmt));
                            }

                            if (aplStmt is TryCatchStmt)
                            {
                                foreach (CatchStmt cstmt in (aplStmt as TryCatchStmt).catchList)
                                {
                                    TranslateToAPLStatements(procState, cstmt.body, inAtom);
                                }
                            }
                        }
                    }
                }

                //----------------------------------------------------
                // this is after simpleCmds and ec are processed
                if (!inAtom)
                {
                    if (tc != null || ec is BreakCmd || ec is ContinueCmd)
                    {
                        AtomicStmt atom = Qoogie.MakeAtomicStmt(new CmdSeq(), ec, tc);
                        atom.body.ParentContext = stmt;

                        if (newbbs.Count == 1 && newbbs[0] == bb)
                        {
                            Debug.Assert(inAtom || simpleCmds.Length == 0);
                            atom.body.ParentBigBlock = bb;
                            bb.ec = atom;
                            bb.tc = null;
                        }
                        else
                        {
                            BigBlock bbatom = new BigBlock(atom.tok, atom.label, new CmdSeq(), atom, null);
                            atom.body.ParentBigBlock = bbatom;
                            newbbs.Add(bbatom);
                        }
                    }
                    else if (ec != null)
                    {
                        if (newbbs.Count == 1 && newbbs[0] == bb)
                        {
                            Debug.Assert(inAtom || simpleCmds.Length == 0);
                            bb.ec = ec;
                            bb.tc = tc;
                        }
                        else
                        {
                            Debug.Assert(!(ec is APLStmt) || LabelName != null);
                            BigBlock newbb = new BigBlock(bb.tok, LabelName, new CmdSeq(), ec, tc);
                            newbbs.Add(newbb);
                        }
                    }

                    Debug.Assert(newbbs.Count > 0);
                    // add bbs to BBs, newbbs is cleared at the beginning of foreach
                    newBBs.AddRange(newbbs);
                }
            }

            if(!inAtom)
            {
                stmt.BigBlocks.Clear();
                stmt.BigBlocks.AddRange(newBBs);
            }

        }

        static public void InstrumentEntry(StmtList stmt, CmdSeq cmds, bool inAtomic)
        {
            if (inAtomic)
            {
                // add cmds to the first bigblock
                BigBlock bb = stmt.BigBlocks[0];
                CmdSeq newCmds = new CmdSeq(cmds);
                newCmds.AddRange(bb.simpleCmds);
                bb.simpleCmds = newCmds;
            }
            else
            {
                AtomicStmt atom = Qoogie.MakeAtomicStmt(cmds, null, null);
                BigBlock newbb = new BigBlock(Token.NoToken, atom.label, new CmdSeq(), atom, null);
                stmt.BigBlocks.Insert(0, newbb);
            }            
        }

        static public void InstrumentExit(StmtList stmt, CmdSeq cmds, bool inAtomic, string exitBlockLabel) {

            List<BigBlock> exitBlocks = new List<BigBlock>();
            
            BigBlocksResolutionContext ctx = new BigBlocksResolutionContext(stmt);
            ctx.RecordSuccessors(stmt, null);

            Set<BigBlock> bbs = new BigBlocksCollector().Collect(stmt);

            IDictionary<string, BigBlock> label2BB = new Dictionary<string, BigBlock>();
            foreach (BigBlock bb in bbs)
            {
                if (bb.LabelName != null)
                {
                    label2BB.Add(bb.LabelName, bb);
                }
            }

            foreach (BigBlock bb in bbs)
            {
                // check if any specific block label is given
                if (exitBlockLabel != null && bb.LabelName != exitBlockLabel)
                {
                    continue;
                }

                // break
                if (bb.ec != null && bb.ec is BreakCmd)
                {
                    BreakCmd breakCmd = bb.ec as BreakCmd;
                    if (!label2BB.ContainsKey(breakCmd.BreakEnclosure.LabelName))
                    {
                        bb.simpleCmds.AddRange(cmds);
                    }
                }
                else // continue
                if (bb.ec != null && bb.ec is ContinueCmd)
                {
                    ContinueCmd continueCmd = bb.ec as ContinueCmd;
                    if (!label2BB.ContainsKey(continueCmd.ContinueEnclosure.LabelName))
                    {
                        bb.simpleCmds.AddRange(cmds);
                    }
                }
                else
                {
                    if (bb.tc != null)
                    {   // return
                        if (bb.tc is ReturnCmd)
                        {
                            bb.simpleCmds.AddRange(cmds);
                        }
                        else
                        {   // goto
                            GotoCmd gotoCmd = bb.tc as GotoCmd;
                            if (!label2BB.ContainsKey(gotoCmd.labelNames[0]))
                            {   
                                // all goto labels must be outside of the atomic newbody
                                foreach (string label in gotoCmd.labelNames)
                                {
                                    Debug.Assert(!label2BB.ContainsKey(label));
                                }

                                bb.simpleCmds.AddRange(cmds);                                
                            }
                        }
                    }
                    //else
                    //{
                    //    // bb.tc == null
                    //    if (bb.ec == null)
                    //    {
                    //        if (bb.successorBigBlock == null || (bb.successorBigBlock != null && !label2BB.ContainsKey(bb.successorBigBlock.LabelName)))
                    //        {
                    //            bb.simpleCmds.AddRange(cmds);
                    //        }
                    //    }
                    //    else
                    //    {   // bb.ec != null
                    //        StmtList parentStmt = Qoogie.GetParentContext(bb.ec);
                    //        Debug.Assert(parentStmt != null);
                    //        BigBlock newbb = new BigBlock(Token.NoToken, null, new CmdSeq(cmds), null, null);
                    //        parentStmt.BigBlocks.Add(newbb);
                    //    }
                    //}
                }
            }

            // finally put at the end a new block
            BigBlock endbb = stmt.BigBlocks[stmt.BigBlocks.Count - 1];
            if(!(endbb.ec is BreakCmd) && !(endbb.ec is ContinueCmd) && endbb.tc == null) {
                BigBlock newbb;
                if (inAtomic)
                {
                    newbb = new BigBlock(Token.NoToken, null, new CmdSeq(cmds), null, null);
                }
                else
                {
                    AtomicStmt atom = Qoogie.MakeAtomicStmt(cmds, null, null);
                    newbb = new BigBlock(Token.NoToken, atom.label, new CmdSeq(), atom, null);
                }
                stmt.BigBlocks.Add(newbb);
            }
        }

        internal static void Inline(ProcedureState callerProc, CallStmt callStmt, ProcedureState procState)
        {
            AtomicStmt procBody = procState.GetAtomicBody();
            // clone the body
            AtomicStmt atom = new StmtDuplicator().VisitAtomicStmt(procBody);

            CallCmd callCmd = callStmt.cmd;
            
            // find out local variables
            // we use this to avoid using redundant local variables of the procedure that do not appear in newbody
            Pair ngvars = Qoogie.CollectNonGlobalVariables(atom.body);
            Set<Variable> locals = ngvars.First as Set<Variable>;
            
            // create fresh local for ngvars
            Hashtable map = new Hashtable();
            foreach(Variable lvar in locals) {
                // create new variable
                Variable fvar = callerProc.CreateFreshLocalVar(lvar.TypedIdent.Type);
                map.Add(lvar, new IdentifierExpr(Token.NoToken, fvar));
            }

            //// inputs
            //if (procState.impl.InParams.Length > 0)
            //{
            //    List<AssignLhs> inLhss = new List<AssignLhs>();
            //    List<Expr> inRhss = new List<Expr>();
            //    for (int j = 0, n = procState.impl.InParams.Length; j < n; ++j)
            //    {
            //        IdentifierExpr iexpr = Logic.Substitute(subst, new IdentifierExpr(Token.NoToken, procState.impl.InParams[j])) as IdentifierExpr;
            //        inLhss.Add(new SimpleAssignLhs(Token.NoToken, iexpr));
            //        inRhss.Add(callCmd.Ins[j]);
            //    }
            //    AssignCmd inAssignCmd = new AssignCmd(Token.NoToken, inLhss, inRhss);
            //    CodeTransformations.InstrumentEntry(newbody.body, new CmdSeq(inAssignCmd));
            //}

            //// outputs
            //if (procState.impl.OutParams.Length > 0)
            //{
            //    List<AssignLhs> outLhss = new List<AssignLhs>();
            //    List<Expr> outRhss = new List<Expr>();
            //    for (int j = 0, n = procState.impl.OutParams.Length; j < n; ++j)
            //    {
            //        outLhss.Add(new SimpleAssignLhs(Token.NoToken, callCmd.Outs[j]));
            //        IdentifierExpr iexpr = Logic.Substitute(subst, new IdentifierExpr(Token.NoToken, procState.impl.OutParams[j])) as IdentifierExpr;
            //        outRhss.Add(iexpr);
            //    }
            //    AssignCmd outAssignCmd = new AssignCmd(Token.NoToken, outLhss, outRhss);
            //    CodeTransformations.InstrumentExit(newbody.body, new CmdSeq(outAssignCmd));
            //}

            // inputs
            for (int j = 0, n = procState.impl.InParams.Length; j < n; ++j)
            {
                map.Add(procState.impl.InParams[j], callCmd.Ins[j]);
            }
            // outputs
            for (int j = 0, n = procState.impl.OutParams.Length; j < n; ++j)
            {
                map.Add(procState.impl.OutParams[j], callCmd.Outs[j]);
            }

            // do substitution
            Substitution subst = Substituter.SubstitutionFromHashtable(map);
            atom = new MySubstituter(subst).VisitAtomicStmt(atom);

            // add as comment the original call
            CommentCmd cmt = new CommentCmd(Output.ToString(callCmd), true);
            CodeTransformations.InstrumentEntry(atom.body, new CmdSeq(cmt), true);

            // original body goes to return, but the inlined body must go to next block
            Debug.Assert(callStmt.body.BigBlocks.Count == 1 && callStmt.body.BigBlocks[0].ec == null);
            
            // deal with return
            bool hasReturn = CodeTransformations.ReplaceReturnWithThrow(atom.body);
            if (hasReturn)
            {
                atom.body = Qoogie.SkipEx(atom.body, callStmt.body.BigBlocks[0].tc, ProofState.GetInstance().exReturnExpr);
            }

            // add preconditions as assertions
            Expr precond = procState.Pre;
            CodeTransformations.InstrumentEntry(atom.body, new CmdSeq(new AssertCmd(Token.NoToken, precond)), true);

            // rename the labels
            RenameLabels(atom.body, callStmt.label);

            // do inline: replace call stmt with atomic stmt
            CodeTransformations.SwapAtoms(callStmt, atom);

            // keep the mover type of the original body
            atom.mover = procBody.mover;

            callerProc.MarkAsTransformed();

        }

        public static bool ReplaceReturnWithThrow(StmtList stmtList)
        {
            bool any = false;

            Set<BigBlock> bbs = new BigBlocksCollector().Collect(stmtList);
            foreach (BigBlock bb in bbs)
            {
                if (bb.tc is ReturnCmd && !(bb.tc is ThrowCmd))
                {
                    bb.tc = new ThrowCmd(bb.tc.tok, ProofState.GetInstance().exReturnExpr);
                    any = true;
                }
                else if (bb.tc is ThrowCmd)
                {
                    ThrowCmd thrw = bb.tc as ThrowCmd;
                    if (thrw.ex.Equals(ProofState.GetInstance().exReturnExpr))
                    {
                        any = true;
                    }
                }
            }
            return any;
        }

        public static bool ReplaceBreakWithThrow(StmtList stmtList)
        {
            bool any = false;

            Set<BigBlock> bbs = new BigBlocksCollector().Collect(stmtList);
            foreach (BigBlock bb in bbs)
            {
                if (bb.ec is BreakCmd)
                {
                    bb.tc = new ThrowCmd(bb.ec.tok, ProofState.GetInstance().exBreakExpr);
                    bb.ec = null;
                    any = true;
                }
                else if (bb.tc is ThrowCmd)
                {
                    ThrowCmd thrw = bb.tc as ThrowCmd;
                    if (thrw.ex.Equals(ProofState.GetInstance().exBreakExpr))
                    {
                        any = true;
                    }
                }
            }
            return any;
        }

        public static bool ReplaceContinueWithThrow(StmtList stmtList)
        {
            bool any = false;

            Set<BigBlock> bbs = new BigBlocksCollector().Collect(stmtList);
            foreach (BigBlock bb in bbs)
            {
                if (bb.ec is ContinueCmd)
                {
                    bb.tc = new ThrowCmd(bb.ec.tok, ProofState.GetInstance().exContinueExpr);
                    bb.ec = null;
                    any = true;
                }
                else if (bb.tc is ThrowCmd)
                {
                    ThrowCmd thrw = bb.tc as ThrowCmd;
                    if (thrw.ex.Equals(ProofState.GetInstance().exContinueExpr))
                    {
                        any = true;
                    }
                }
            }
            return any;
        }
        
        static public void SwapAtoms(APLStmt oldStmt, APLStmt newStmt) {
		    Debug.Assert(oldStmt.body.ParentBigBlock.ec == oldStmt);
		    Debug.Assert(oldStmt.body.ParentContext.BigBlocks.Contains(oldStmt.body.ParentBigBlock));

            newStmt.body.ParentBigBlock = oldStmt.body.ParentBigBlock;
            newStmt.body.ParentContext = oldStmt.body.ParentContext;
            oldStmt.body.ParentBigBlock.ec = newStmt;

            // adjust the labels for transfer cmds
            newStmt.label = oldStmt.label;
        }

        static public StmtList ReplaceBody(APLStmt parent, StmtList newbody)
        {
            StmtList origStmt = parent.body;

            Debug.Assert(parent.body.ParentBigBlock.ec == parent);
            Debug.Assert(parent.body.ParentContext.BigBlocks.Contains(parent.body.ParentBigBlock));

            newbody.ParentBigBlock = parent.body.ParentBigBlock;
            newbody.ParentContext = parent.body.ParentContext;
            parent.body = newbody;

            return origStmt;
        }

        static public StructuredCmd ReplaceStructuredCmd(BigBlock parent, AtomicStmt newbody)
        {
            Debug.Assert(parent.ec != null);

            StructuredCmd currentCmd = parent.ec;

            Qoogie.SetParentContext(newbody, Qoogie.GetParentBigBlock(currentCmd), Qoogie.GetParentContext(currentCmd));
            
            parent.ec = newbody;

            if (parent.Anonymous)
            {
                parent.LabelName = newbody.label;
                parent.Anonymous = false;
            }
            else
            {
                newbody.label = parent.LabelName;
            }

            return currentCmd;
        }

        static public AtomicStmt ReplaceAtom(BigBlock parent, WhileCmd newbody)
        {
            Debug.Assert(parent.ec is AtomicStmt);

            AtomicStmt atom = parent.ec as AtomicStmt;

            newbody.Body.ParentBigBlock = atom.body.ParentBigBlock;
            newbody.Body.ParentContext = atom.body.ParentContext;
            parent.ec = atom;

            return atom;
        }

        #region Make branch
        static public void MakeBranch(ProcedureState procState, BigBlock parent, StmtList elsestmt, VariableSeq newlocals, out AtomicStmt elsebody, out IdentifierExprSeq origModifies)
        {
            Debug.Assert(parent.ec != null);

            StructuredCmd thenbody = parent.ec;

            string atomLbl = AtomicStmt.GenerateLabel() + "_else";
            elsebody = new AtomicStmt(Token.NoToken, atomLbl, elsestmt);

            MakeBranch(parent, elsebody);

            //----------------------------------------------
            foreach (Variable var in newlocals)
            {
                procState.ResolveTypeCheckVar(var);
                procState.AddAuxVar(var as LocalVariable);
            }

            //----------------------------------------------
            // update the cfg
            procState.ForceComputeAtomicBlocks();

            //----------------------------------------------
            // add extra modified variables
            origModifies = procState.impl.Proc.Modifies;

            IdentifierExprSeq newModifies = Util.MakeIdentifierExprSeq(CodeAnalyses.GetAssignedGlobalVars(elsestmt));
            newModifies.AddRange(origModifies);
            newModifies = Util.RemoveDuplicates(newModifies);

            procState.impl.Proc.Modifies = newModifies;

            BoogiePL.Errors.count = 0;
        }

        static public void UndoMakeBranch(ProcedureState procState, BigBlock parent, bool success, VariableSeq newlocals, IdentifierExprSeq origModifies)
        {
            Debug.Assert(parent.ec != null && parent.ec is IfCmd);

            UndoMakeBranch(parent);

            //----------------------------------------------
            if (!success)
            {
                Debug.Assert(newlocals != null);
                foreach (Variable var in newlocals)
                {
                    procState.RemoveLocalVar(var);
                }
            }
            else
            {
                Debug.Assert(newlocals != null);
                foreach (Variable var in newlocals)
                {
                    procState.MakeNonAuxVar(var as LocalVariable);
                }
            }

            //----------------------------------------------
            if (!success)
            {
                Debug.Assert(origModifies != null);
                procState.impl.Proc.Modifies = origModifies;
            }
        }


        static public void MakeBranch(BigBlock parent, AtomicStmt elsebody)
        {
            Debug.Assert(parent.ec != null);

            StructuredCmd thenbody = parent.ec;
            StmtList parentStmt = Qoogie.GetParentContext(thenbody);

            BigBlock thenbb = new BigBlock(thenbody.tok, parent.LabelName, new CmdSeq(), thenbody, null);
            List<BigBlock> thenbbs= new List<BigBlock>();
            thenbbs.Add(thenbb);
            StmtList thenstmt= new StmtList(thenbbs, Token.NoToken);
            thenstmt.ParentBigBlock = parent;
            thenstmt.ParentContext = parentStmt;

            BigBlock elsebb = new BigBlock(elsebody.tok, elsebody.label, new CmdSeq(), elsebody, null);
            List<BigBlock> elsebbs = new List<BigBlock>();
            elsebbs.Add(elsebb);
            StmtList elsestmt = new StmtList(elsebbs, Token.NoToken);
            elsestmt.ParentBigBlock = parent;
            elsestmt.ParentContext = parentStmt;

            IfCmd ifCmd = new IfCmd(Token.NoToken, null, thenstmt, null, elsestmt);

            parent.ec = ifCmd;
            parent.LabelName = null; // now then atom has this label
        }

        static public void UndoMakeBranch(BigBlock parent)
        {
            Debug.Assert(parent.ec != null && parent.ec is IfCmd);

            IfCmd ifbody = parent.ec as IfCmd;
            Debug.Assert(ifbody.thn.BigBlocks.Count == 1 && ifbody.thn.BigBlocks[0].ec != null);

            StructuredCmd thenbody = ifbody.thn.BigBlocks[0].ec;
            Qoogie.SetParentContext(thenbody, parent, ifbody.thn.ParentContext);

            parent.ec = thenbody;
            if (thenbody is AtomicStmt)
            {
                parent.LabelName = (thenbody as AtomicStmt).label; // get back the label of the atom
            }
            else
            {
                if(parent.Anonymous) parent.LabelName = null;
            }
            
        }
        #endregion

        // this creates an atomic body
        static public Implementation CreateImplFromSpec(Procedure proc)
        {
            Hashtable map = new Hashtable();

            // input vars
            VariableSeq inputVars = new VariableSeq();
            for (int i = 0; i < proc.InParams.Length; ++i)
            {
                Formal f = proc.InParams[i] as Formal;
                Formal ff = new Formal(f.tok, new TypedIdent(f.tok, f.Name, f.TypedIdent.Type), true);

                inputVars.Add(ff);
                map.Add(f, new IdentifierExpr(ff.tok, ff));
            }

            // output vars
            VariableSeq outputVars = new VariableSeq();
            for (int i = 0; i < proc.OutParams.Length; ++i)
            {
                Formal f = proc.OutParams[i] as Formal;
                Formal ff = new Formal(f.tok, new TypedIdent(f.tok, f.Name, f.TypedIdent.Type), false);

                outputVars.Add(ff);
                map.Add(f, new IdentifierExpr(ff.tok, ff));
            }

            Substitution subst = Substituter.SubstitutionFromHashtable(map);

            Expr gate = Expr.True;
            foreach (Requires req in proc.Requires)
            {
                if (!req.Free)
                {
                    gate = Expr.And(gate, Logic.Substitute(subst, req.Condition));
                }
            }

            Expr trans = Expr.True;
            foreach (Ensures ens in proc.Ensures)
            {
                if (!ens.Free)
                {
                    trans = Expr.And(trans, Logic.Substitute(subst, ens.Condition));
                }
            }

            IdentifierExprSeq mods = new IdentifierExprSeq(proc.Modifies);
		    // outputs
		    for(int j = 0, n = proc.OutParams.Length; j < n; ++j) {
			    mods.Add(map[proc.OutParams[j]] as IdentifierExpr);
		    }

            GatedAction gact = new GatedAction(Token.NoToken, gate, trans, mods, true);

            // now create the body
            BigBlock bb = new BigBlock(Token.NoToken, null, new CmdSeq(gact), null, null);
            List<BigBlock> bbs = new List<BigBlock>();
            bbs.Add(bb);
            StmtList atomstmt = new StmtList(bbs, Token.NoToken);

            string atomLbl = proc.Name + "_Body";

            AtomicStmt atom = new AtomicStmt(Token.NoToken, atomLbl, atomstmt);

            bb = new BigBlock(Token.NoToken, atomLbl, new CmdSeq(), atom, null);
            bbs = new List<BigBlock>();
            bbs.Add(bb);
            StmtList bodystmt = new StmtList(bbs, Token.NoToken);


            Implementation impl = new Implementation(proc.tok, proc.Name, proc.TypeParameters, inputVars, outputVars, new VariableSeq(), bodystmt);
            impl.Proc = proc; // TODO: is there still need for resolution and type checking?

            return impl;
        }

        static public Implementation CreateImplFromSpec2(Procedure proc)
        {
            ExprSeq ins = new ExprSeq();
            IdentifierExprSeq outs = new IdentifierExprSeq();

            // input vars
            VariableSeq inputVars = new VariableSeq();
            for (int i = 0; i < proc.InParams.Length; ++i)
            {
                Formal f = proc.InParams[i] as Formal;
                Formal ff = new Formal(f.tok, new TypedIdent(f.tok, f.Name, f.TypedIdent.Type), true);
                
                inputVars.Add(ff);
                ins.Add(new IdentifierExpr(ff.tok, ff));
            }

            // output vars
            VariableSeq outputVars = new VariableSeq();
            for (int i = 0; i < proc.OutParams.Length; ++i)
            {
                Formal f = proc.OutParams[i] as Formal;
                Formal ff = new Formal(f.tok, new TypedIdent(f.tok, f.Name, f.TypedIdent.Type), false);
                
                outputVars.Add(ff);
                outs.Add(new IdentifierExpr(ff.tok, ff));
            }
            
            // dummy call cmd
            CallCmd callCmd = new CallCmd(Token.NoToken, proc.Name, ins, outs);
            callCmd.Proc = proc; // TODO: is there still need for resolution and type checking?

            // decugar the call command           
            StateCmd stateCmd = callCmd.Desugaring as StateCmd;
            Debug.Assert(stateCmd != null);

            // now create the body
            BigBlock bb = new BigBlock(Token.NoToken, null, stateCmd.Cmds, null, null);
            List<BigBlock> bbs = new List<BigBlock>();
            bbs.Add(bb);
            StmtList atomstmt = new StmtList(bbs, Token.NoToken);

            string atomLbl = proc.Name + "_Body";

            AtomicStmt atom = new AtomicStmt(Token.NoToken, atomLbl, atomstmt);

            bb = new BigBlock(Token.NoToken, atomLbl, new CmdSeq(), atom, null);
            bbs = new List<BigBlock>();
            bbs.Add(bb);
            StmtList bodystmt = new StmtList(bbs, Token.NoToken);


            Implementation impl = new Implementation(proc.tok, proc.Name, proc.TypeParameters, inputVars, outputVars, stateCmd.Locals, bodystmt);
            impl.Proc = proc; // TODO: is there still need for resolution and type checking?

            return impl;
        }

        static public void RenameLabels(StmtList stmtList, string prefix) {

            prefix = ((prefix == null) ? "" : (prefix + "_"));
            
            Set<BigBlock> bbs = new BigBlocksCollector().Collect(stmtList);
            foreach (BigBlock bb in bbs)
            {
                // is anonymous, just clear the label, this is relabeled later
                if (bb.Anonymous)
                {
                    bb.LabelName = null;
                }
                else
                {
                    bb.LabelName = prefix + bb.LabelName;

                    if (bb.ec is APLStmt)
                    {
                        APLStmt aplStmt = bb.ec as APLStmt;
                        aplStmt.label = bb.LabelName;
                    }
                }

                // take care of tc
                if (bb.tc is ThrowCmd)
                {
                    ThrowCmd thrw = bb.tc as ThrowCmd;
                    if (thrw.catchStmt != null)
                    {
                        thrw.catchStmt.GotoLabel = prefix + thrw.catchStmt.GotoLabel;
                    }
                }
                else if (bb.tc is GotoCmd)
                {
                    // note that there is no loop in newbody, so no back edge to newbody, so we just add the prefix
                    StringSeq seq = new StringSeq();
                    GotoCmd gotoCmd = bb.tc as GotoCmd;
                    foreach (string lbl in gotoCmd.labelNames)
                    {
                        seq.Add(prefix + lbl);
                    }
                    gotoCmd.labelNames = seq;
                }
            }
        }


        // remove the assertions
        internal static void RelaxStmt(StmtList stmtList, CmdSeq assertions, bool makeAssume)
        {
            Set<BigBlock> bbs = new BigBlocksCollector().Collect(stmtList);
            foreach (BigBlock bb in bbs)
            {
                bb.simpleCmds = RelaxCmdSeq(bb.simpleCmds, assertions, makeAssume);
            }
        }

        // for tressa 
        // remove the tressa claims
        internal static void RelaxStmtForTressa(StmtList stmtList)
        {
            Set<BigBlock> bbs = new BigBlocksCollector().Collect(stmtList);
            foreach (BigBlock bb in bbs)
            {
                bb.simpleCmds = RelaxCmdSeqForTressa(bb.simpleCmds);
            }
        }

        // remove assertions from cmdsToRelax
        // if GatedAction, do not remove but make its gate true.
        internal static CmdSeq RelaxCmdSeq(CmdSeq cmdsToRelax, CmdSeq assertions, bool makeAssume)
        {
            if (cmdsToRelax.Length > 0)
            {
                CmdSeq newCmds = new CmdSeq();
                for (int i = 0; i < cmdsToRelax.Length; ++i)
                {
                    Cmd cmd = cmdsToRelax[i];
                    if (assertions.Has(cmd))
                    {
                        CommentCmd cmt = new CommentCmd(Output.ToString(cmd) + " [Discharged]", true);
                        newCmds.Add(cmt);

                        if (cmd is GatedAction)
                        {
                            GatedAction gact = cmd as GatedAction;
                            GatedAction gactnew = new GatedAction(gact.tok, Expr.True, gact.action, gact.mod, gact.checkAssert);
                            if (makeAssume)
                            {
                                gactnew.action = Expr.And(gact.gate, gactnew.action);
                            }
                            newCmds.Add(gactnew);
                        }
                        else
                        {
                            AssertCmd assertCmd = cmd as AssertCmd;
                            Debug.Assert(assertCmd != null);
                            if (makeAssume)
                            {
                                newCmds.Add(new AssumeCmd(Token.NoToken, assertCmd.Expr));
                            }
                        }
                    }
                    else
                    {
                        newCmds.Add(cmd);
                    }
                }
                return newCmds;
            }
            return cmdsToRelax;
        }

        // for tressa
        internal static CmdSeq RelaxCmdSeqForTressa(CmdSeq cmdsToRelax)
        {
            if (cmdsToRelax.Length > 0)
            {
                CmdSeq newCmds = new CmdSeq();
                for (int i = 0; i < cmdsToRelax.Length; ++i)
                {
                    Cmd cmd = cmdsToRelax[i] as TressaCmd;
                    if (cmd != null)
                    // if (assertions.Has(cmd))
                    {
                        CommentCmd cmt = new CommentCmd(Output.ToString(cmd) + " [Discharged]", true);
                        newCmds.Add(cmt);

                        //if (cmd is GatedAction)
                        //{
                        //    GatedAction gact = cmd as GatedAction;
                        //    GatedAction gactnew = new GatedAction(gact.tok, Expr.True, gact.action, gact.mod, gact.checkAssert);
                        //    if (makeAssume)
                        //    {
                        //        gactnew.action = Expr.And(gact.gate, gactnew.action);
                        //    }
                        //    newCmds.Add(gactnew);
                        //}
                        //else
                        //{
                        //    AssertCmd assertCmd = cmd as AssertCmd;
                        //    Debug.Assert(assertCmd != null);
                        //    if (makeAssume)
                        //    {
                        //        newCmds.Add(new AssumeCmd(Token.NoToken, assertCmd.Expr));
                        //    }
                        //}
                    }
                    else
                    {
                        newCmds.Add(cmdsToRelax[i]);
                    }
                }
                return newCmds;
            }
            return cmdsToRelax;
        }

        internal static bool Hoist(ProcedureState procState, AtomicStmt atom, bool isAfter)
        {
            Qoogie.ResolveStmt(procState, procState.Body);

            //------------------------------------------------
            BigBlock atomBB = atom.body.ParentBigBlock;
            StmtList parentStmt = atom.body.ParentContext;

            AtomicStmt clonedAtom = new StmtDuplicator().VisitAtomicStmt(atom);
            clonedAtom.label = clonedAtom.label + "_else";
            BigBlock clonedBB = new BigBlock(clonedAtom.tok, clonedAtom.label, new CmdSeq(), clonedAtom, null);

            //------------------------------------------------
            // find the statement
            BigBlock stmtBB = null;
            int atomIdx = -1;
            int stmtIdx = -1;
            for (int i = 0; i < parentStmt.BigBlocks.Count; ++i)
            {
                if (parentStmt.BigBlocks[i] == atomBB)
                {
                    atomIdx = i;
                    Debug.Assert(parentStmt.BigBlocks[atomIdx] == atomBB);
                    stmtIdx = isAfter ? i + 1 : i - 1;
                    Debug.Assert(0 <= stmtIdx && stmtIdx < parentStmt.BigBlocks.Count);
                    stmtBB = parentStmt.BigBlocks[stmtIdx];
                    Debug.Assert((isAfter && atomBB.successorBigBlock == stmtBB) || (!isAfter && stmtBB.successorBigBlock == atomBB));
                    
                    break;                    
                }
            }

            if (stmtBB == null || stmtBB.ec == null || !(stmtBB.ec is IfCmd) || (Math.Abs(atomIdx - stmtIdx) != 1))
            {
                Output.AddError("Statement block is not found or is not adjacent to " + atom.label);
                return false;
            }

            // now do hoist
            // insert newbody into if
            IfCmd ifCmd = stmtBB.ec as IfCmd;
            Debug.Assert(ifCmd.elseIf == null);

            //------------------------------------------------
            // now insert the atom to then and else branches
            CodeTransformations.InsertAt(ifCmd.thn, atomBB, isAfter ? 0 : ifCmd.thn.BigBlocks.Count);

            if (ifCmd.elseBlock != null)
            {
                CodeTransformations.InsertAt(ifCmd.elseBlock, clonedBB, isAfter ? 0 : ifCmd.elseBlock.BigBlocks.Count);
            }
            else
            {
                // create an else block
                List<BigBlock> newbbs = new List<BigBlock>();
                newbbs.Add(clonedBB);
                ifCmd.elseBlock = new StmtList(newbbs, Token.NoToken);
            }

            // generate new stmtlist
            CodeTransformations.RemoveAt(parentStmt, atomIdx);

            //------------------------------------------------
            // remove the guard and add it as assumption
            Expr guard = ifCmd.Guard;
            if (isAfter && guard != null)
            {
                TranslateToIfStar(procState, ifCmd, null, false, false /*!*/);

                // insert the guard after the atomic blocks
                AssumeCmd assumeThn = new AssumeCmd(Token.NoToken, guard);
                InstrumentExit(atom.body, new CmdSeq(assumeThn), true, null);

                AssumeCmd assumeEls = new AssumeCmd(Token.NoToken, Expr.Not(Qoogie.DuplicateExpr(guard)));
                InstrumentExit(clonedAtom.body, new CmdSeq(assumeEls), true, null);

                Debug.Assert(ifCmd.Guard == null);
            }

            // change the label of the main atom
            atom.label = atomBB.LabelName = atom.label + "_then";

            return true;
        }

        internal static bool SplitIf(ProcedureState procState, AtomicStmt atom)
        {
            Qoogie.ResolveStmt(procState, procState.Body);

            //------------------------------------------------
            BigBlock atomBB = atom.body.ParentBigBlock;
            StmtList parentStmt = atom.body.ParentContext.ParentContext;
            BigBlock parentBB = atom.body.ParentContext.ParentBigBlock;
            
            Debug.Assert(parentBB.ec != null && parentBB.ec is IfCmd);
            IfCmd ifCmd = parentBB.ec as IfCmd;

            Debug.Assert(ifCmd.elseBlock == null, "We only support then parts for now!");

            int idx = Qoogie.GetIndex(parentBB, parentStmt);
            
            StmtList body = ifCmd.thn;
            
            parentStmt.BigBlocks.RemoveAt(idx);
            //------------------------------------------------
            string label = parentBB.Anonymous ? null : parentBB.LabelName;
            for (int i = 0; i < body.BigBlocks.Count; ++i)
            {
                List<BigBlock> newbbs = new List<BigBlock>();
                newbbs.Add(body.BigBlocks[i]);
                StmtList newstmt = new StmtList(newbbs, Token.NoToken);

                IfCmd newif = new IfCmd(Token.NoToken, Qoogie.DuplicateExpr(ifCmd.Guard), newstmt, null, null);
                BigBlock newbb = new BigBlock(Token.NoToken, label, new CmdSeq(), newif, null);
                label = null;
                parentStmt.BigBlocks.Insert(idx, newbb);
                ++idx;
            }

            return true;
        }

        internal static void InsertAt(StmtList parent, BigBlock bb, int index)
        {
            parent.BigBlocks.Insert(index, bb);
        }

        internal static void InsertBefore(BigBlock bb, BigBlock newbb)
        {
            Debug.Assert(bb.ec != null);
            StmtList parentStmt = Qoogie.GetParentContext(bb.ec);
            Debug.Assert(parentStmt != null);

            int found = -1;
            int i = 0;
            for (; i < parentStmt.BigBlocks.Count; ++i)
            {
                if (parentStmt.BigBlocks[i] == bb)
                {
                    found = i;
                    break;
                }
            }
            Debug.Assert(found >= 0);

            InsertAt(parentStmt, newbb, i);
        }
        
        internal static void RemoveAt(StmtList parent, int index)
        {
            parent.BigBlocks.RemoveAt(index);
        }
        
        // if the body is not in an atomic stmt then surround it in an atomic stmt
        internal static void MakeAtomic(StmtList stmtList)
        {
            BigBlock bb = stmtList.BigBlocks[0];
            if (!(bb.ec is AtomicStmt))
            {
                List<BigBlock> bbs = new List<BigBlock>();
                bbs.AddRange(stmtList.BigBlocks);
                StmtList atomstmt = new StmtList(bbs, stmtList.EndCurly);
                AtomicStmt atom = new AtomicStmt(bb.tok, null, atomstmt);

                bb = new BigBlock(bb.tok, null, new CmdSeq(), atom, null);
                stmtList.BigBlocks.Clear();
                stmtList.BigBlocks.Add(bb);
            }

            Debug.Assert(stmtList.BigBlocks.Count == 1 || (stmtList.BigBlocks.Count == 2) && stmtList.BigBlocks[1].ec == null && stmtList.BigBlocks[1].tc is ReturnCmd);
        }

        internal static void RemoveBigBlock(BigBlock bb)
        {
            Debug.Assert(bb.ec != null);
            StmtList parentStmt = Qoogie.GetParentContext(bb.ec);
            Debug.Assert(parentStmt != null);

            int found = -1;
            int i = 0;
            for (; i < parentStmt.BigBlocks.Count; ++i)
            {
                if (parentStmt.BigBlocks[i] == bb)
                {
                    found = i;
                    break;
                }
            }
            Debug.Assert(found >= 0);

            RemoveAt(parentStmt, i);
        }

        public static void RemoveUnreachableLabels(StmtList stmtList)
        {
            Hashtable labels = new Hashtable();

            Set<BigBlock> bbs = new BigBlocksCollector().Collect(stmtList);
            foreach (BigBlock bb in bbs)
            {
                if (bb.tc is GotoCmd)
                {
                    GotoCmd gotoCmd = bb.tc as GotoCmd;
                    foreach (string label in gotoCmd.labelNames)
                    {
                        labels[label] = null;
                    }
                }
            }

            List<StmtList> stmtLists = new StmtListCollector().Collect(stmtList);

            foreach (StmtList stmt in stmtLists)
            {
                List<BigBlock> newbbs = new List<BigBlock>();
                for (int i = 0; i < stmt.BigBlocks.Count; ++i)
                {
                    BigBlock bb = stmt.BigBlocks[i];
                    if (!(bb.ec is APLStmt) && !(bb.ec is ParallelStmt) && !(bb.ec is ForkStmt) && !bb.Anonymous && !labels.Contains(bb.LabelName))
                    {
                        if (bb.simpleCmds.Length > 0 || bb.ec != null || bb.tc != null)
                        {
                            BigBlock newbb = new BigBlock(bb.tok, null, bb.simpleCmds, bb.ec, bb.tc);
                            newbbs.Add(newbb);
                        }
                    } else
                    {
                        newbbs.Add(bb);
                    }
                }
                stmt.BigBlocks.Clear();
                stmt.BigBlocks.AddRange(newbbs);
            }
        }

        //internal static void MakeNotAnonymous(BigBlock bb)
        //{
        //    Debug.Assert(bb.LabelName != null);

        //    if (bb.Anonymous)
        //    {
        //        Debug.Assert(bb.ec != null);
        //        StmtList parentStmt = Qoogie.GetParentContext(bb.ec);
        //        Debug.Assert(parentStmt != null);
        //        bool found = false;
        //        for (int i = 0; i < parentStmt.BigBlocks.Count; ++i)
        //        {
        //            if (parentStmt.BigBlocks[i] == bb)
        //            {
        //                BigBlock newbb = new BigBlock(bb.tok, bb.LabelName, bb.simpleCmds, bb.ec, bb.tc);
        //                parentStmt.BigBlocks[i] = newbb;
        //                found = true;
        //                break;
        //            }
        //        }
        //        Debug.Assert(found);
        //    }
        //}

        internal static void InsertAfter(StmtList containerStmt, AtomicStmt existing, AtomicStmt atom)
        {
            int index;
            StmtList parent = Qoogie.GetParentContext(existing.body.ParentBigBlock, containerStmt, out index);

            BigBlock bb = new BigBlock(Token.NoToken, atom.label, new CmdSeq(), atom, null);

            InsertAt(parent, bb, index + 1);
        }

        internal static void InsertBefore(StmtList containerStmt, AtomicStmt existing, AtomicStmt atom)
        {
            int index;
            StmtList parent = Qoogie.GetParentContext(existing.body.ParentBigBlock, containerStmt, out index);

            BigBlock bb = new BigBlock(Token.NoToken, atom.label, new CmdSeq(), atom, null);

            InsertAt(parent, bb, index);
        }

        internal static void InsertAfter(StmtList containerStmt, BigBlock existing, BigBlock newbb)
        {
            int index;
            StmtList parent = Qoogie.GetParentContext(existing, containerStmt, out index);

            InsertAt(parent, newbb, index + 1);
        }

        internal static void InsertBefore(StmtList containerStmt, BigBlock existing, BigBlock newbb)
        {
            int index;
            StmtList parent = Qoogie.GetParentContext(existing, containerStmt, out index);

            InsertAt(parent, newbb, index);
        }


        // TODO: this does not modify the gotos to the label
        internal static void RelabelAtomicStmt(AtomicStmt atomicStmt, string newlabel)
        {
            BigBlock bb = Qoogie.GetParentBigBlock(atomicStmt);
            Debug.Assert(bb != null && bb.LabelName == atomicStmt.label);
            bb.LabelName = atomicStmt.label = newlabel;
        }
    } // end CodeTransformations


  
  
} // end namespace QED