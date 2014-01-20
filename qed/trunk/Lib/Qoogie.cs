using System;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using Microsoft.Boogie;
using BoogiePL;
using System.Diagnostics;
using Microsoft.Basetypes;
using Type = Microsoft.Boogie.Type;
using System.Drawing;
using System.Text;
using PureCollections;

namespace QED
{
    // colors for text highlighting
    public class TextHighligtingOptions
    {
        static public IDictionary<string, System.Drawing.Color> ColorOptions;
        static public char[] charSet;
        static public System.Drawing.Color charSetColor;

        static TextHighligtingOptions()
        {
            ColorOptions = new Dictionary<string, System.Drawing.Color>();
            ColorOptions.Add("atomic", Color.Red);
            ColorOptions.Add("action", Color.Red);
            ColorOptions.Add("type", Color.Red);
            ColorOptions.Add("const", Color.Red);
            ColorOptions.Add("unique", Color.Red);
            ColorOptions.Add("call", Color.Red);
            ColorOptions.Add("var", Color.Red);
            ColorOptions.Add("if", Color.Red);
            ColorOptions.Add("while", Color.Red);
            ColorOptions.Add("procedure", Color.Blue);
            ColorOptions.Add("implementation", Color.Blue);
            ColorOptions.Add("Set", Color.Blue);
            ColorOptions.Add("Queue", Color.Blue);
            ColorOptions.Add("Mutex", Color.Blue);
            ColorOptions.Add("tid", Color.Blue);
            ColorOptions.Add("fork", Color.Red);
            ColorOptions.Add("join", Color.Red);
            ColorOptions.Add("New", Color.Red);
            ColorOptions.Add("Free", Color.Red);
            ColorOptions.Add("record", Color.Red);
            ColorOptions.Add("dopar", Color.Red);
            ColorOptions.Add("with", Color.Red);
            ColorOptions.Add("else", Color.Red);
            ColorOptions.Add("try", Color.Red);
            ColorOptions.Add("catch", Color.Red);
            ColorOptions.Add("break", Color.Red);
            ColorOptions.Add("continue", Color.Red);
            ColorOptions.Add("return", Color.Red);
            ColorOptions.Add("throw", Color.Red);
            ColorOptions.Add("foreach", Color.Red);
            ColorOptions.Add("in", Color.Red);

            charSet = "{}(),;*:[]".ToCharArray();
            charSetColor = System.Drawing.Color.Green;
        }
    }


    public class Qoogie2Boogie
    {
        public static bool AssumeFalseAtLoops = true;

        public static Expr PcExpr;
        public static bool CheckPc = false;

        public CmdSeq PrefixCmds = new CmdSeq();

        public IDictionary<string, APLStmt> APLStmtMap = new Dictionary<string, APLStmt>();
        public IDictionary<string, APLBlock> APLBlockMap = new Dictionary<string, APLBlock>();
        public IDictionary<WhileCmd, LoopInfo> LoopInfoMap = new Dictionary<WhileCmd, LoopInfo>();
        public List<Block> Blocks = new List<Block>();

        protected BigBlocksResolutionContext rctx;


        public Qoogie2Boogie()
        {
        }

        public void TranslateStmt(ProcedureState procState, StmtList stmtList)
        {
            this.rctx = Qoogie.ResolveStmt(stmtList);
            Debug.Assert(rctx != null);

            if (CheckPc)
            {
                PcExpr = Expr.Eq(procState.pcExpr, ProofState.GetInstance().exSkipExpr);
            }

            TranslateStmt(procState, stmtList, null, false);
        }

        static public TransferCmd GotoSuccessor(IToken tok, BigBlock b, string runOffTheEndLabel)
        {
            if (b.tc != null)
            {
                return b.tc;
            }
            else if (runOffTheEndLabel != null)
            {
                return new GotoCmd(tok, new StringSeq(runOffTheEndLabel));
            }
            else if (b.successorBigBlock != null)
            {
                return new GotoCmd(tok, new StringSeq(b.successorBigBlock.LabelName));
            }
            else
            {
                return new ReturnCmd(tok);
            }
        }

        public void TranslateStmt(ProcedureState procState, StmtList stmtList, string runOffTheEndLabel, bool inAtom)
        {
            int n = stmtList.BigBlocks.Count;
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                --n;
                Debug.Assert(inAtom || bb.simpleCmds.Length == 0);

                TransferCmd tc = bb.tc;
                StructuredCmd scmd = bb.ec;

                if (tc != null)
                {
                    // this BigBlock has the very same components as a Block
                    Debug.Assert(scmd == null);
                    TranslateTransfer(procState, bb.tok, bb.LabelName, bb.simpleCmds, tc, inAtom);
                }
                else
                {
                    string nextLabel = ((n == 0 && runOffTheEndLabel != null) ? runOffTheEndLabel : (bb.successorBigBlock != null ? bb.successorBigBlock.LabelName : null));

                    if (scmd == null)
                    {
                        TransferCmd trCmd = GotoSuccessor(stmtList.EndCurly, bb, nextLabel);
                        TranslateTransfer(procState, bb.tok, bb.LabelName, bb.simpleCmds, trCmd, inAtom);
                    }
                    else
                    {
                        IfCmd ifCmd = scmd as IfCmd;
                        if (ifCmd != null)
                        {
                            //Debug.Assert(ifCmd.Guard == null);
                            TranslateIf(procState, ifCmd, bb, nextLabel, inAtom);
                        }
                        else
                        {
                            WhileCmd whileCmd = scmd as WhileCmd;
                            if (whileCmd != null)
                            {
                                //Debug.Assert(whileCmd.Guard == null);
                                TranslateWhile(procState, whileCmd, bb, nextLabel, inAtom);
                            }
                            else
                            {
                                BreakCmd breakCmd = scmd as BreakCmd;
                                if (breakCmd != null)
                                {
                                    TranslateBreak(procState, breakCmd, bb, inAtom);
                                }
                                else
                                {
                                    ContinueCmd continueCmd = scmd as ContinueCmd;
                                    if (continueCmd != null)
                                    {
                                        TranslateContinue(procState, continueCmd, bb, inAtom);
                                    }
                                    else
                                    {
                                        AtomicStmt atomStmt = scmd as AtomicStmt;
                                        if (atomStmt != null)
                                        {
                                            TranslateAtomicStmt(procState, scmd as AtomicStmt, bb, nextLabel, inAtom);
                                        }
                                        else
                                        {
                                            CallStmt callStmt = scmd as CallStmt;
                                            if (callStmt != null)
                                            {
                                                TranslateCallStmt(procState, scmd as CallStmt, bb, nextLabel, inAtom);
                                            }
                                            else
                                            {
                                                ParallelStmt parStmt = scmd as ParallelStmt;
                                                if (parStmt != null)
                                                {
                                                    Debug.Assert(bb.LabelName == parStmt.label);
                                                    TranslateParStmt(procState, parStmt, bb, nextLabel, inAtom);
                                                }
                                                else
                                                {
                                                    ForkStmt forkStmt = scmd as ForkStmt;
                                                    if (forkStmt != null)
                                                    {
                                                        Debug.Assert(bb.LabelName == forkStmt.label);
                                                        TranslateForkStmt(procState, forkStmt, bb, nextLabel);
                                                    }
                                                    else
                                                    {
                                                        JoinStmt joinStmt = scmd as JoinStmt;
                                                        if (joinStmt != null)
                                                        {
                                                            Debug.Assert(bb.LabelName == joinStmt.label);
                                                            TranslateJoinStmt(procState, joinStmt, bb, nextLabel);
                                                        }
                                                        else
                                                        {
                                                            TryCatchStmt trycatch = scmd as TryCatchStmt;
                                                            if (trycatch != null)
                                                            {
                                                                Debug.Assert(bb.LabelName == trycatch.label);
                                                                TranslateTryCatchStmt(procState, trycatch, bb, nextLabel, inAtom);
                                                            }
                                                            //else
                                                            //{
                                                            //    ForeachStmt feStmt = scmd as ForeachStmt;
                                                            //    if (feStmt != null)
                                                            //    {
                                                            //        Debug.Assert(bb.LabelName == feStmt.label);
                                                            //        TranslateForeachStmt(procState, feStmt, bb, nextLabel, inAtom);
                                                            //    }
                                                            //}
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        private void TranslateTryCatchStmt(ProcedureState procState, TryCatchStmt trycatch, BigBlock parentBB, string runOffTheEndLabel, bool inAtom)
        {
            // ex := ExSkip;
            // PrefixCmds.Add(AssignCmd.SimpleAssign(Token.NoToken, procState.exExpr, ProofState.GetInstance().exSkipExpr));
            
            TransferCmd trCmd = new GotoCmd(trycatch.tok, new StringSeq(trycatch.body.BigBlocks[0].LabelName));
            TranslateTransfer(procState, trycatch.tok, trycatch.label, parentBB.simpleCmds, trCmd, inAtom);

            TranslateStmt(procState, trycatch.body, runOffTheEndLabel, inAtom);

            //------------------
            // translate catch blocks
            foreach (CatchStmt catchStmt in trycatch.catchList)
            {
                TranslateCatchStmt(procState, catchStmt, parentBB, runOffTheEndLabel, inAtom);
            }
        }

        private void TranslateCatchStmt(ProcedureState procState, CatchStmt catchStmt, BigBlock parentBB, string runOffTheEndLabel, bool inAtom)
        {
            //-------------------------------
            if (CheckPc)
            {
                if (catchStmt.labels.Count == 0)
                {
                    PcExpr = Expr.Neq(procState.pcExpr, ProofState.GetInstance().exSkipExpr);
                }
                else
                {
                    Function stf = ProofState.GetInstance().subtypeFunction;
                    FunctionCall stcall = new FunctionCall(new IdentifierExpr(Token.NoToken, stf.Name, stf.OutParams[0].TypedIdent.Type));
                    
                    PcExpr = Expr.False;
                    foreach (IdentifierExpr lbl in catchStmt.labels)
                    {
                        PcExpr = Expr.Or(PcExpr, new NAryExpr(Token.NoToken, stcall, new ExprSeq(procState.pcExpr, lbl)));
                    }
                }
            }
            //-------------------------------
            TranslateStmt(procState, catchStmt.body, runOffTheEndLabel, inAtom);
        }
   

        private void TranslateParStmt(ProcedureState procState, ParallelStmt parStmt, BigBlock parentBB, string runOffTheEndLabel, bool inAtom)
        {
            List<StmtList> bodies = parStmt.bodies;

            // create the fork block
            StringSeq seq = new StringSeq();
            foreach (StmtList body in bodies)
            {
                seq.Add(body.BigBlocks[0].LabelName);
            }
            GotoCmd gotoCmd = new GotoCmd(parStmt.tok, seq);

            TranslateFork(procState, parStmt, parStmt.tok, parentBB.LabelName, gotoCmd, parentBB.simpleCmds);

            string joinLabel = parentBB.LabelName + "_join";

            // translate bodies
            foreach (StmtList body in bodies)
            {
                TranslateStmt(procState, body, joinLabel, inAtom);
            }

            TransferCmd trCmd = GotoSuccessor(parStmt.tok, parentBB, runOffTheEndLabel);
            TranslateJoin(procState, parStmt, parStmt.tok, joinLabel, trCmd, new CmdSeq());
        }

        //private void TranslateForeachStmt(ProcedureState procState, ForeachStmt feStmt, BigBlock parentBB, string runOffTheEndLabel, bool inAtom)
        //{
        //    StmtList body = feStmt.Body;

        //    // create the foreach start block
        //    StringSeq seq = new StringSeq();
        //    seq.Add(body.BigBlocks[0].LabelName);
        //    GotoCmd gotoCmd = new GotoCmd(feStmt.tok, seq);

        //    TranslateTransfer(procState, feStmt.tok, feStmt.label, new CmdSeq(), gotoCmd, inAtom);

        //    // translate the body
        //    TranslateStmt(procState, body, runOffTheEndLabel, inAtom);
        //}

        private void TranslateForkStmt(ProcedureState procState, ForkStmt forkStmt, BigBlock bb, string runOffTheEndLabel)
        {
            TransferCmd trCmd = GotoSuccessor(forkStmt.tok, bb, runOffTheEndLabel);
            
            TranslateFork(procState, forkStmt, forkStmt.tok, bb.LabelName, trCmd, new CmdSeq());
        }

        private void TranslateJoinStmt(ProcedureState procState, JoinStmt joinStmt, BigBlock bb, string runOffTheEndLabel)
        {
            TransferCmd trCmd = GotoSuccessor(joinStmt.tok, bb, runOffTheEndLabel);

            TranslateJoin(procState, joinStmt, joinStmt.tok, bb.LabelName, trCmd, new CmdSeq());
        }

        private void TranslateWhile(ProcedureState procState, WhileCmd whileCmd, BigBlock parentBB, string runOffTheEndLabel, bool inAtom)
        {
            // Debug.Assert(!inAtom);

            string label = parentBB.LabelName;

            StmtList body = whileCmd.Body;

            CmdSeq initInv = new CmdSeq();
            CmdSeq assumeInv = new CmdSeq();
            CmdSeq checkInv = new CmdSeq();

            // collect cmds for checking and assuming loop invariant
            for (int i = 0; i < whileCmd.Invariants.Count; ++i)
            {
                PredicateCmd predCmd = whileCmd.Invariants[i];
                if (predCmd != null)
                {
                    if (predCmd is AssumeCmd)
                    {
                        initInv.Add(predCmd);
                        checkInv.Add(predCmd);
                        assumeInv.Add(predCmd);
                    }
                    else
                    {
                        AssertCmd assertCmd = predCmd as AssertCmd;
                        Debug.Assert(assertCmd != null, "PredicateCmd should be either an assume or assert command!");

                        AssumeCmd assumeCmd = new AssumeCmd(assertCmd.tok, assertCmd.Expr);
                        initInv.Add(assumeCmd);

                        LoopInitAssertCmd lia = new LoopInitAssertCmd(assertCmd.tok, assertCmd.Expr);
                        checkInv.Add(lia);

                        LoopInvMaintainedAssertCmd lma = new LoopInvMaintainedAssertCmd(assertCmd.tok, assertCmd.Expr);
                        assumeInv.Add(lma);
                    }
                }
            }

            // find out assigned variables
            // TODO: Why did I use FilterLocals here? VariableSeq varsToHavoc = Util.FilterLocalVariables(Qoogie.CollectAssignedVarsInLoop(body));
            VariableSeq varsToHavoc = Qoogie.CollectAssignedVarsInLoop(body);
            IdentifierExprSeq havocExprs = new IdentifierExprSeq();
            foreach (Variable v in varsToHavoc)
            {
                IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
                if (!havocExprs.Has(ie))
                    havocExprs.Add(ie);
            }
            HavocCmd havocCmd = null;
            if (havocExprs.Length > 0)
            {
                havocCmd = new HavocCmd(whileCmd.tok, havocExprs);
            }

            // head cmds
            CmdSeq headCmds = new CmdSeq();
            headCmds.AddRange(parentBB.simpleCmds);
            headCmds.AddRange(initInv);
            if(havocCmd != null)
                headCmds.Add(havocCmd);
            headCmds.AddRange(assumeInv);

            string bodyLabel = label + "_body";
            string doneLabel = label + "_done";

            // create the while head
            StringSeq seq = new StringSeq();
            // goto body
            seq.Add(bodyLabel);
            // goto done
            seq.Add(doneLabel);
            GotoCmd gotoCmd = new GotoCmd(whileCmd.tok, seq);
            ControlBlock headBlock = TranslateTransfer(procState, whileCmd.tok, label, headCmds, gotoCmd, inAtom);

            string backlabel = label + "_back";

            // create the back-edge
            CmdSeq backCmds = new CmdSeq(checkInv);
            if (AssumeFalseAtLoops)
            {
                backCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
            }
            ControlBlock tailBlock = TranslateTransfer(procState, whileCmd.tok, backlabel, backCmds, new ReturnCmd(whileCmd.tok), inAtom);

            // translate body
            gotoCmd = new GotoCmd(whileCmd.Body.BigBlocks[0].tok, new StringSeq(whileCmd.Body.BigBlocks[0].LabelName));
            TranslateTransfer(procState, whileCmd.Body.BigBlocks[0].tok, bodyLabel, new CmdSeq(), gotoCmd, inAtom);

            if (whileCmd.Guard != null)
            {
                PrefixCmds.Add(new AssumeCmd(Token.NoToken, whileCmd.Guard));
            }
            TranslateStmt(procState, body, backlabel, inAtom);

            // translate done
            TransferCmd trf = null;
            if (runOffTheEndLabel == null)
            {
                trf = new ReturnCmd(Token.NoToken);
            }
            else
            {
                trf = new GotoCmd(whileCmd.tok, new StringSeq(runOffTheEndLabel));
            }

            CmdSeq cmds = new CmdSeq();
            if (whileCmd.Guard != null)
            {
                cmds.Add(new AssumeCmd(Token.NoToken, Expr.Not(whileCmd.Guard)));
            }
            TranslateTransfer(procState, whileCmd.tok, doneLabel, cmds, trf, inAtom);

            LoopInfoMap.Add(whileCmd, new LoopInfo(parentBB, headBlock, tailBlock));

            if (runOffTheEndLabel != null && CheckPc)
            {
                PcExpr = Expr.Or(Expr.Eq(procState.pcExpr, ProofState.GetInstance().exSkipExpr),
                                 Expr.Eq(procState.pcExpr, ProofState.GetInstance().exBreakExpr));
            }
        }

        private void TranslateBreak(ProcedureState procState, BreakCmd breakCmd, BigBlock parentBB, bool inAtom)
        {
            string label = parentBB.LabelName;

            Debug.Assert(breakCmd.BreakEnclosure != null);

            TransferCmd tc = null; // GotoSuccessor(b.ec.tok, bcmd.BreakEnclosure);
            tc = ThrowCmd.CreateForBreak(breakCmd); // goes to parentBB.LabelName_done
            
            TranslateTransfer(procState, breakCmd.tok, label, parentBB.simpleCmds, tc, inAtom);
        }

        private void TranslateContinue(ProcedureState procState, ContinueCmd continueCmd, BigBlock parentBB, bool inAtom)
        {
            string label = parentBB.LabelName;

            Debug.Assert(continueCmd.ContinueEnclosure != null);

            TransferCmd tc = tc = ThrowCmd.CreateForContinue(continueCmd);  // goes to parentBB.LabelName_back

            TranslateTransfer(procState, continueCmd.tok, label, parentBB.simpleCmds, tc, inAtom);
        }


        private ControlBlock TranslateTransfer(ProcedureState procState, IToken tok, string label, CmdSeq cmds, TransferCmd tc, bool inAtom)
        {
            Block b = TranslateBlock(procState, tok, label, cmds, tc);

            ControlBlock cb = null;
            //if (!inAtom)
            //{
                List<Block> bs = new List<Block>();
                bs.Add(b);
                cb = new ControlBlock(procState, bs, b);

                APLBlockMap.Add(cb.Label, cb);
            //}

            return cb;
        }

        private ControlBlock TranslateFork(ProcedureState procState, StructuredCmd parStmt, IToken tok, string label, TransferCmd tc, CmdSeq cmds)
        {
            Block b = TranslateBlock(procState, tok, label, cmds, tc);

            List<Block> bs = new List<Block>();
            bs.Add(b);
            ForkBlock cb = new ForkBlock(procState, bs, b, parStmt);

            APLBlockMap.Add(cb.Label, cb);

            return cb;
        }

        private ControlBlock TranslateJoin(ProcedureState procState, StructuredCmd parStmt, IToken tok, string label, TransferCmd tc, CmdSeq cmds)
        {
            Block b = TranslateBlock(procState, tok, label, cmds, tc);

            List<Block> bs = new List<Block>();
            bs.Add(b);
            JoinBlock cb = new JoinBlock(procState, bs, b, parStmt);

            APLBlockMap.Add(cb.Label, cb);

            return cb;
        }

        private void TranslateIf(ProcedureState procState, IfCmd ifCmd, BigBlock parentBB, string runOffTheEndLabel, bool inAtom)
        {
            string label = parentBB.LabelName;

            StmtList thenBlock = ifCmd.thn;
            StmtList elseBlock = ifCmd.elseBlock;
       //     Debug.Assert(ifCmd.elseIf == null); // TSO Peelaway icin kapadim.

            string thnLabel = label + "_thn";
            string elsLabel = label + "_els";

            // create the goto of the if head
            StringSeq seq = new StringSeq(thnLabel, elsLabel);
            
            GotoCmd gotoCmd = new GotoCmd(ifCmd.tok, seq);

            TranslateTransfer(procState, ifCmd.tok, label, parentBB.simpleCmds, gotoCmd, inAtom);

            // translate then
            gotoCmd = new GotoCmd(thenBlock.BigBlocks[0].tok, new StringSeq(thenBlock.BigBlocks[0].LabelName));
            CmdSeq cmds = new CmdSeq();
            if(ifCmd.Guard != null)
            {
                cmds.Add(new AssumeCmd(Token.NoToken, ifCmd.Guard));
            }
            TranslateTransfer(procState, thenBlock.BigBlocks[0].tok, thnLabel, cmds, gotoCmd, inAtom);
            
            TranslateStmt(procState, thenBlock, runOffTheEndLabel, inAtom);

            // translate else
            if (elseBlock != null)
            {
                gotoCmd = new GotoCmd(elseBlock.BigBlocks[0].tok, new StringSeq(elseBlock.BigBlocks[0].LabelName));
                cmds = new CmdSeq();
                if (ifCmd.Guard != null)
                {
                    cmds.Add(new AssumeCmd(Token.NoToken, Expr.Not(ifCmd.Guard)));
                }
                TranslateTransfer(procState, elseBlock.BigBlocks[0].tok, elsLabel, cmds, gotoCmd, inAtom);

                TranslateStmt(procState, elseBlock, runOffTheEndLabel, inAtom);
            }
            else
            {
                TransferCmd trf = null;
                if (runOffTheEndLabel == null)
                {
                    trf = new ReturnCmd(Token.NoToken);
                }
                else
                {
                    trf = new GotoCmd(ifCmd.tok, new StringSeq(runOffTheEndLabel));
                }

                cmds = new CmdSeq();
                if (ifCmd.Guard != null)
                {
                    cmds.Add(new AssumeCmd(Token.NoToken, Expr.Not(ifCmd.Guard)));
                }

                TranslateTransfer(procState, ifCmd.tok, elsLabel, cmds, trf, inAtom);
            }

            // translate elseif
            //if (elseIf != null)
            //{
            //    TranslateIf(procState, elseIf, elsifLabel, nextlabel, runOffTheEndLabel);
            //}
        }


        private void TranslateCallStmt(ProcedureState procState, CallStmt stmt, BigBlock parentBB, string runOffTheEndLabel, bool inAtom)
        {
            //if (!inAtom)
            //{

                //rctx.blocks.Clear();
                //rctx.CreateBlocks(stmt.body, runOffTheEndLabel);
                //List<Block> blks = rctx.blocks;

                Debug.Assert(parentBB.simpleCmds.Length == 0);

                List<Block> blocks = new List<Block>(Blocks);
                Blocks.Clear();

                Block startBlock = TranslateBlock(procState, stmt.tok, stmt.label, new CmdSeq(), new GotoCmd(Token.NoToken, new StringSeq(stmt.body.BigBlocks[0].LabelName)));

                TranslateStmt(procState, stmt.body, runOffTheEndLabel, true);
                Debug.Assert(Blocks.Count == 2 && Blocks[0] == startBlock);

                CallBlock callBlock = new CallBlock(procState, new List<Block>(Blocks), startBlock, stmt);

                Blocks.InsertRange(0, blocks);

                APLStmtMap.Add(stmt.label, stmt);
                APLBlockMap.Add(callBlock.Label, callBlock);
                //Blocks.AddRange(blks);
            //}
            //else
            //{
            //    TransferCmd tc = GotoSuccessor(stmt.tok, parentBB, runOffTheEndLabel);
            //    TranslateTransfer(procState, stmt.tok, stmt.label, new CmdSeq(stmt.cmd), tc, inAtom);
            //}

            // register caller
            ProofState.GetInstance().GetProcedureState(stmt.cmd.Proc.Name).RegisterCaller(procState, stmt);
        }


        private void TranslateAtomicStmt(ProcedureState procState, AtomicStmt stmt, BigBlock parentBB, string runOffTheEndLabel, bool inAtom)
        {
            //rctx.blocks.Clear();
            //rctx.CreateBlocks(stmt.body, runOffTheEndLabel);
            Debug.Assert(parentBB.simpleCmds.Length == 0);

            List<Block> blocks = new List<Block>(Blocks);
            Blocks.Clear();

            Block startBlock = TranslateBlock(procState, stmt.tok, stmt.label, new CmdSeq(), new GotoCmd(Token.NoToken, new StringSeq(stmt.body.BigBlocks[0].LabelName)));

            TranslateStmt(procState, stmt.body, runOffTheEndLabel, true); // in atom

            if (!inAtom)
            {
                Debug.Assert(!(stmt is StraightAtomicStmt));
                AtomicBlock atomicBlock = new AtomicBlock(procState, new List<Block>(Blocks), startBlock, stmt);
                APLStmtMap.Add(stmt.label, stmt);
                APLBlockMap.Add(atomicBlock.Label, atomicBlock);
            }
            else if (stmt is StraightAtomicStmt)
            {
                // inAtom: inside an atomic block
                StraightAtomicBlock atomicBlock = new StraightAtomicBlock(procState, new List<Block>(Blocks), startBlock, stmt);
                APLStmtMap.Add(stmt.label, stmt);
                APLBlockMap.Add(atomicBlock.Label, atomicBlock);
            }
            else
            {
                Debug.Assert(false);
            }

            Blocks.InsertRange(0, blocks);

            //Blocks.AddRange(blks);
        }

        private Block TranslateBlock(ProcedureState procState, IToken tok, string label, CmdSeq cmds, TransferCmd tc)
        {
            Block block = new Block(tok, label, new CmdSeq(), tc);

            if (CheckPc)
            {
                block.Cmds.Add(new AssertCmd(Token.NoToken, PcExpr));
                PcExpr = Expr.Eq(procState.pcExpr, ProofState.GetInstance().exSkipExpr);
            }

            block.Cmds.AddRange(PrefixCmds);
            PrefixCmds = new CmdSeq();

            for (int i = 0; i < cmds.Length; ++i)
            {
                block.Cmds.AddRange(TranslateCmd(cmds[i]));
            }

            Expr ex;
            if (tc is ThrowCmd)
            {
                ex = (tc as ThrowCmd).ex;
            }
            else if (tc is ReturnCmd)
            {
                ex = ProofState.GetInstance().exReturnExpr;
            }
            else // GotoCmd
            {
                ex = ProofState.GetInstance().exSkipExpr;
            }

            // pc := ex
            block.Cmds.Add(AssignCmd.SimpleAssign(Token.NoToken, procState.pcExpr, ex));
            // if an exception is thrown, then ex refers to that exception
            if (!(tc is GotoCmd))
                block.Cmds.Add(AssignCmd.SimpleAssign(Token.NoToken, procState.exExpr, ex));


            Blocks.Add(block);

            return block;
        }

        public static CmdSeq TranslateCmd(Cmd cmd)
        {
            if (cmd is NewCmd)
            {
                return Desugar.Cmd(cmd as NewCmd);
            }
            else if (cmd is FreeCmd)
            {
                return Desugar.Cmd(cmd as FreeCmd);
            } 
            else if (cmd is QHavocCmd)
            {
                return Desugar.Cmd(cmd as QHavocCmd);
            }
            else if (cmd is GatedAction)
            {
                return Desugar.Cmd(cmd as GatedAction);
            }
            else if (cmd is AssertCmd)
            {
                return Desugar.Cmd(cmd as AssertCmd);
            }

            // other commands
            return new CmdSeq(cmd);
        }
    }



    // code analyses on Qoogie programs
    public class Qoogie
    {
        static public IDictionary<string, ICollection<BigBlock>> ComputePredecessorMap(ICollection<BigBlock> bbs)
        {
            IDictionary<string, ICollection<BigBlock>> map = new Dictionary<string, ICollection<BigBlock>>();

            foreach (BigBlock bb in bbs)
            {
                GotoCmd gotoCmd = bb.tc as GotoCmd;
                if (gotoCmd != null)
                {
                    foreach (string target in gotoCmd.labelNames)
                    {
                        if (!map.ContainsKey(target))
                        {
                            map.Add(target, new Set<BigBlock>());
                        }
                        map[target].Add(bb);
                    }
                }
            }
            return map;
        }

        static public IDictionary<string, ICollection<BigBlock>> ComputePredecessorMap(StmtList stmt)
        {
            return ComputePredecessorMap(new BigBlocksCollector().Collect(stmt));
        }

        static public StmtList SkipStmt
        {
            get
            {
                AtomicStmt atom = MakeAtomicStmt(new CmdSeq(new AssumeCmd(Token.NoToken, Expr.True)), null, null);
                BigBlock bb = new BigBlock(Token.NoToken, atom.label, new CmdSeq(), atom, null);
                List<BigBlock> bbs = new List<BigBlock>();
                bbs.Add(bb);
                return new StmtList(bbs, Token.NoToken);
            }
        }

        static public StmtList SuppressStmt
        {
            get
            {
                AtomicStmt atom = MakeAtomicStmt(new CmdSeq(new AssumeCmd(Token.NoToken, Expr.False)), null, null);
                BigBlock bb = new BigBlock(Token.NoToken, atom.label, new CmdSeq(), atom, null);
                List<BigBlock> bbs = new List<BigBlock>();
                bbs.Add(bb);
                return new StmtList(bbs, Token.NoToken);
            }
        }

        static public StmtList SkipEx(StmtList stmt, TransferCmd tc, params IdentifierExpr[] labels)
        {
            if (MergeCommand.IsAtomic(stmt))
            {
                AtomicStmt atom = stmt.BigBlocks[0].ec as AtomicStmt;
                atom.body = MakeTryCatchStmt(atom.body, Qoogie.SkipStmt, tc, labels);
                return stmt;
            }
            // else
            return MakeTryCatchStmt(stmt, Qoogie.SkipStmt, tc, labels);
        }

        static public StmtList SuppressEx(StmtList stmt, TransferCmd tc, params IdentifierExpr[] labels)
        {
            if (MergeCommand.IsAtomic(stmt))
            {
                AtomicStmt atom = stmt.BigBlocks[0].ec as AtomicStmt;
                atom.body = MakeTryCatchStmt(atom.body, Qoogie.SuppressStmt, tc, labels);
                return stmt;
            }
            // else
            return MakeTryCatchStmt(stmt, Qoogie.SuppressStmt, tc, labels);
        }

        static public StmtList SuppressEx2(StmtList stmt, TransferCmd tc, params IdentifierExpr[] labels)
        {
            Debug.Assert(tc == null);

            Set<BigBlock> bbs = new BigBlocksCollector().Collect(stmt);
            foreach (BigBlock bb in bbs)
            {
                if (bb.tc is ThrowCmd)
                {
                    ThrowCmd throwCmd = bb.tc as ThrowCmd;
                    bool ok = labels.Length == 0;
                    foreach (IdentifierExpr ie in labels)
                    {
                        if (ie.Equals(throwCmd.ex))
                        {
                            ok = true;
                            break;
                        }
                    }
                    if (ok)
                    {
                        bb.simpleCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
                        bb.tc = null;
                    }
                }
            }
            return stmt;
        }

        static public StmtList Suppress(StmtList stmt)
        {
            if (MergeCommand.IsAtomic(stmt))
            {
                AtomicStmt atom = stmt.BigBlocks[0].ec as AtomicStmt;
                atom.body.BigBlocks.AddRange(Qoogie.SuppressStmt.BigBlocks);
                return stmt;
            }
            // else
            stmt.BigBlocks.AddRange(Qoogie.SuppressStmt.BigBlocks);
            return stmt;
        }

        // if null there was an error
        static public BigBlocksResolutionContext ResolveStmt(StmtList stmtList)
        {
            // remove PrefixCommands of all stmt lists
            List<StmtList> stmtLists = new StmtListCollector().Collect(stmtList);
            foreach (StmtList stmt in stmtLists)
            {
                stmt.PrefixCommands = null;
                stmt.ParentContext = null;
                stmt.ParentBigBlock = null;
            }

            // remove BreakEnclosures of all breaks
            Set<BigBlock> bbs = new BigBlocksCollector().Collect(stmtList);
            foreach (BigBlock bb in bbs)
            {
                if (bb.ec != null && bb.ec is BreakCmd)
                {
                    (bb.ec as BreakCmd).BreakEnclosure = null;
                }
                else if (bb.ec != null && bb.ec is ContinueCmd)
                {
                    (bb.ec as ContinueCmd).ContinueEnclosure = null;
                }
            }

            BigBlocksResolutionContext ctx = new BigBlocksResolutionContext(stmtList);

            ctx.blocks = new List<Block>();

            int startErrorCount = BoogiePL.Errors.count;
            // Check that there are no goto's into the middle of a block, and no break statement to a non-enclosing loop.
            // Also, determine a good value for "prefix".
            ctx.CheckLegalLabels(stmtList, null, null);

            // fill in names of anonymous blocks
            ctx.NameAnonymousBlocks(stmtList);

            // determine successor blocks
            ctx.RecordSuccessors(stmtList, null);

            //----------------------------------------------------
            // resolve throw statements
            ResolveThrows(stmtList);

            ////----------------------------------------------------
            //// resolve the statements
            //ResolutionContext rc = procState.GetResolutionContext(false);
            //foreach (BigBlock bb in bbs)
            //{
            //    foreach (Cmd cmd in bb.simpleCmds)
            //    {
            //        cmd.Resolve(rc);
            //    }
            //}
            ////----------------------------------------------------
            //// typecheck the statements

            //TypecheckingContext tc = procState.GetTypecheckingContext();
            //foreach (BigBlock bb in bbs)
            //{
            //    foreach (Cmd cmd in bb.simpleCmds)
            //    {
            //        cmd.Typecheck(tc);
            //    }
            //}

            //----------------------------------------------------
            return (BoogiePL.Errors.count == startErrorCount) ? ctx : null;
        }

        private static void ResolveThrows(StmtList stmtList)
        {
            ResolveThrows(stmtList, new List<CatchStmt>());
        }

        private static void ResolveThrows(StmtList stmtList, List<CatchStmt> catchList)
        {
            for (int i = 0; i < stmtList.BigBlocks.Count; ++i)
            {
                BigBlock bb = stmtList.BigBlocks[i];
                if (bb.tc != null)
                {
                    if (bb.tc is ThrowCmd)
                    {
                        ThrowCmd throwCmd = bb.tc as ThrowCmd;

                        bool found = false;
                        foreach (CatchStmt catchStmt in catchList)
                        {
                            if (catchStmt.labels.Count == 0)
                            {
                                throwCmd.catchStmt = catchStmt;
                                found = true;
                                break;
                            }
                            else
                            {
                                foreach (IdentifierExpr ex in catchStmt.labels)
                                {
                                    if (ProofState.GetInstance().IsSubType(throwCmd.ex.Name, ex.Name))
                                    {
                                        throwCmd.catchStmt = catchStmt;
                                        found = true;
                                        break;
                                    }
                                }
                            }
                        }
                        Debug.Assert(found || throwCmd.catchStmt == null);
                    }
                }
                else if (bb.ec != null)
                {
                    if (bb.ec is WhileCmd)
                    {
                        WhileCmd whileCmd = bb.ec as WhileCmd;
                        ResolveThrows(whileCmd.Body, catchList);
                    }
                    else if (bb.ec is IfCmd)
                    {
                        IfCmd ifCmd = bb.ec as IfCmd;
                        while (ifCmd != null)
                        {
                            ResolveThrows(ifCmd.thn, catchList);
                            if (ifCmd.elseBlock != null)
                            {
                                ResolveThrows(ifCmd.elseBlock, catchList);
                                Debug.Assert(ifCmd.elseIf == null);
                            }
                            ifCmd = ifCmd.elseIf;
                        }
                    }
                    else if (bb.ec is TryCatchStmt)
                    {
                        TryCatchStmt trycatch = bb.ec as TryCatchStmt;
                        List<CatchStmt> cloneList = new List<CatchStmt>(catchList);

                        for (int j = 0; j < trycatch.catchList.Count; ++j)
                        {
                            CatchStmt catchStmt = trycatch.catchList[j];

                            ResolveThrows(catchStmt.body, catchList);

                            cloneList.Add(catchStmt);
                        }

                        ResolveThrows(trycatch.body, cloneList);

                    }
                    else if (bb.ec is APLStmt)
                    {
                        APLStmt aplStmt = bb.ec as APLStmt;
                        foreach (StmtList body in aplStmt.bodies)
                        {
                            ResolveThrows(body, catchList);
                        }
                    }
                }
            }
        }

        internal static Pair CollectNonGlobalVariables(StmtList stmtList)
        {
            return (new NonGlobalVarsCollector()).Collect(stmtList);
        }

        static public Type ParseType(string text)
        {
            Type type;
            Parser.ParseType(text, out type);

            return type;
        }

        static public StmtList ParseCode(string text, out VariableSeq localVars)
        {
            return ParseCode(text, out localVars, null);
        }

        static public StmtList ParseCode(string text, out VariableSeq localVars, IDictionary<string, BigBlock> enclosure/* = null*/)
        {
            // if there is break of continue in codeText, give its while enclosure 
            QEDPLGlobals.whileEnclosure = enclosure;
            //------------------------------------------------------------------------

            StringBuilder sb = new StringBuilder();

            sb.Append("implementation dummyName () {");
            sb.Append(text);
            sb.Append(" }");

            Program prog = ParseProgram("ParseCode", sb.ToString());

            // clean the while enclosures
            QEDPLGlobals.whileEnclosure = null;

            if (prog != null)
            {
                Debug.Assert(prog.TopLevelDeclarations.Count == 1);

                Implementation impl = prog.TopLevelDeclarations[0] as Implementation;

                Debug.Assert(impl != null);

                // clear labels of anonymous blocks
                CodeTransformations.RenameLabels(impl.StructuredStmts, null);

                localVars = impl.LocVars;

                return impl.StructuredStmts;
            }
            
            // failure
            localVars = null;
            return null;
        }

        static public Expr ParseExpr(string text)
        {
            Expr expr;

            BoogiePL.Parser.ParseProposition(text, out expr);

            return BoogiePL.Errors.count == 0 ? expr : null;
        }

        internal static VariableSeq CollectAssignedVarsInLoop(StmtList body)
        {
            return (new AssignedVarsInLoopCollector()).Collect(body);
        }

        static public Program ParseFile(string filename)
        {
            Program program;

            try
            {
                int errorCount = BoogiePL.Parser.Parse(filename, out program);
                if (program == null || errorCount != 0)
                {
                    Output.LogLine(BoogiePL.Errors.count + " parse errors detected in " + filename);
                    return null;
                }
            }
            catch (IOException e)
            {
                Output.LogLine("Error opening file " + filename);
                Output.Add(e);
                return null;
            }

            return program;
        }

        static public Program ParseProgram(string programName, string programText)
        {
            BoogiePL.Errors.count = 0;
            Program program = null;
            BoogiePL.Buffer.Fill(programText);
            BoogiePL.Scanner.Init(string.Format("\"{0}\"", programName));
            BoogiePL.Parser.Parse(out program);
            return program;
        }

        internal static Constant GetConstant(Program program, string cname)
        {
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Constant cons = decl as Constant;
                if (cons != null && cons.Name == cname)
                {
                    return cons;
                }
            }
            return null;
        }

        internal static Function GetFunction(Program program, string fname)
        {
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Function f = decl as Function;
                if (f != null && f.Name == fname)
                {
                    return f;
                }
            }
            return null;
        }


        internal static Type GetType(Program program, string tname)
        {
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                TypeCtorDecl tdecl = decl as TypeCtorDecl;
                if (tdecl != null && tdecl.Name == tname)
                {
                    return new CtorType(tdecl.tok, tdecl, new TypeSeq());
                }
            }
            return null;
        }

        internal static GlobalVariable GetGlobalVar(Program program, string vname)
        {
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                GlobalVariable gvar = decl as GlobalVariable;
                if (gvar != null && gvar.Name == vname)
                {
                    return gvar;
                }
            }
            return null;
        }

        internal static Procedure GetProcedure(Program program, string pname)
        {
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Procedure proc = decl as Procedure;
                if (proc != null && proc.Name == pname)
                {
                    return proc;
                }
            }
            return null;
        }


        internal static StmtList GetParentContext(BigBlock bb, StmtList main, out int index)
        {
            //if (bb.ec != null)
            //{
            //    return GetParentContext(bb.ec);
            //}

            List<StmtList> stmtLists = new StmtListCollector().Collect(main);
            foreach (StmtList stmtList in stmtLists)
            {
                for (int i = 0; i < stmtList.BigBlocks.Count; i++)
                {
                    if (stmtList.BigBlocks[i] == bb)
                    {
                        index = i;
                        return stmtList;
                    }
                }
            }
            Debug.Assert(false);
            index = -1;
            return null;
        }

        internal static StmtList GetParentContext(AtomicStmt atom, StmtList main, out int index)
        {
            //if (bb.ec != null)
            //{
            //    return GetParentContext(bb.ec);
            //}

            List<StmtList> stmtLists = new StmtListCollector().Collect(main);
            foreach (StmtList stmtList in stmtLists)
            {
                for (int i = 0; i < stmtList.BigBlocks.Count; i++)
                {
                    if (stmtList.BigBlocks[i].ec == atom)
                    {
                        index = i;
                        return stmtList;
                    }
                }
            }
            Debug.Assert(false);
            index = -1;
            return null;
        }

        internal static StmtList GetParentContext(StructuredCmd stmt)
        {
            if (stmt is IfCmd)
            {
                return (stmt as IfCmd).thn.ParentContext;
            }
            if (stmt is WhileCmd)
            {
                return (stmt as WhileCmd).Body.ParentContext;
            }
            if (stmt is APLStmt)
            {
                return (stmt as APLStmt).body.ParentContext;
            }
            Debug.Assert(false);
            return null;
        }

        internal static BigBlock GetParentBigBlock(StructuredCmd stmt)
        {
            if (stmt is IfCmd)
            {
                return (stmt as IfCmd).thn.ParentBigBlock;
            }
            if (stmt is WhileCmd)
            {
                return (stmt as WhileCmd).Body.ParentBigBlock;
            }
            if (stmt is APLStmt)
            {
                return (stmt as APLStmt).body.ParentBigBlock;
            }
            Debug.Assert(false);
            return null;
        }

        // this must return false for outmost atomic stmts
        internal static bool IsInAtomic(APLStmt stmt)
        {
            for (StmtList sl = GetParentContext(stmt); sl.ParentBigBlock != null; sl = sl.ParentContext)
            {
                Debug.Assert(sl != null);

                BigBlock bb = sl.ParentBigBlock;

                if (bb.ec != null && bb.ec is AtomicStmt)
                {
                    return true;
                }
            }
            return false;
        }


        internal static AtomicStmt GetParentAtomicStmt(StmtList stmt)
        {
            AtomicStmt parent = null;
            for (StmtList sl = stmt; sl.ParentBigBlock != null; sl = sl.ParentContext)
            {
                Debug.Assert(sl != null);

                BigBlock bb = sl.ParentBigBlock;

                if (bb.ec != null && bb.ec is AtomicStmt)
                {
                    parent = bb.ec as AtomicStmt;
                }
            }
            Debug.Assert(parent == null || (parent is AtomicStmt && !(parent is StraightAtomicStmt)));
            return parent;
        }

        internal static void SetParentContext(StructuredCmd stmt, BigBlock parentBB, StmtList parentStmt)
        {
            if (stmt is IfCmd)
            {
                IfCmd ifCmd = stmt as IfCmd;
                ifCmd.thn.ParentBigBlock = parentBB;
                ifCmd.thn.ParentContext = parentStmt;
                if (ifCmd.elseBlock != null)
                {
                    ifCmd.elseBlock.ParentBigBlock = parentBB;
                    ifCmd.elseBlock.ParentContext = parentStmt;
                }
            }
            else
                if (stmt is WhileCmd)
                {
                    WhileCmd whileCmd = stmt as WhileCmd;
                    whileCmd.Body.ParentBigBlock = parentBB;
                    whileCmd.Body.ParentContext = parentStmt;
                }
                else
                    if (stmt is APLStmt)
                    {
                        APLStmt aplStmt = stmt as APLStmt;
                        foreach (StmtList body in aplStmt.bodies)
                        {
                            body.ParentBigBlock = parentBB;
                            body.ParentContext = parentStmt;
                        }
                    }
                    else
                    {
                        Debug.Assert(false);
                    }
        }

        public static StraightAtomicStmt MakeStraightAtomicStmt(List<BigBlock> bbs)
        {
            string atomLbl = AtomicStmt.GenerateLabel();
            StmtList stmtList = new StmtList(bbs, Token.NoToken);
            return new StraightAtomicStmt(Token.NoToken, atomLbl, stmtList, null);
        }

        public static AtomicStmt MakeAtomicStmt(CmdSeq cmdSeq, StructuredCmd ec, TransferCmd tc)
        {
            string atomLbl = AtomicStmt.GenerateLabel();
            List<BigBlock> bbs = new List<BigBlock>();
            bbs.Add(new BigBlock(Token.NoToken, null, new CmdSeq(cmdSeq), ec, tc));
            StmtList stmtList = new StmtList(bbs, Token.NoToken);
            return new AtomicStmt(Token.NoToken, atomLbl, stmtList, null);
        }

        public static CallStmt MakeCallStmt(CallCmd cmd, StructuredCmd ec, TransferCmd tc)
        {
            string atomLbl = CallStmt.GenerateLabel();
            List<BigBlock> bbs = new List<BigBlock>();
            bbs.Add(new BigBlock(Token.NoToken, null, new CmdSeq(cmd), ec, tc));
            StmtList stmtList = new StmtList(bbs, Token.NoToken);
            return new CallStmt(Token.NoToken, atomLbl, stmtList, cmd);
        }

        public static ForkStmt MakeForkStmt(AsyncCallCmd cmd, StructuredCmd ec, TransferCmd tc)
        {
            string atomLbl = ForkStmt.GenerateLabel();
            List<BigBlock> bbs = new List<BigBlock>();
            bbs.Add(new BigBlock(Token.NoToken, null, new CmdSeq(cmd), ec, tc));
            StmtList stmtList = new StmtList(bbs, Token.NoToken);
            return new ForkStmt(Token.NoToken, atomLbl, cmd);
        }

        public static JoinStmt MakeJoinStmt(JoinCmd cmd, StructuredCmd ec, TransferCmd tc)
        {
            string atomLbl = JoinStmt.GenerateLabel();
            List<BigBlock> bbs = new List<BigBlock>();
            bbs.Add(new BigBlock(Token.NoToken, null, new CmdSeq(cmd), ec, tc));
            StmtList stmtList = new StmtList(bbs, Token.NoToken);
            return new JoinStmt(Token.NoToken, atomLbl, cmd);
        }

        static public StmtList MakeTryCatchStmt(StmtList bodyStmt, StmtList catchbodyStmt, TransferCmd tc, params IdentifierExpr[] labels)
        {
            CatchStmt catchStmt = new CatchStmt(Token.NoToken, new List<IdentifierExpr>(labels), catchbodyStmt);
            List<CatchStmt> catchList = new List<CatchStmt>();
            catchList.Add(catchStmt);
            TryCatchStmt trycatch = new TryCatchStmt(Token.NoToken, TryCatchStmt.GenerateLabel(), bodyStmt, catchList);
            BigBlock bb = new BigBlock(Token.NoToken, trycatch.label, new CmdSeq(), trycatch, tc);
            List<BigBlock> bbs = new List<BigBlock>();
            bbs.Add(bb);
            StmtList newstmt = new StmtList(bbs, Token.NoToken);
            return newstmt;
        }

        public static Expr DuplicateExpr(Expr expr)
        {
            return new StmtDuplicator().VisitExpr(expr);
        }

        public static Cmd DuplicateCmd(Cmd cmd)
        {
            return new StmtDuplicator().Visit(cmd) as Cmd;
        }

        public static BigBlock DuplicateBigBlock(BigBlock bb)
        {
            List<BigBlock> bbs = new List<BigBlock>();
            bbs.Add(bb);

            List<BigBlock> newbbs = new StmtDuplicator().VisitBigBlocks(bbs);

            FinishDuplicateStatement(newbbs, Qoogie.ComputePredecessorMap(newbbs));

            return newbbs[0];
        }

        public static StmtList DuplicateStatement(StmtList stmtList)
        {
            StmtList newStmtList = new StmtDuplicator().VisitStmtList(stmtList);

            FinishDuplicateStatement(new BigBlocksCollector().Collect(newStmtList), Qoogie.ComputePredecessorMap(newStmtList));

            return newStmtList;
        }

        public static void FinishDuplicateStatement(ICollection<BigBlock> newbbs, IDictionary<string, ICollection<BigBlock>> BBPredecessorMap)
        {
            foreach (BigBlock newbb in newbbs)
            {
                if (newbb.Anonymous)
                {
                    newbb.LabelName = null;
                }
                else
                {
                    string label = newbb.LabelName;
                    newbb.LabelName = label + "_dup";
                    if (newbb.ec is APLStmt)
                    {
                        (newbb.ec as APLStmt).label = newbb.LabelName;
                    }

                    if (BBPredecessorMap.ContainsKey(label))
                    {
                        ICollection<BigBlock> preds = BBPredecessorMap[label];
                        foreach (BigBlock pred in preds)
                        {
                            GotoCmd gotoCmd = pred.tc as GotoCmd;
                            if (gotoCmd != null)
                            {
                                if (gotoCmd.labelNames.Has(label))
                                {
                                    StringSeq seq = new StringSeq();
                                    foreach (string s in gotoCmd.labelNames)
                                    {
                                        if (s != label)
                                        {
                                            seq.Add(s);
                                        }
                                        else
                                        {
                                            seq.Add(newbb.LabelName);
                                        }
                                    }
                                    gotoCmd.labelNames = seq;
                                    gotoCmd.labelTargets = null;
                                }
                            }
                        }
                    }
                }
            }
        }

        internal static void RemoveQKeyValue(Declaration decl, string key)
        {
            QKeyValue prev = null;
            for (QKeyValue qkv = decl.Attributes; qkv != null; qkv = qkv.Next)
            {
                if (qkv.Key == key)
                {
                    if (prev != null)
                        prev.Next = qkv.Next;
                    if (qkv == decl.Attributes)
                        decl.Attributes = qkv.Next;
                    break;
                }
                prev = qkv;
            }
        }

        internal static void AddQKeyValue(Declaration decl, string key)
        {
            if (!QKeyValue.FindBoolAttribute(decl.Attributes, key))
            {
                QKeyValue qkv = new QKeyValue(Token.NoToken, key, new List<object>(), null);
                if (decl.Attributes == null)
                    decl.Attributes = qkv;
                else
                    decl.Attributes.AddLast(qkv);
            }
        }

        internal static int GetIndex(BigBlock parentBB, StmtList parentStmt)
        {
            int index = -1;
            for (int i = 0; i < parentStmt.BigBlocks.Count; i++)
            {
                if (parentStmt.BigBlocks[i] == parentBB)
                {
                    index = i;
                    break;
                }
            }
            Debug.Assert(index >= 0);
            return index;
        }

        internal static CmdSeq DuplicateCmdSeq(CmdSeq cmdSeq)
        {
            StmtDuplicator duplicator = new StmtDuplicator();
            CmdSeq cmds = new CmdSeq();
            for (int i = 0; i < cmdSeq.Length; ++i)
            {
                cmds.Add(duplicator.Visit(cmdSeq[i]) as Cmd);
            }
            return cmds;
        }

        internal static bool CheckQKeyValue(Variable var, string key)
        {
            return QKeyValue.FindBoolAttribute(var.Attributes, key);
        }

        internal static IDictionary<string, BigBlock> ComputeWhileEnclosure(StmtList stmtList)
        {
            IDictionary<string, BigBlock> whileEnclosure = new Dictionary<string, BigBlock>();
            for (StmtList sl = stmtList; sl.ParentBigBlock != null; sl = sl.ParentContext)
            {
                BigBlock bb = sl.ParentBigBlock;
                if (!(bb.ec is WhileCmd)) continue;

                if (bb.simpleCmds.Length == 0)
                {
                    // this is a good target:  the label refers to the if/while statement
                    if (bb.LabelName != null)
                    {
                        whileEnclosure.Add(bb.LabelName, bb);
                    }

                    if (!whileEnclosure.ContainsKey(""))
                    {
                        whileEnclosure.Add("", bb);
                    }

                }
                else
                {
                    // the label of bb refers to the first statement of bb, which in which case is a simple statement, not an if/while statement
                    Output.AddError("break label '" + bb.LabelName + "' must designate an enclosing statement");
                }
            }
            return whileEnclosure;
        }

        // take a variable name, global name, record.field, or local name and return the actual variable
        static public Variable GetVariableByName(ProofState proofState, string varname, ProcedureState procState)
        {
            Variable var = null;

            int i = varname.IndexOf('.');
            if (i >= 0)
            {
                string recordname = varname.Substring(0, i);
                string fieldname = varname.Substring(i + 1);
                Record record = proofState.program.Records[recordname];
                if (record == null)
                {
                    Output.AddError("Record not found: " + recordname);
                    return null;
                }
                var = record.GetFieldMap(varname);
            }
            else
                if (procState == null)
                {
                    var = proofState.GetGlobalVar(varname);
                    if (var == null)
                    {
                        Output.AddError("Variable not found: " + varname);
                        return null;
                    }
                }
                else
                {
                    var = procState.GetLocalVar(varname);
                    if (var == null)
                    {
                        Output.AddError("Variable not found: " + varname);
                        return null;
                    }
                }

            Debug.Assert(var != null);
            return var;
        }


        // make a new atomic stmt from the given two
        internal static AtomicStmt ComposeAtomics(AtomicStmt atomA, AtomicStmt atomB)
        {
            string label = AtomicStmt.GenerateLabel();
            BigBlock bbA = new BigBlock(Token.NoToken, null, new CmdSeq(), atomA, null);
            BigBlock bbB = new BigBlock(Token.NoToken, null, new CmdSeq(), atomB, null);
            List<BigBlock> bbs = new List<BigBlock>();
            bbs.Add(bbA); 
            bbs.Add(bbB);
            StmtList stmt = new StmtList(bbs, Token.NoToken);
            AtomicStmt atom = new AtomicStmt(Token.NoToken, label, stmt, null);
            return atom;
        }
    }
}
