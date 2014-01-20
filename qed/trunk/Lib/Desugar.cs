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
    using Microsoft.Boogie.AbstractInterpretation;
    using AI = Microsoft.AbstractInterpretationFramework;
    using Microsoft.Contracts;
    using Type = Microsoft.Boogie.Type;
    using PureCollections;

    public class DesugarVisitor : StmtDuplicator
    {
        public DesugarVisitor()
            : base()
        {
            this.TargetLang = Lang.Boogie2;
        }

        IDictionary<string, Record> recordMap = new Dictionary<string, Record>();
        List<Invariant> invariants = new List<Invariant>();

        public void TranslateAndPrint(Program prog, string filename)
        {
            Program program = Translate(prog);
            if (program != null)
            {
                Util.WriteToFile(program, filename);
                Output.AddLine("Current program was saved to " + filename);
            }
            else
            {
                Output.AddError("Current program could not be saved!");
            }
        }

        public Program Translate(Program prog)
        {
            Program program = new StmtDuplicator().VisitProgram(prog);

            if (!Verifier.ResolveTypeCheck(program))
            {
                Output.AddError("Copy of input program could not be resolved/typechecked!");
                return null;
            }

            // collect records and invariants
            List<Declaration> topList = new List<Declaration>();
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Record rec = decl as Record;
                if (rec != null)
                {
                    recordMap.Add(rec.Name, rec);

                    topList.Add(rec.typeDecl);
                    // add records maps to the top level declarations
                    foreach (Field field in rec.fields)
                    {
                        topList.Add(field.mapVar);
                       // prog.TopLevelDeclarations.Add(rec.GetFieldMap(field.Name));
                    }
                    continue;
                }

                //--------------
                Invariant inv = decl as Invariant;
                if (inv != null)
                {
                    invariants.Add(inv);
                    continue;
                }

                // otherwise add the declaration
                topList.Add(decl);

            }
            program.TopLevelDeclarations.Clear();
            program.TopLevelDeclarations.AddRange(topList);
            topList.Clear();

            // now visit the rest of the declarations
            // visit implementations explicitly and translate the commands
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl != null)
                {
                    Set<BigBlock> bbs = new BigBlocksCollector().Collect(impl.StructuredStmts);
                    foreach (BigBlock bb in bbs)
                    {
                        CmdSeq cmds = new CmdSeq();
                        foreach (Cmd cmd in bb.simpleCmds)
                        {
                            cmds.AddRange(Desugar.Cmd(cmd));
                        }
                        bb.simpleCmds = cmds;
                    }
                }
            }
            
            // sanity assignment
            this.TargetLang = Lang.Boogie2;

            // now visit everything else in the program
            program = this.VisitProgram(program);

            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl != null)
                {
                    impl.StructuredStmts = VisitStmtList(impl.StructuredStmts);
                }
            }

            // visit implementations again to recompute the blocks
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl != null)
                {
                    BigBlocksResolutionContext ctx = Qoogie.ResolveStmt(impl.StructuredStmts);
                    Debug.Assert(ctx != null);
                    ctx.CreateBlocks(impl.StructuredStmts, null);
                    impl.Blocks = ctx.blocks;
                }
            }
            
            if (!Verifier.ResolveTypeCheck(program))
            {
                Output.AddError("Translated program could be resolved/typechecked!");
                return null;
            }

            return program;
        }

        public override StmtList VisitStmtList(StmtList list)
        {
            List<BigBlock> newBBs = new List<BigBlock>();
            for (int i = 0; i < list.BigBlocks.Count; ++i)
            {
                BigBlock bb = list.BigBlocks[i];
                if (bb.ec != null && bb.ec is APLStmt)
                {
                    APLStmt aplStmt = bb.ec as APLStmt;
                    if (!bb.Anonymous || bb.simpleCmds.Length > 0 || bb.tc != null)
                    {
                        bb.ec = null;
                        newBBs.Add(bb);
                    }

                    foreach (StmtList body in aplStmt.bodies)
                    {
                        newBBs.AddRange(body.BigBlocks);
                    }
                }
                else
                {
                    newBBs.Add(bb);
                }
            }

            StmtList stmtList = new StmtList(VisitBigBlocks(newBBs), list.EndCurly);
            //stmtList.ParentBigBlock = list.ParentBigBlock;
            //stmtList.ParentContext = list.ParentContext;
            return stmtList;
        }

    } // end class

    public class Desugar
    {
        public static CmdSeq Cmd(Cmd cmd)
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
            else if (cmd is AssignCmd)
            {
                return Desugar.Cmd(cmd as AssignCmd);
            }

            // other commands
            return new CmdSeq(cmd);
        }

        public static CmdSeq Cmd(AssignCmd cmd)
        {
            CmdSeq cmds = new CmdSeq();

            for (int i = 0; i < cmd.Lhss.Count; ++i)
            {
                AssignLhs lhs = cmd.Lhss[i];
                if (lhs is FieldAssignLhs)
                {
                    FieldAssignLhs flhs = lhs as FieldAssignLhs;
                    cmds.Add(flhs.AsMapAssignment(cmd.Rhss[i]));
                }
                else
                {
                    List<AssignLhs> lhss = new List<AssignLhs>();
                    lhss.Add(lhs);
                    List<Expr> rhss = new List<Expr>();
                    rhss.Add(cmd.Rhss[i]);
                    cmds.Add(new AssignCmd(cmd.tok, lhss, rhss));
                }
            }

            return cmds;
        }

        public static CmdSeq Cmd(NewCmd newCmd)
        {
            CmdSeq cmds = new CmdSeq();

            Record record = newCmd.record;
            Expr obj = newCmd.assignLhs.AsExpr;
            Debug.Assert(record != null);

            cmds.Add(new HavocCmd(Token.NoToken, new IdentifierExprSeq(newCmd.assignLhs.DeepAssignedIdentifier)));

            IdentifierExpr fieldMapExpr = record.GetFieldMapExpr("alloc");
            Debug.Assert(fieldMapExpr != null && fieldMapExpr.Decl != null);
            cmds.Add(new AssumeCmd(Token.NoToken, Expr.Eq(Expr.Select(fieldMapExpr, obj), ProofState.GetInstance().deallocExpr)));
            cmds.Add(AssignCmd.MapAssign(Token.NoToken, fieldMapExpr, obj, ProofState.GetInstance().allocExpr));

            fieldMapExpr = record.GetFieldMapExpr("owner");
            Debug.Assert(fieldMapExpr != null && fieldMapExpr.Decl != null);
            cmds.Add(new AssumeCmd(Token.NoToken, Expr.Eq(Expr.Select(fieldMapExpr, obj), LiteralExpr.Literal(0))));
            cmds.Add(AssignCmd.MapAssign(Token.NoToken, fieldMapExpr, obj, ProofState.GetInstance().tidExpr));

            return cmds;
        }

        public static CmdSeq Cmd(FreeCmd freeCmd)
        {
            CmdSeq cmds = new CmdSeq();

            Record record = freeCmd.record;
            Expr obj = freeCmd.obj;
            Debug.Assert(record != null);

            IdentifierExpr fieldMapExpr = record.GetFieldMapExpr("alloc");
            Debug.Assert(fieldMapExpr != null && fieldMapExpr.Decl != null);
            cmds.Add(new AssertCmd(Token.NoToken, Expr.Eq(Expr.Select(fieldMapExpr, obj), ProofState.GetInstance().allocExpr)));
            cmds.Add(AssignCmd.MapAssign(Token.NoToken, fieldMapExpr, obj, ProofState.GetInstance().deallocExpr));

            fieldMapExpr = record.GetFieldMapExpr("owner");
            Debug.Assert(fieldMapExpr != null && fieldMapExpr.Decl != null);
            cmds.Add(new AssertCmd(Token.NoToken, Expr.Eq(Expr.Select(fieldMapExpr, obj), ProofState.GetInstance().tidExpr)));
            cmds.Add(AssignCmd.MapAssign(Token.NoToken, fieldMapExpr, obj, LiteralExpr.Literal(0)));

            return cmds;
        }

        public static CmdSeq Cmd(QHavocCmd qhavocCmd)
        {
            CmdSeq cmds = new CmdSeq();

            Debug.Assert(qhavocCmd.Lhss.Count > 0);

            // create the assumption
            foreach (AssignLhs assignLhs in qhavocCmd.Lhss)
            {
                if (assignLhs is SimpleAssignLhs)
                {
                    SimpleAssignLhs simpleAssignLhs = assignLhs as SimpleAssignLhs;

                    cmds.Add(new HavocCmd(qhavocCmd.tok, new IdentifierExprSeq(simpleAssignLhs.DeepAssignedIdentifier)));
                }
                else
                {
                    List<Expr> indexes = null;
                    Variable map = null;

                    if (assignLhs is FieldAssignLhs)
                    {
                        FieldAssignLhs fieldAssignLhs = assignLhs as FieldAssignLhs;
                        Record record = fieldAssignLhs.record;
                        Debug.Assert(record != null);
                        map = record.GetFieldMap(fieldAssignLhs.fieldName);

                        indexes = new List<Expr>();
                        indexes.Add(fieldAssignLhs.obj);
                    }
                    else if (assignLhs is MapAssignLhs)
                    {
                        MapAssignLhs mapAssignLhs = assignLhs as MapAssignLhs;
                        Debug.Assert(mapAssignLhs.Map is SimpleAssignLhs);
                        map = mapAssignLhs.Map.DeepAssignedVariable;

                        indexes = mapAssignLhs.Indexes;
                    }

                    IdentifierExpr mapExpr = new IdentifierExpr(Token.NoToken, map);

                    Expr fcond = Logic.FrameCondition(mapExpr, indexes);

                    cmds.Add(new GatedAction(qhavocCmd.tok, Expr.True, fcond, new IdentifierExprSeq(mapExpr), false));
                }
            }

            return cmds;
        }

        public static CmdSeq Cmd(AssertCmd assertCmd)
        {
            CmdSeq cmds = new CmdSeq();

            cmds.Add(assertCmd);
            cmds.Add(new StmtDuplicator().Visit(new AssumeCmd(assertCmd.tok, assertCmd.Expr)));

            return cmds;
        }

        public static CmdSeq Cmd(GatedAction gact)
        {
            CmdSeq cmds = new CmdSeq();

            if (gact.checkAssert && gact.gate != Expr.True)
            {
                cmds.Add(new AssertCmd(gact.tok, gact.gate));
                cmds.Add(new StmtDuplicator().Visit(new AssumeCmd(gact.tok, gact.gate)));
            }
            cmds.Add(gact);

            return cmds;
        }

        internal static Expr NAryExpr(NAryExpr node)
        {
            if (node.Fun is FieldSelect)
            {
                return (node.Fun as FieldSelect).Desugar(node);
            }
            else if (node.Fun is FieldStore)
            {
                return (node.Fun as FieldStore).Desugar(node);
            }
            return node;
        }
    }
   

} // end namespace QED