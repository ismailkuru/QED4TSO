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


    // code analyses on Boogie programs
    public class CodeAnalyses
    {
        // start from an entry and compute the atomic statements that may run in parallel
        static public IDictionary<Pair, Set<Pair>> ComputeParallelAtomicStmt(StmtList entryBody)
        {
            IDictionary<Pair, Set<Pair>> map = new Dictionary<Pair, Set<Pair>>();

            Set<Pair> context;
          
            for (int i = 0; i < entryBody.BigBlocks.Count; ++i)
            {
                BigBlock bb = entryBody.BigBlocks[i];

                if (bb.ec != null && bb.ec is ParallelStmt)
                {
                    ParallelStmt parStmt = bb.ec as ParallelStmt;
                    // collect atomic statements
                    context = new Set<Pair>();
                    foreach(StmtList stmt in parStmt.bodies)
                    {
                        context.AddRange(new AtomicStmtCollector().DeepCollect(stmt));
                    }
                    foreach (Pair pair in context)
                    {
                        //if (pair.Second == null) // if from the current procedure
                        //{
                            map.Add(pair, context);
                        //}
                    }
                }
                else if (bb.ec != null && bb.ec is CobeginStmt)
                {
                    CobeginStmt cobgn = bb.ec as CobeginStmt;
                    if (QKeyValue.FindBoolAttribute(cobgn.attributes, "parallel"))
                    {
                        // collect atomic statements
                        context = new Set<Pair>();
                        foreach (StmtList stmt in cobgn.bodies)
                        {
                            context.AddRange(new AtomicStmtCollector().DeepCollect(stmt));
                        }
                        foreach (Pair pair in context)
                        {
                            //if (pair.Second == null) // if from the current procedure
                            //{
                                map.Add(pair, context);
                            //}
                        }
                    }
                }
                else if (bb.ec != null && bb.ec is ForeachStmt)
                {
                    ForeachStmt feStmt = bb.ec as ForeachStmt;
                    if (QKeyValue.FindBoolAttribute(feStmt.attributes, "parallel"))
                    {
                        // collect atomic statements
                        context = new Set<Pair>();
                        context.AddRange(new AtomicStmtCollector().DeepCollect(feStmt.Body));
                        foreach (Pair pair in context)
                        {
                            //if (pair.Second == null) // if from the current procedure
                            //{
                                map.Add(pair, context);
                            //}
                        }
                    }
                }
            }

            return map;
        }


        //Added for TSO
        public static bool IsLocalExpr(Expr expr)
        {
            Set vars = new Set(); 
            expr.ComputeFreeVariables(vars);
            return Util.FilterGlobalVariables(vars).Count == 0;
        }
        //tso
        public static bool IsGlobalExpr(Expr expr)
        {
            Set vars = new Set();
            expr.ComputeFreeVariables(vars);
            return Util.FilterGlobalVariables(vars).Count > 0;
        }
         ///

        //tso
        // returns how many accesses are made to global variables by this command
        static public int NumGlobalAccesses(Cmd cmd)
        {
            return ComputeGlobalAccesses(cmd).Count;
        }
 
        static public Set ComputeGlobalAccesses(Cmd cmd)
        {
            Set s = ComputeGlobalReads(cmd);
            s.AddRange(ComputeGlobalWrites(cmd));
            return s;
        }

        static public Set ComputeGlobalReads(Cmd cmd)
        {
            return Util.FilterGlobalVariables(ComputeReads(cmd));
        }

        static public Set ComputeGlobalWrites(Cmd cmd)
        {
            return Util.FilterGlobalVariables(ComputeWrites(cmd));
        }

        static public Set ComputeReads(Cmd cmd)
        {

            Set vars = new Set();

            if (cmd is AssertCmd)
            {

                AssertCmd assertCmd = cmd as AssertCmd;

                assertCmd.Expr.ComputeFreeVariables(vars);

            }
            else if (cmd is AssumeCmd)
            {

                AssumeCmd assumeCmd = cmd as AssumeCmd;

                assumeCmd.Expr.ComputeFreeVariables(vars);

            }
            else if (cmd is AssignCmd)
            {

                AssignCmd assignCmd = cmd as AssignCmd;
                foreach (AssignLhs assignLhs in assignCmd.Lhss)
                {
                    if (assignLhs is MapAssignLhs)
                    {
                        MapAssignLhs mapLhs = assignLhs as MapAssignLhs;
                        Debug.Assert(mapLhs.Map is SimpleAssignLhs, "For now, we do nopt allow nested accesses to maps in this situation!");
                        foreach (Expr index in mapLhs.Indexes)
                        {
                            index.ComputeFreeVariables(vars);
                        }
                    }
                }

                foreach (Expr rhs in assignCmd.Rhss)
                {
                    rhs.ComputeFreeVariables(vars);
                }

                //} else if(cmd is ArrayAssignCmd) {

                //    ArrayAssignCmd arrayCmd = (ArrayAssignCmd) cmd;

                //    arrayCmd.Index0.ComputeFreeVariables(vars);
                //    if(arrayCmd.Index1 != null) arrayCmd.Index1.ComputeFreeVariables(vars);
                //    arrayCmd.Rhs.ComputeFreeVariables(vars);			

            }
            else if (cmd is GatedAction)
            {

                GatedAction gact = cmd as GatedAction;

                gact.gate.ComputeFreeVariables(vars);
                gact.action.ComputeFreeVariables(vars);

            }
            else if (cmd is HavocCmd)
            {

                // noop

            }
            else if (cmd is BeginAbstractCmd)
            {

                // noop

            }
            else if (cmd is EndAbstractCmd)
            {

                // noop

            }
            else if (cmd is CallCmd)
            {

                CallCmd callCmd = cmd as CallCmd;

                foreach (Expr var in callCmd.Ins) var.ComputeFreeVariables(vars);

            }

            return vars;

        }

        static public Set ComputeWrites(Cmd cmd)
        {

            Set vars = new Set();

            VariableSeq varseq = new VariableSeq();
            cmd.AddAssignedVariables(varseq);
            foreach (Variable var in varseq)
            {
                vars.Add(var);
            }

            return vars;

            //if (cmd is AssertCmd)
            //{

            //    // noop

            //}
            //else if (cmd is AssumeCmd)
            //{

            //    // noop

            //}
            //else if (cmd is AssignCmd)
            //{

            //    AssignCmd assignCmd = cmd as AssignCmd;
            //    foreach (AssignLhs assignLhs in assignCmd.Lhss)
            //    {
            //        vars.Add(assignLhs.DeepAssignedVariable);
            //    }

            //    //} else if(cmd is ArrayAssignCmd) {

            //    //    ArrayAssignCmd arrayCmd = (ArrayAssignCmd) cmd;

            //    //    arrayCmd.Array.ComputeFreeVariables(vars);			

            //}
            //else if (cmd is GatedAction)
            //{

            //    GatedAction gact = cmd as GatedAction;

            //    foreach (Expr var in gact.mod) var.ComputeFreeVariables(vars);

            //}
            //else if (cmd is HavocCmd)
            //{

            //    HavocCmd havocCmd = cmd as HavocCmd;

            //    foreach (Expr var in havocCmd.Vars) var.ComputeFreeVariables(vars);

            //}
            //else if (cmd is BeginAbstractCmd)
            //{

            //    BeginAbstractCmd abstractCmd = cmd as BeginAbstractCmd;

            //    foreach (Expr var in abstractCmd.Vars) var.ComputeFreeVariables(vars);

            //}
            //else if (cmd is EndAbstractCmd)
            //{

            //    // noop

            //}
            //else if (cmd is CallCmd)
            //{

            //    CallCmd callCmd = cmd as CallCmd;

            //    foreach (Expr var in callCmd.Proc.Modifies) var.ComputeFreeVariables(vars);
            //    foreach (Expr var in callCmd.Outs) var.ComputeFreeVariables(vars);

            //}

        }

        public static Cmd SubstituteReads(Cmd cmd, Hashtable map)
        {
            if (cmd is AssertCmd)
            {

                AssertCmd assertCmd = cmd as AssertCmd;

                assertCmd.Expr = Logic.Substitute(map, assertCmd.Expr);

                return cmd;

            }
            else if (cmd is AssumeCmd)
            {

                AssumeCmd assumeCmd = cmd as AssumeCmd;

                assumeCmd.Expr = Logic.Substitute(map, assumeCmd.Expr);

                return cmd;

            }
            else if (cmd is AssignCmd)
            {
                AssignCmd assignCmd = cmd as AssignCmd;
                for (int i = 0; i < assignCmd.Lhss.Count; ++i)
                {
                    AssignLhs assignLhs = assignCmd.Lhss[i];
                    AssignLhs newLhs = null;
                    if (assignLhs is SimpleAssignLhs)
                    {
                        IdentifierExpr iexpr = Logic.Substitute(map, assignCmd.Lhss[i].DeepAssignedIdentifier) as IdentifierExpr;
                        Debug.Assert(iexpr != null);
                        newLhs = new SimpleAssignLhs(Token.NoToken, iexpr);
                    }
                    else
                    {
                        MapAssignLhs mapLhs = assignLhs as MapAssignLhs;
                        Debug.Assert(mapLhs.Map is SimpleAssignLhs, "For now, we do non't allow nested accesses to maps in this situation!");
                        IdentifierExpr iexpr = Logic.Substitute(map, mapLhs.Map.AsExpr) as IdentifierExpr;
                        Debug.Assert(iexpr != null);
                        SimpleAssignLhs simpleLhs = new SimpleAssignLhs(Token.NoToken, Logic.Substitute(map, mapLhs.Map.AsExpr) as IdentifierExpr);
                        newLhs = new MapAssignLhs(Token.NoToken, simpleLhs, Logic.SubstituteList(map, mapLhs.Indexes));
                    }

                    assignCmd.Lhss[i] = newLhs;
                    assignCmd.Rhss[i] = Logic.Substitute(map, assignCmd.Rhss[i]);
                }

                return cmd;

            }
            //else if (cmd is ArrayAssignCmd)
            //{

            //    ArrayAssignCmd arrayCmd = (ArrayAssignCmd)cmd;

            //    arrayCmd.Index0 = Logic.Substitute(map, arrayCmd.Index0);
            //    if (arrayCmd.Index1 != null) arrayCmd.Index1 = Logic.Substitute(map, arrayCmd.Index1);
            //    arrayCmd.Rhs = Logic.Substitute(map, arrayCmd.Rhs);

            //    return cmd;

            //}
            else if (cmd is GatedAction)
            {

                return cmd;

            }
            else if (cmd is HavocCmd)
            {

                return cmd;

            }
            else if (cmd is BeginAbstractCmd)
            {

                return cmd;

            }
            else if (cmd is EndAbstractCmd)
            {

                return cmd;

            }
            else if (cmd is CallCmd)
            {

                CallCmd callCmd = cmd as CallCmd;

                List<Expr> newIns = new List<Expr>();

                foreach (Expr var in callCmd.Ins)
                {
                    newIns.Add(Logic.Substitute(map, var));
                }

                callCmd.Ins = newIns;

                return cmd;
            }

            Debug.Assert(false, "Unrecognized command: " + cmd.ToString());
            return cmd;
        }

        static public Set<AtomicBlock> ComputeReachableAtomicBlocks(AtomicBlock atomicBlock)
        {
            Set<AtomicBlock> blocks = new Set<AtomicBlock>();

            Stack<AtomicBlock> work = new Stack<AtomicBlock>();
            work.Push(atomicBlock);
            blocks.Add(atomicBlock);

            while (work.Count > 0)
            {
                AtomicBlock ablock = work.Pop();
                foreach (AtomicBlock succ in ablock.Successors)
                {
                    if (!blocks.Contains(succ))
                    {
                        blocks.Add(succ);
                        work.Push(succ);
                    }
                }
            }

            return blocks;
        }

        static public Graph<Block> GraphFromImpl(Implementation impl)
        {
            Graph<Block> g = new Graph<Block>();
            g.AddSource(impl.Blocks[0]); // there is always at least one node in the graph
            foreach (Block b in impl.Blocks)
            {
                GotoCmd gtc = b.TransferCmd as GotoCmd;
                if (gtc != null)
                {
                    foreach (Block dest in gtc.labelTargets)
                    {
                        g.AddEdge(b, dest);
                    }
                }
            }
            return g;
        }

#if false
    static public Set<Block> ComputeBackEdges(LoopBlock loopBlock)
    {
        // add assertion to the back edges
        Implementation impl = loopBlock.procState.impl;

        impl.PruneUnreachableBlocks();

        // compute loops
        Graph<Block> g = CodeAnalyses.GraphFromImpl(impl);

        g.ComputeLoops(); // this is the call that does all of the processing
        if (!g.Reducible)
        {
            Debug.Assert(false);
        }

        Set<Block> backEdges = new Set<Block>();
        foreach (Block b in g.BackEdgeNodes(loopBlock.LoopInfo.Header))
        {
            backEdges.Add(b);
        }

        return backEdges;
    }

    static public VariableSeq ComputeModifiedVars(LoopBlock loopBlock)
    {
        Debug.Assert(loopBlock.startBlock == loopBlock.LoopInfo.Header);
        Block header = loopBlock.LoopInfo.Header;

        ProcedureState procState = loopBlock.procState;

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

        return modifiedVars;
    }

#endif


        internal static VariableSeq GetAssignedGlobalVars(StmtList stmt)
        {
            VariableSeq vars = new VariableSeq();
            Set<BigBlock> bbs = new BigBlocksCollector().Collect(stmt);
            foreach (BigBlock bb in bbs)
            {
                foreach (Cmd cmd in bb.simpleCmds)
                {
                    cmd.AddAssignedVariables(vars);
                }
            }
            return Util.RemoveDuplicates(Util.FilterGlobalVariables(vars));
        }
    } // end CodeAnalyses

    public class CallGraph : StmtVisitor
    {
        List<ProcedureState> procStates;
        int current;
        private bool[,] callMap;

        public bool Query(ProcedureState from, ProcedureState to)
        {
            return callMap[indexOf(from), indexOf(to)];
        }

        // multiple levels
        public List<ProcedureState> CollectCallers(ProcedureState procState)
        {
            List<ProcedureState> callers = new List<ProcedureState>();
            Queue<ProcedureState> q = new Queue<ProcedureState>();
            q.Enqueue(procState);
            while (q.Count > 0)
            {
                ProcedureState p = q.Dequeue();
                int i = indexOf(p);
                for (int j = 0; j < procStates.Count; ++j)
                {
                    if (i != j && callMap[j, i] == true)
                    {
                        ProcedureState caller = procStates[j];
                        if (!callers.Contains(caller))
                        {
                            callers.Add(caller);
                            q.Enqueue(caller);
                        }
                    }
                }
            }
            return callers;
        }

        // only one level
        public List<ProcedureState> CollectCallees(ProcedureState procState)
        {
            List<ProcedureState> callees = new List<ProcedureState>();

            int i = indexOf(procState);
            for (int j = 0; j < procStates.Count; ++j)
            {
                if (i != j && callMap[i, j] == true)
                {
                    ProcedureState callee = procStates[j];
                    if (!callees.Contains(callee))
                    {
                        callees.Add(callee);
                    }
                }
            }
            return callees;
        }

        private int indexOf(ProcedureState procState)
        {
            int found = -1;
            for (int i = 0; i < procStates.Count; ++i)
            {
                if (procStates[i] == procState)
                {
                    found = i;
                    break;
                }
            }
            Debug.Assert(found >= 0);
            return found;
        }

        private int indexOf(string name)
        {
            int found = -1;
            for (int i = 0; i < procStates.Count; ++i)
            {
                if (procStates[i].Name == name)
                {
                    found = i;
                    break;
                }
            }
            Debug.Assert(found >= 0);
            return found;
        }

        public CallGraph(ProofState proofState)
        {
            procStates = new List<ProcedureState>(proofState.ProcedureStates);
            callMap = new bool[procStates.Count, procStates.Count];

            callMap.Initialize(); // initialize to false
            for (int i = 0; i < procStates.Count; ++i)
            {
                current = i;
                ProcedureState procState = procStates[current];
                VisitStmtList(procState.Body);
            }
        }

        public override Cmd VisitCallCmd(CallCmd node)
        {
            string procName = node.Proc.Name;
            callMap[current,indexOf(procName)] = true;

            return base.VisitCallCmd(node);
        }
    }

  
} // end namespace QED