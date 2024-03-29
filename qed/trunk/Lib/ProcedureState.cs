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
    using Microsoft.Glee.Drawing;
    using Graphing;
    using Type = Microsoft.Boogie.Type;
    using System.Text;
    using PureCollections;


    public class LoopInfo
    {
        public BigBlock Parent;
        public ControlBlock Head;
        public ControlBlock Tail;

        public LoopInfo(BigBlock bb, ControlBlock h, ControlBlock t)
        {
            this.Parent = bb;
            this.Head = h;
            this.Tail = t;
        }

        internal void CheckAtomicBody(AtomicBlock bodyBlock)
        {
            Set<APLBlock> succBody = bodyBlock.Successors;
            Debug.Assert(succBody.Count >= 1 && succBody.Contains(this.Tail));
            //Debug.Assert(this.Head.Successors.Contains(bodyBlock));
        }
    }

    public class ProcedureState
    {

        public bool IsReduced;

        public bool IsPublic;

        private bool isAtomic;
        public bool IsAtomic
        {
            get { ComputeAtomicBlocks(); return this.isAtomic; }
        }

        public bool IsAutoLabel;

        public Implementation impl;

        //public List<AtomicStmt> atomicStmts;

        public IDictionary<string, APLStmt> aplStmtMap;
        public IDictionary<string, APLBlock> aplBlockMap;
        public IDictionary<WhileCmd, LoopInfo> loopInfoMap;

        public Hashtable localVars;

        public Hashtable modifiesMap;

        public IdentifierExpr pcExpr;

        public IdentifierExpr exExpr;

        public Hashtable auxVars;

        public Hashtable hiddenVars;

        public VariableSeq primes;

        public Hashtable primesMap;

        public IDictionary<ProcedureState, List<CallStmt>> callerStmtMap;

        //public IDictionary<Block,LoopInfo> loopInfoMap;

        public List<Expr> localinvs;

        public Set<Variable> thrLocalVars;

        // public BigBlock whileStarDrainBlock;
        public int cloneCount;
        public bool hasTransformed;

        public void MarkAsTransformed()
        {
            this.hasTransformed = true;
        }

        //public Set<CondAssumeCmd> condAssumesForLoops;

        //public Set<CondAssertCmd> condAssertsToCheck;

        public string Name
        {
            get
            {
                return impl.Name;
            }
        }

        protected MoverType mover;

        virtual public MoverType Mover
        {
            get
            {
                return mover;
            }
            set
            {
                mover = value;
            }
        }

        public string CurrentStateInfo()
        {
            StringBuilder strb = new StringBuilder();

            strb.Append("Procedure ").Append(this.Name).AppendLine(IsReduced ? " (Reduced)" : "");

            strb.Append("Precond: ").Append(Output.ToString(this.Pre)).AppendLine();
            strb.Append("Postcond: ").Append(Output.ToString(this.Post)).AppendLine();

            strb.Append("Modifies: ");
            foreach (Variable modVar in modifiesMap.Keys)
            {
                strb.Append(modVar.Name).Append(" ");
            }

            return strb.ToString();
        }

        public ProcedureState(Implementation impl, bool isatomic, bool autolabel, bool ispublic)
        {

            this.isAtomic = isatomic;
            this.IsAutoLabel = autolabel;

            this.IsPublic = ispublic;

            this.IsReduced = false;

            this.impl = impl;

            this.callerStmtMap = new Dictionary<ProcedureState, List<CallStmt>>();

            this.localVars = new Hashtable();

            this.modifiesMap = new Hashtable();

            this.localinvs = new List<Expr>();

            this.thrLocalVars = new Set<Variable>();

            primesMap = new Hashtable();
            primes = new VariableSeq();
            //	whileStarDrainBlock = new BigBlock(Token.NoToken, null, new CmdSeq(), null, null);
            //condAssumesForLoops = new Set<CondAssumeCmd>();
            //condAssertsToCheck = new Set<CondAssertCmd>();
            this.hasTransformed = true;
            this.mover = null; // not a mover
        }

        public void Init(ProofState proofState)
        {

            auxVars = new Hashtable();
            hiddenVars = new Hashtable();

            // compute local variables
            foreach (Variable var in impl.InParams)
            {
                AddLocalVar(var, true);
            }

            foreach (Variable var in impl.OutParams)
            {
                AddLocalVar(var, true);
            }

            foreach (Variable var in impl.LocVars)
            {

                AddLocalVar(var, true);

                if (QKeyValue.FindBoolAttribute(var.Attributes, "isaux"))
                {
                    MakeAuxVar(var as LocalVariable);
                }

                if (QKeyValue.FindBoolAttribute(var.Attributes, "ishidden"))
                {
                    HideVar(var as LocalVariable);
                }

            }

            // TODO: do we need to make every procedure modify error?
            // this.impl.Proc.Modifies.Add(proofState.errorExpr);
            foreach (IdentifierExpr modexpr in this.impl.Proc.Modifies)
            {
                modifiesMap[modexpr.Decl] = null;
            }

            //---------------------

            // replace all asserts with conditional assert that are disabled at the beginning
            //ReplaceCondPredicateCmds(impl); // TODO: removed

            InitPc();

            InitEx();

            // this adds a new block at the beginning, so leave it before computing the atomic blocks
            //InitEntryBlock(impl);

            //---------------------

            // ensure that there is only one return block
            // note that ComputeLoops may create new return blocks but they are not considered here, so do this before computing loops
            //UnifyReturnBlocks(impl);

            //---------------------

            // computes loops and converts cfg to dag
            //ComputeLoops();

            //-----------------------------------

            if (this.isAtomic)
            {
                // surround the code with atomic
                AtomicStmt atomBody = CodeTransformations.MakeAtomic(this.Body, (this.IsAutoLabel ? "Body" : null));
                // assign the name of the block to the atomic body
                //CodeTransformations.RenameAtomicStmt(atomBody, "Body"); // the above call handles this (TODO: any difference?)
            }

            //-----------------------------------
            // resolve-typecheck
            ResolveTypeCheckStmt();

            // set the new body of the implementation
            CodeTransformations.TranslateToAPLStatements(this, this.Body);

            CodeTransformations.RemoveUnreachableLabels(this.Body);

            ForceComputeAtomicBlocks();
        }

        //private void ReplaceCondPredicateCmds(Implementation impl) {
        //    foreach(Block block in impl.Blocks) {
        //        CmdSeq newCmds = new CmdSeq();
        //        foreach(Cmd cmd in block.Cmds) {
        //            if(cmd is AssertCmd) {
        //                CondAssertCmd cac = new CondAssertCmd(cmd.tok, (cmd as AssertCmd).Expr, false);
        //                this.condAssertsToCheck.Add(cac);

        //                newCmds.Add(cac);					
        //            } else {
        //                newCmds.Add(cmd);
        //            }
        //        }
        //        block.Cmds = newCmds;
        //    }
        //}

        public void ForceComputeAtomicBlocks()
        {
            MarkAsTransformed();
            ComputeAtomicBlocks();
        }

        public void ComputeAtomicBlocks()
        {
            if (hasTransformed)
            {
                CodeTransformations.PostProcessStmts(this, this.Body);

                /////////////////////////////////////

                // resolve-typecheck
                ResolveTypeCheckStmt();

                // we translate the body to boogie blocks and procudure atomic blocks
                Qoogie2Boogie translator = new Qoogie2Boogie();

                translator.TranslateStmt(this, this.Body);

                // register atomic stmts
                aplStmtMap = translator.APLStmtMap;

                /**/
          //     foreach(KeyValuePair<string, APLStmt> pair in aplStmtMap){ Output.AddLine(" Stmt " + pair.Key.ToString());}
                
                // register atomic blocks
                aplBlockMap = translator.APLBlockMap;
          //     foreach (KeyValuePair<string, APLBlock> pair in aplBlockMap){ Output.AddLine(" Block " + pair.Key.ToString());}
                

                // register loop infors
                loopInfoMap = translator.LoopInfoMap;

                impl.Blocks.Clear();
                impl.Blocks.AddRange(translator.Blocks);

                // resolve-typecheck
                ResolveTypeCheckBlocks();

                // make sure this is before CheckAndSetIsAtomic
                hasTransformed = false;

                // set IsAtomic
                CheckAndSetIsAtomic();

                ResetMoverTypes();

                ComputeDeadLocals();
            }
        }

        private bool CheckAndSetIsAtomic()
        {
            this.isAtomic = false;
            if (this.Body.BigBlocks.Count == 1)
            {
                AtomicStmt atomicStmt = this.Body.BigBlocks[0].ec as AtomicStmt;
                if (atomicStmt != null)
                {
                    Debug.Assert(this.AtomicBlocks.Count == 1);
                    this.isAtomic = true;
                }
            }
            return this.isAtomic;
            //int c1 = this.AtomicBlocks.Count;
            //int c2 = this.Atoms.Count;
            //this.IsAtomic = (c1 == 1 && c2 == 1);
        }

        // computes dead local variables and assigns them to atomic blocks
        private void ComputeDeadLocals()
        {
            Set<Variable> locals = new Set<Variable>();
            this.InitialAPLBlock.ComputeDeadLocals(locals);
        }

        private void ResetMoverTypes()
        {
            foreach (AtomicBlock atomicBlock in AtomicBlocks)
            {
                // this sets the mover type of the AtomicStmt as well
                atomicBlock.Mover = MoverType.NonMover;
            }
        }

        private void ResolveTypeCheckBlocks()
        {
            BoogiePL.Errors.count = 0;

            impl.Proc = null; // forces resolution
            impl.Resolve(ProofState.GetInstance().GetResolutionContext(false));
            impl.Typecheck(ProofState.GetInstance().GetTypecheckingContext());

            RecomputeBlockPredecessors();
        }

        private void ResolveTypeCheckStmt()
        {
            BoogiePL.Errors.count = 0;

            Debug.Assert(impl.Proc != null);
            ResolutionContext rc = this.GetResolutionContext(false);
            TypecheckingContext tc = this.GetTypecheckingContext();

            Set<BigBlock> bbs = new BigBlocksCollector().Collect(this.Body);
            foreach (BigBlock bb in bbs)
            {
                foreach (Cmd cmd in bb.simpleCmds)
                {
                    cmd.Resolve(rc);
                }

                if (bb.ec is IfCmd)
                {
                    IfCmd ifCmd = bb.ec as IfCmd;
                    if (ifCmd.Guard != null)
                        ifCmd.Guard.Resolve(rc);
                }

                if (bb.ec is ForeachStmt)
                {
                    ForeachStmt feachStmt = bb.ec as ForeachStmt;
                    if (feachStmt.iterVar != null)
                    {
                        Debug.Assert(feachStmt.collVar != null);
                        feachStmt.iterVar.Resolve(rc);
                        feachStmt.collVar.Resolve(rc);
                    }
                    foreach (PredicateCmd inv in feachStmt.Invariants)
                    {
                        inv.Resolve(rc);
                    }
                }
                else
                    if (bb.ec is WhileCmd)
                    {
                        WhileCmd whileCmd = bb.ec as WhileCmd;
                        if (whileCmd.Guard != null)
                            whileCmd.Guard.Resolve(rc);
                        foreach (PredicateCmd inv in whileCmd.Invariants)
                        {
                            inv.Resolve(rc);
                        }
                    }
            }

            foreach (BigBlock bb in bbs)
            {
                foreach (Cmd cmd in bb.simpleCmds)
                {
                    cmd.Typecheck(tc);
                }

                if (bb.ec is IfCmd)
                {
                    IfCmd ifCmd = bb.ec as IfCmd;
                    if (ifCmd.Guard != null)
                        ifCmd.Guard.Typecheck(tc);
                }

                if (bb.ec is ForeachStmt)
                {
                    ForeachStmt feachStmt = bb.ec as ForeachStmt;
                    if (feachStmt.iterVar != null)
                    {
                        Debug.Assert(feachStmt.collVar != null);
                        feachStmt.iterVar.Typecheck(tc);
                        feachStmt.collVar.Typecheck(tc);
                    }
                    foreach (PredicateCmd inv in feachStmt.Invariants)
                    {
                        inv.Typecheck(tc);
                    }
                }
                else
                    if (bb.ec is WhileCmd)
                    {
                        WhileCmd whileCmd = bb.ec as WhileCmd;
                        if (whileCmd.Guard != null)
                            whileCmd.Guard.Typecheck(tc);
                        foreach (PredicateCmd inv in whileCmd.Invariants)
                        {
                            inv.Typecheck(tc);
                        }
                    }
            }
        }

        public List<AtomicBlock> AtomicBlocks
        {
            get
            {
                Debug.Assert(!this.hasTransformed);

                List<AtomicBlock> atomicBlocks = new List<AtomicBlock>();
                foreach (APLBlock apl in aplBlockMap.Values)
                {
                    if (apl is AtomicBlock && !(apl is StraightAtomicBlock))
                    {
                        atomicBlocks.Add(apl as AtomicBlock);
                    }
                }

                return atomicBlocks;
            }
        }

        public List<APLBlock> Atoms
        {
            get
            {
                Debug.Assert(!this.hasTransformed);

                List<APLBlock> atoms = new List<APLBlock>();
                foreach (APLBlock apl in aplBlockMap.Values)
                {
                    //if (!Qoogie.IsInAtomic(apl.parentApl))
                    //{
                    atoms.Add(apl);
                    //}
                }

                return atoms;
            }
        }

        //public List<AtomicStmt> AtomicStmts
        //{
        //    get
        //    {
        //        List<AtomicStmt> atomicStmts = new List<AtomicStmt>();
        //        foreach (APLStmt apl in aplStmtMap.Values)
        //        {

        //            if (apl is AtomicStmt)
        //            {
        //                atomicStmts.Add(apl as AtomicStmt);
        //            }
        //        }

        //        return atomicStmts;
        //    }
        //}

        //public List<CallStmt> CallStmts
        //{
        //    get
        //    {
        //        List<CallStmt> callStmts  = new List<CallStmt>();
        //        foreach (APLStmt apl in aplStmtMap.Values)
        //        {

        //            if (apl is CallStmt)
        //            {
        //                callStmts.Add(apl as CallStmt);
        //            }
        //        }

        //        return callStmts;
        //    }
        //}

        public StmtList Body
        {
            get
            {
                return impl.StructuredStmts;
            }
            set
            {
                impl.StructuredStmts = value;
            }
        }

        public APLBlock InitialAPLBlock
        {
            get
            {
                Block block = impl.Blocks[0];
                return LookupAPLBlockStarts(block);
            }
        }

        public Expr MapExprFromProcToImpl(Expr expr)
        {
            Hashtable map = this.impl.GetImplFormalMap();
            Expr mappedExpr = Logic.Substitute(map, expr);
            return mappedExpr;
        }

        //static private void UnifyReturnBlocks(Implementation impl) {
        //    int returnBlocks = 0;
        //    foreach ( Block b in impl.Blocks ) {
        //      if (b.TransferCmd is ReturnCmd) {
        //        returnBlocks++;
        //      }
        //    }
        //    if (returnBlocks > 1) {
        //        // merge return blocks into one
        //        Block returnBlock = new Block(Token.NoToken, "ExitBlock", new CmdSeq(), new ReturnCmd(Token.NoToken));
        //        foreach(Block block in impl.Blocks) {
        //            if(block.TransferCmd is ReturnCmd) {
        //                GotoCmd gotoCmd = new GotoCmd(Token.NoToken, new BlockSeq(returnBlock));
        //                block.TransferCmd = gotoCmd;
        //            }
        //        }
        //        impl.Blocks.Add(returnBlock);

        //        // Verifier.ResolveTypeCheck(ProofState.GetInstance().program);
        //    }
        //}

        int nextFreshLocalVarId = 0;
        public Variable CreateFreshLocalVar(Type type)
        {
            Variable fvar = CreateFreshLocalVar("fresh_" + nextFreshLocalVarId.ToString(), type, true);

            ++nextFreshLocalVarId;

            return fvar;
        }

        public Variable CreateFreshLocalVar(string name, Type type)
        {
            return CreateFreshLocalVar(name, type, true);
        }

        public Variable CreateFreshLocalVar(string name, Type type, bool visible)
        {

            LocalVariable fvar = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, name, type));

            if (visible)
            {
                impl.LocVars.Add(fvar);
            }
            AddLocalVar(fvar, visible);

            return fvar;
        }

        // add variable to locals before calling this method
        // this method does not add it to the locals of impl, do it beforehand
        public void AddLocalVar(Variable var, bool visible)
        {
            //if(!impl.LocVars.Has(var)) {
            //	impl.LocVars.Add(var);
            //}
            Debug.Assert(!visible || impl.LocVars.Has(var) || impl.InParams.Has(var) || impl.OutParams.Has(var));

            localVars[var.Name] = var;
            IdentifierExpr primeExpr = Logic.MakePrimedExpr(var);

            primesMap[var] = primeExpr;

            primes.Add(primeExpr.Decl);
        }

        public void RemoveLocalVar(Variable var)
        {
            Variable prime = GetPrimedVar(var);

            localVars.Remove(var.Name);
            impl.LocVars = Util.RemoveFromVarSeq(impl.LocVars, var);

            primesMap.Remove(var);

            primes = Util.RemoveFromVarSeq(primes, prime);

            // remove from aux vars and hidden vars
            if (auxVars.ContainsKey(var.Name))
            {
                auxVars.Remove(var.Name);
            }

            if (hiddenVars.ContainsKey(var.Name))
            {
                hiddenVars.Remove(var.Name);
            }
        }

        public Variable GetLocalVar(string name)
        {
            if (!localVars.ContainsKey(name)) return null;
            return (Variable)this.localVars[name];
        }

        public Variable GetPrimedVar(Variable var)
        {
            return GetPrimedExpr(var).Decl;
        }

        public IdentifierExpr GetPrimedExpr(Variable var)
        {
            if (primesMap.Contains(var))
                return (IdentifierExpr)primesMap[var];
            else
                return ProofState.GetInstance().GetPrimedExpr(var);
        }

        public IdentifierExpr GetPrimedExpr(IdentifierExpr expr)
        {
            return GetPrimedExpr(expr.Decl);
        }

        public Hashtable AllPrimesMap
        {
            get
            {
                Hashtable map = new Hashtable();

                foreach (object key in ProofState.GetInstance().primesMap.Keys)
                {
                    map.Add(key, ProofState.GetInstance().primesMap[key]);
                }

                foreach (object key in this.primesMap.Keys)
                {
                    map.Add(key, this.primesMap[key]);
                }
                return map;
            }
        }

        public GatedAction Spec
        {
            get
            {
                Expr gate = this.Requires;

                Expr action = this.Ensures;

                IdentifierExprSeq mod = impl.Proc.Modifies;

                GatedAction gact = new GatedAction(Token.NoToken, gate, action, mod, true);

                return gact;
            }
        }

        public GatedAction SpecAtCall(ProcedureState caller, CallCmd callCmd)
        {

            Expr gate = this.RequiresAtCall(caller, callCmd);

            Expr action = this.EnsuresAtCall(caller, callCmd);

            // modifies
            IdentifierExprSeq mod = new IdentifierExprSeq(impl.Proc.Modifies);
            // outputs
            for (int j = 0, n = callCmd.Outs.Count; j < n; ++j)
            {
                mod.Add(callCmd.Outs[j]);
            }
            // aux vars
            foreach (Variable auxVar in ProofState.GetInstance().AuxVars)
            {
                mod.Add(new IdentifierExpr(Token.NoToken, auxVar));
            }

            GatedAction gact = new GatedAction(Token.NoToken, gate, action, mod, true);

            return gact;
        }

        public Expr MakePrime(Expr expr)
        {
            return Logic.Substitute(this.AllPrimesMap, expr);
        }

        public Expr MakeUnprimed(Expr expr)
        {
            Hashtable reverseMap = new Hashtable();

            Hashtable allPrimesMap = this.AllPrimesMap;

            foreach (Variable var in allPrimesMap.Keys)
            {
                IdentifierExpr iexpr = allPrimesMap[var] as IdentifierExpr;
                Debug.Assert(iexpr != null);
                reverseMap.Add(iexpr.Decl, new IdentifierExpr(Token.NoToken, var));
            }
            return Logic.Substitute(reverseMap, expr);
        }

        //public void EnableCondAssumesForLoops() {
        //    foreach(CondAssumeCmd ac in condAssumesForLoops) {
        //        ac.IsEnabled = true;
        //    }

        //    ClearTransitionPredicates();
        //}

        //public void DisableCondAssumesForLoops() {
        //    foreach(CondAssumeCmd ac in condAssumesForLoops) {
        //        ac.IsEnabled = false;
        //    }

        //    ClearTransitionPredicates();
        //}

        //public void EnableCondAssertsToCheck() {
        //    foreach(CondAssertCmd ac in condAssertsToCheck) {
        //        ac.IsEnabled = true;
        //    }

        //    ClearTransitionPredicates();
        //}

        //public void DisableCondAssertsToCheck() {
        //    foreach(CondAssertCmd ac in condAssertsToCheck) {
        //        ac.IsEnabled = false;
        //    }

        //    ClearTransitionPredicates();
        //}

        //public void ClearTransitionPredicates()
        //{
        //    foreach (APLBlock apl in aplBlockMap.Values)
        //    {
        //        apl.ClearTransitionPredicate();
        //    }
        //}

        //public void RecomputeTransitionPredicates()
        //{
        //    ClearTransitionPredicates();
        //    foreach (AtomicBlock atomicBlock in atomicBlockMap.Values)
        //    {
        //        atomicBlock.RecomputeTransitionPredicate();
        //    }
        //}

        public void RegisterCaller(ProcedureState callerProc, CallStmt callStmt)
        {
            List<CallStmt> stmts;

            if (!callerStmtMap.ContainsKey(callerProc))
            {
                stmts = new List<CallStmt>();
                callerStmtMap.Add(callerProc, stmts);
            }

            stmts = callerStmtMap[callerProc];
            if (!stmts.Contains(callStmt))
            {
                stmts.Add(callStmt);
            }
        }
        //TSO
       /* public void ReduceSingleDrainHead(ProofState pf)
        {
            foreach (ProcedureState callerProc in callerStmtMap.Keys)
            {
                List<CallStmt> callerStmts = callerStmtMap[callerProc];
                Set<AtomicStmt> atoms = new AtomicStmtCollector().Collect(callerProc.Body);
                foreach (AtomicStmt atom in atoms)//CallStmt callStmt in callerStmts
                {
                    // remove the straight atomic statements inside
                    if (atom.straightAtoms.Count == 2)
                    {
                        Set<BigBlock> bbs = new BigBlocksCollector().Collect(atom.body);
                        
                        foreach (BigBlock bb in bbs)
                        {
                            if (bb.ec != null && bb.ec is AtomicStmt)
                            {
                                StraightAtomicStmt satom = bb.ec as StraightAtomicStmt;
                                Debug.Assert(satom != null);
                                CodeTransformations.ReplaceWith(satom, satom.body);
                            }
                            
                            if (bb.ec != null && bb.simpleCmds[0] is AssertCmd)
                            {

                                AssertCmd isBufEmpty = bb.simpleCmds[0] as AssertCmd;
                                

                            
                            }

                        }

                        atom.straightAtoms.Clear();
                    }
                }
            }
        
        
        }
*/

        //TSO
        public void DestroyEmptyDrains(ProofState pf)
        {
            AssertCmd isBufEmpty = SetAssertCmdForIsBufEmpty(pf);

           foreach (ProcedureState callerProc in callerStmtMap.Keys)
            {
                if (callerProc.Name != "dummy_while")
                {

                    List<CallStmt> callerStmts = callerStmtMap[callerProc];

                    foreach (CallStmt callStmt in callerStmts)
                    {
                        if (callStmt.CalleeName == "drainHead")
                        {
                            StmtList parentStmt = callStmt.body.ParentContext;
                            BigBlock parentBB = callStmt.body.ParentContext.ParentBigBlock; // this is while Cmd

                          

                            if (parentBB.ec is WhileCmd && parentStmt.BigBlocks.Count == 2 && parentStmt.BigBlocks[0].ec is AtomicStmt)
                            {                                
                                AtomicStmt asrtAtom = parentStmt.BigBlocks[0].ec as AtomicStmt;
                                if (asrtAtom.body.BigBlocks[0].simpleCmds[0] is AssertCmd && parentStmt.BigBlocks[1].ec is CallStmt)
                                {
                                 //   Output.AddLine("Label of atomic assert is  " + asrtAtom.label);
                                   // Output.AddLine("Label of block next to atomic is " + parentStmt.BigBlocks[1].LabelName);
                                
                                
                                    AssertCmd asrt = asrtAtom.body.BigBlocks[0].simpleCmds[0] as AssertCmd;
                                 //   Output.AddLine("Expressionlar esit " + isBufEmpty.Expr.Equals(asrt.Expr));
                                    /*&&*/
                                        CallStmt cls = parentStmt.BigBlocks[1].ec as CallStmt;
                                        Output.AddLine("Label of call statement is " + cls.label);
                                        if (cls.CalleeName == "drainHead" && asrt.Expr.Equals( isBufEmpty.Expr))
                                        {
                                            parentStmt.BigBlocks.RemoveAt(1);
                                        }
                                    
                                }
                            }
                        }
                    }
                }
                callerProc.MarkAsTransformed();
            }
        }
        
        
        

        // TSO
        public void ReduceWhileStarDrains(ProofState pf)
        {
            //List<BigBlock> bodyInsert = SetWhileStarBlock(pf);
            //  Output.AddLine(" BigBlock call  " + toInsert.);
            List<BigBlock> toDeleteBB = new List<BigBlock>();

            //List<CallStmt> ntoDelete = new List<CallStmt>();
            //KeyValuePair<string,int> toDelete =new KeyValuePair<string,int>();
            IDictionary<int, BigBlock> toDelete = new Dictionary<int, BigBlock>();
            
            foreach (ProcedureState callerProc in callerStmtMap.Keys)
            {
                if (callerProc.Name != "dummy_while")
                {

                    List<CallStmt> callerStmts = callerStmtMap[callerProc];

                    foreach (CallStmt callStmt in callerStmts)
                    {
                        if (callStmt.CalleeName == "drainHead" &&
                            callStmt.body.ParentContext.BigBlocks.Count == 1 &&
                            callStmt.body.ParentContext.BigBlocks[0].ec is CallStmt)
                        {

                            StmtList parentStmt = callStmt.body.ParentContext;
                            StmtList parenparentStmt = callStmt.body.ParentContext.ParentContext;

                            BigBlock parentBB = callStmt.body.ParentContext.ParentBigBlock; // this is while Cmd
                           
                            //  Output.AddLine("First Block label " + parentStmt.BigBlocks[0].LabelName);
                            // Output.AddLine("Count in block " + parentStmt.BigBlocks.Count.ToString());
                            
                            for (int i = 0; i < parenparentStmt.BigBlocks.Count ;  i++)
                            {
                                //if(parentStmt.BigBlocks[i] == parentBB)
                                if (parenparentStmt.BigBlocks[i].ec is WhileCmd)
                                {
                                    WhileCmd whileDrain = parenparentStmt.BigBlocks[i].ec as WhileCmd;
                                    Output.AddLine("First Block label" + whileDrain.Body.BigBlocks[0].LabelName);
                                    
                                    if (whileDrain.Body.BigBlocks[0].ec is CallStmt && whileDrain.Body.BigBlocks.Count == 1  )
                                    {
                                        CallStmt drainHead = whileDrain.Body.BigBlocks[0].ec as CallStmt;
                                       // CallStmt drainHeadNext = whileDrainNext.Body.BigBlocks[0].ec as CallStmt;

                                        if (drainHead.CalleeName == "drainHead" )
                                        {
                                            
                                            //toDeleteBB.Add(parenparentStmt.BigBlocks[i]);
                                            toDelete.Add(i, parenparentStmt.BigBlocks[i]);
                                            
                                            Output.AddLine("Deleted While*drainHead label ADDED : " + callStmt.label);
                                            
                                        }
                                    }
                                }
                            }
                            // Now Delete Operation for each callStmt parentStmt
                            //
                            foreach(KeyValuePair<int,BigBlock> p in toDelete)
                            {
                                if (toDelete.ContainsKey(p.Key+1))
                                {
                                    parenparentStmt.BigBlocks.Remove(p.Value);

                                }
                            }
                             toDelete.Clear();
                        } // Collected all whileDrain* drainHead for each drainhead call 's parentStmt
                        //
                       
                        


                    }
                }
                callerProc.MarkAsTransformed();
            }
            // Now delete



            //
            /*  for (int i=ntoDelete.Count-1; i >=0 ; i=i-2) {
                 StmtList parentStmt = ntoDelete[i].body.ParentContext.ParentContext;
                 BigBlock parentBB = ntoDelete[i].body.ParentContext.ParentBigBlock; // this is while Cmd
                 if (!(parentBB.ec is WhileCmd))
                 {
                     Output.AddError(" Call statment drainHead must be in while(*){ } ");

                 }
                 Output.AddLine("Now deleting the label of : " + parentBB.LabelName);
                // parentStmt.BigBlocks.Remove(parentBB);
                   
              }*/
        }



        public AssumeCmd SetAssumeCmdForIsBufEmpty(ProofState pf)
        {
            ProcedureState dummy_while_state = pf.GetProcedureState("dummy_emptyBuf_assume");

            AtomicStmt isBufEmptyAtom = dummy_while_state.Body.BigBlocks[0].ec as AtomicStmt;

            AssumeCmd isBufEmpty = isBufEmptyAtom.body.BigBlocks[0].simpleCmds[0] as AssumeCmd;

            return isBufEmpty;
        }
        


        public AssertCmd SetAssertCmdForIsBufEmpty(ProofState pf) {
            ProcedureState dummy_while_state = pf.GetProcedureState("dummy_emptyBuf");

            AtomicStmt isBufEmptyAtom = dummy_while_state.Body.BigBlocks[0].ec as AtomicStmt;

            AssertCmd isBufEmpty = isBufEmptyAtom.body.BigBlocks[0].simpleCmds[0] as AssertCmd;

            return isBufEmpty;
        }
                  

        public List<BigBlock> SetWhileStarBlock(ProofState pf)
        {
            ProcedureState dummy_while_state = pf.GetProcedureState("dummy_while");

            /*
                        for(int i=0 ; i< dummy_while_state.Body.BigBlocks.Count ; i++ )
                        {
                            Output.AddLine("Block Count " + i+ " of the WhileStarDrain " + dummy_while_state.Body.BigBlocks[i].LabelName);
                        }
            */

            return dummy_while_state.Body.BigBlocks;




        }

        // Added for tso // proofcommand2
        public void EliminateIsAtHeadAndDrainAsm(ProofState proofState, ProcedureState procState, AtomicStmt atom)
        {

            Qoogie.ResolveStmt(procState.Body);
            AssumeCmd isBufEmpty = SetAssumeCmdForIsBufEmpty(proofState);

            BigBlock atomBB = atom.body.ParentBigBlock;



            if (atom.body.BigBlocks.Count == 2)
            {

                if (atom.body.BigBlocks[0].ec is AtomicStmt &&
                    atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec is CallStmt)
                {
                    CallStmt isAtH = atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec as CallStmt;
                    AtomicStmt isBufEmpAtom = atom.body.BigBlocks[0].ec as AtomicStmt;
                    if (!(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssumeCmd)) { Output.AddError("If(*) must include AssumeCmd"); }
                    //Debug.Assert(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssumeCmd);
                    
                    AssumeCmd isBufEmpAssert = isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] as AssumeCmd;



                    if (isAtH.cmd.Proc.Name == "isAtHeadAndDrain" && isBufEmpAssert.Expr.Equals(isBufEmpty.Expr))
                    {

                        CodeTransformations.RemoveAt(atom.body, atom.body.BigBlocks.Count - 1);
                        AssumeCmd assumefalse = new AssumeCmd(Token.NoToken, Expr.False);
                        BigBlock asfalse = new BigBlock(Token.NoToken, atom.body.BigBlocks[0].LabelName + "_assume_false", new CmdSeq(assumefalse), null, null);
                        CodeTransformations.InsertAt(atom.body, asfalse, atom.body.BigBlocks.Count - 1);
                    }

                }

            }
        
        }

        // Added for tso // proofcommand2
        public void EliminateIsAtHeadAndDrain(ProofState proofState, ProcedureState procState, AtomicStmt atom)
        {

            Qoogie.ResolveStmt(procState.Body);
            AssertCmd isBufEmpty = SetAssertCmdForIsBufEmpty(proofState);

            BigBlock atomBB = atom.body.ParentBigBlock;



            if (atom.body.BigBlocks.Count == 2)
            {

                if (atom.body.BigBlocks[0].ec is AtomicStmt &&
                    atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec is CallStmt)
                {
                    CallStmt isAtH = atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec as CallStmt;
                    AtomicStmt isBufEmpAtom = atom.body.BigBlocks[0].ec as AtomicStmt;
                    
                    if (!(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssertCmd)) { Output.AddError("If(*) must include Assertmd"); }
                  //  Debug.Assert(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssertCmd);
                    
                    AssertCmd isBufEmpAssert = isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] as AssertCmd;



                    if (isAtH.cmd.Proc.Name == "isAtHeadAndDrain" && isBufEmpAssert.Expr.Equals(isBufEmpty.Expr))
                    {

                        CodeTransformations.RemoveAt(atom.body, atom.body.BigBlocks.Count - 1);
                        AssumeCmd assumefalse = new AssumeCmd(Token.NoToken, Expr.False);
                        BigBlock asfalse = new BigBlock(Token.NoToken,atom.body.BigBlocks[0].LabelName+"_assume_false" , new CmdSeq(assumefalse),null,null);
                        CodeTransformations.InsertAt(atom.body, asfalse, atom.body.BigBlocks.Count - 1);
                    }

                }

            }

        }
        
        //Added for tSO // proof command 1
        public void EliminateSingleDrainHeadAsm(ProofState proofState, ProcedureState procState, AtomicStmt atom)
        {

            Qoogie.ResolveStmt(procState.Body);
            AssumeCmd isBufEmpty = SetAssumeCmdForIsBufEmpty(proofState);

            BigBlock atomBB = atom.body.ParentBigBlock;
            
            if (atom.body.BigBlocks.Count == 2)
            {

                if (atom.body.BigBlocks[0].ec is AtomicStmt &&
                    atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec is CallStmt)
                {
                    CallStmt isAtH = atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec as CallStmt;
                    AtomicStmt isBufEmpAtom = atom.body.BigBlocks[0].ec as AtomicStmt;
                    if (!(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssumeCmd)) { Output.AddError("If(*) must include AssumeCmd"); }
                   // Debug.Assert(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssumeCmd);
                    
                    AssumeCmd isBufEmpAssert = isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] as AssumeCmd;



                    if (isAtH.cmd.Proc.Name == "drainHead" && isBufEmpAssert.Expr.Equals(isBufEmpty.Expr))
                    {

                        CodeTransformations.RemoveAt(atom.body, atom.body.BigBlocks.Count - 1);
                        AssumeCmd assumefalse = new AssumeCmd(Token.NoToken, Expr.False);
                        BigBlock asfalse = new BigBlock(Token.NoToken, atom.body.BigBlocks[0].LabelName + "_assume_false", new CmdSeq(assumefalse), null, null);
                        CodeTransformations.InsertAt(atom.body, asfalse, atom.body.BigBlocks.Count - 1);
                    }

                }

            }

        }

        
        //Added for tSO // proof command 1
        public void EliminateSingleDrainHead(ProofState proofState, ProcedureState procState, AtomicStmt atom)
        {

            Qoogie.ResolveStmt(procState.Body);
            AssertCmd isBufEmpty = SetAssertCmdForIsBufEmpty(proofState);

            BigBlock atomBB = atom.body.ParentBigBlock;
                                

            if (atom.body.BigBlocks.Count == 2)
            {

                if (atom.body.BigBlocks[0].ec is AtomicStmt &&
                    atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec is CallStmt)
                {
                    CallStmt isAtH = atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec as CallStmt;
                    AtomicStmt isBufEmpAtom = atom.body.BigBlocks[0].ec as AtomicStmt;
                    
                    if (!(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssertCmd)) { Output.AddError("If(*) must include AssertCmd"); }
                  //  Debug.Assert(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssertCmd);
                    
                    AssertCmd isBufEmpAssert = isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] as AssertCmd;


                    if (isAtH.cmd.Proc.Name == "drainHead" && isBufEmpAssert.Expr.Equals( isBufEmpty.Expr))
                    {

                        CodeTransformations.RemoveAt(atom.body, atom.body.BigBlocks.Count - 1);
                       
                    }

                }

            }
                       
        }



        // Ifstar version of elimX

        public void EliminateSingleDrainHeadIf(ProofState proofState, ProcedureState procState, AtomicStmt atom)
        {

            Qoogie.ResolveStmt(procState.Body);
            AssertCmd isBufEmpty = SetAssertCmdForIsBufEmpty(proofState);

            BigBlock atomBB = atom.body.ParentBigBlock;


            if (atom.body.BigBlocks.Count == 2)
            {

                if (atom.body.BigBlocks[0].ec is AtomicStmt &&
                    atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec is IfCmd)
                {
                    IfCmd isAtH = atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec as IfCmd;

                    CallStmt singleDr = isAtH.thn.BigBlocks[0].ec as CallStmt;

                    AtomicStmt isBufEmpAtom = atom.body.BigBlocks[0].ec as AtomicStmt;
                    if (!(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssertCmd)) { Output.AddError("If(*) must include AssertCmd"); }
              //      Debug.Assert(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssertCmd);
                    
                    AssertCmd isBufEmpAssert = isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] as AssertCmd;


                    if ( singleDr.cmd.Proc.Name == "drainHead" && isBufEmpAssert.Expr.Equals(isBufEmpty.Expr))
                    {

                        CodeTransformations.RemoveAt(atom.body, atom.body.BigBlocks.Count - 1);

                    }

                }

            }
        
        }
        public void EliminateSingleDrainHeadAsmIf(ProofState proofState, ProcedureState procState, AtomicStmt atom)
        {
            Qoogie.ResolveStmt(procState.Body);
            AssumeCmd isBufEmpty = SetAssumeCmdForIsBufEmpty(proofState);

            BigBlock atomBB = atom.body.ParentBigBlock;


            if (atom.body.BigBlocks.Count == 2)
            {

                if (atom.body.BigBlocks[0].ec is AtomicStmt &&
                    atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec is IfCmd)
                {
                    IfCmd isAtH = atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec as IfCmd;

                    CallStmt singleDr = isAtH.thn.BigBlocks[0].ec as CallStmt;

                    AtomicStmt isBufEmpAtom = atom.body.BigBlocks[0].ec as AtomicStmt;
                  
                    if (!(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssumeCmd)) { Output.AddError("If(*) must include AssumeCmd"); }
                   // Debug.Assert(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssumeCmd);
                    
                    AssumeCmd isBufEmpAssert = isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] as AssumeCmd;


                    if (singleDr.cmd.Proc.Name == "drainHead" && isBufEmpAssert.Expr.Equals(isBufEmpty.Expr))
                    {

                        CodeTransformations.RemoveAt(atom.body, atom.body.BigBlocks.Count - 1);

                    }

                }

            }


        }
        public void EliminateIsAtHeadAndDrainIf(ProofState proofState, ProcedureState procState, AtomicStmt atom){

            Qoogie.ResolveStmt(procState.Body);
            AssertCmd isBufEmpty = SetAssertCmdForIsBufEmpty(proofState);

            BigBlock atomBB = atom.body.ParentBigBlock;


            if (atom.body.BigBlocks.Count == 2)
            {

                if (atom.body.BigBlocks[0].ec is AtomicStmt &&
                    atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec is IfCmd)
                {
                    IfCmd isAtH = atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec as IfCmd;

                    CallStmt singleDr = isAtH.thn.BigBlocks[0].ec as CallStmt;

                    AtomicStmt isBufEmpAtom = atom.body.BigBlocks[0].ec as AtomicStmt;

                    if (!(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssertCmd)) { Output.AddError("If(*) must include AssertCmd"); }
                   // Debug.Assert(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssertCmd);
                    
                    AssertCmd isBufEmpAssert = isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] as AssertCmd;


                    if (singleDr.cmd.Proc.Name == "isAtHeadAndDrain" && isBufEmpAssert.Expr.Equals(isBufEmpty.Expr))
                    {

                        CodeTransformations.RemoveAt(atom.body, atom.body.BigBlocks.Count - 1);

                    }

                }

            }
        }

        public void EliminateIsAtHeadAndDrainAsmIf(ProofState proofState, ProcedureState procState, AtomicStmt atom)
        {
            Qoogie.ResolveStmt(procState.Body);
            AssumeCmd isBufEmpty = SetAssumeCmdForIsBufEmpty(proofState);

            BigBlock atomBB = atom.body.ParentBigBlock;


            if (atom.body.BigBlocks.Count == 2)
            {

                if (atom.body.BigBlocks[0].ec is AtomicStmt &&
                    atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec is IfCmd)
                {
                    IfCmd isAtH = atom.body.BigBlocks[atom.body.BigBlocks.Count - 1].ec as IfCmd;

                    CallStmt singleDr = isAtH.thn.BigBlocks[0].ec as CallStmt;

                    AtomicStmt isBufEmpAtom = atom.body.BigBlocks[0].ec as AtomicStmt;


                    if (!(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssumeCmd)) { Output.AddError("If(*) must include AssumeCmd"); }
                   // Debug.Assert(isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] is AssumeCmd);

                    
                    AssumeCmd isBufEmpAssert = isBufEmpAtom.body.BigBlocks[0].simpleCmds[0] as AssumeCmd;


                    if (singleDr.cmd.Proc.Name == "isAtHeadAndDrain" && isBufEmpAssert.Expr.Equals(isBufEmpty.Expr))
                    {

                        CodeTransformations.RemoveAt(atom.body, atom.body.BigBlocks.Count - 1);

                    }

                }

            }

        }
        // End If star versions

        //TSO  // while(*){ call drainHead()} <== while(*){assert skip ; call drainHead();}
        public void RemoveSkipAtomic(ProofState proofState)
        {
            foreach (ProcedureState callerProc in callerStmtMap.Keys)
            {
                if (callerProc.Name != "dummy_while")
                {
                    List<CallStmt> callerStmts = callerStmtMap[callerProc];

                    foreach (CallStmt callStmt in callerStmts)
                    {

                        if (callStmt.CalleeName == "drainHead" )
                        {
                            //  int index;
                            StmtList parentStmt = Qoogie.GetParentContext(callStmt);

                            if (parentStmt.BigBlocks.Count >= 2)
                            {

                                
                              if (parentStmt.BigBlocks[0].ec is AtomicStmt && parentStmt.BigBlocks[1].ec is CallStmt)
                                {
                                   
                                    AtomicStmt atm = parentStmt.BigBlocks[0].ec as AtomicStmt;
                                    CallStmt check = parentStmt.BigBlocks[1].ec as CallStmt;
                                    Output.AddLine("atm " + atm.label);
                                    Output.AddLine("cal " + check.label);
                                    
                                        //if (atm.body.BigBlocks.Count == 1)
                                        //{
                                           // AssertCmd asrt = atm.body.BigBlocks[0].simpleCmds[0] as AssertCmd;
                                         //   if (asrt.Expr == Expr.True)
                                       //     {
                                                parentStmt.BigBlocks.RemoveAt(0);
                                                callerProc.MarkAsTransformed();
                                     //       }
                                   //     }
                                  }
                            }
 
                        }
                    }
                }
            }
            
        }
   
        //End TSO
      

        // TSO 
        public void InsertSkipAtomic(ProofState proofState )
        {

            foreach (ProcedureState callerProc in callerStmtMap.Keys)
            {
                if (callerProc.Name != "dummy_while")
                {
                    List<CallStmt> callerStmts = callerStmtMap[callerProc];

                    foreach (CallStmt callStmt in callerStmts)
                    {

                        if (callStmt.CalleeName == "drainHead" )
                        {
                            //  int index;
                            StmtList parentStmt = Qoogie.GetParentContext(callStmt);
                            // Make atomic 
                            AtomicStmt skipAtom = Qoogie.MakeAtomicStmt(new CmdSeq(new AssertCmd(Token.NoToken, Expr.True)), null, null);
                            BigBlock skipBB = new BigBlock(Token.NoToken, skipAtom.label, new CmdSeq(), skipAtom, null);

                            CodeTransformations.InsertAt(parentStmt, skipBB, 0);
                            callerProc.MarkAsTransformed();
                        }
                    }
                }
            }
        }
        
        // Added TSO
        /*public void SwapLeftCheck(ProofState proofState, ProcedureState procState, AtomicStmt atom)
        {

            int index =0;
            Qoogie.ResolveStmt(procState.Body);
            AssertCmd isBufEmpty = SetAssertCmdForIsBufEmpty(proofState);
            StmtList parentStmt = Qoogie.GetParentContext(atom); // While body
            
            StmtList parenparentStmt = atom.body.ParentContext.ParentContext;
            BigBlock parentBB = atom.body.ParentContext.ParentBigBlock; // whileCMd
            
            
            // Get index of the WhileCmd of atom
            for (int i = 0; i< parenparentStmt.BigBlocks.Count; i++) {
                if (parenparentStmt.BigBlocks[i] == parentBB) {

                    index = i;
                    break;
                }
            
            }
            Output.AddLine("Block index of the WhilCmd" + index.ToString());
            


                if (!(parentBB.ec is WhileCmd) )
                {
                    Output.AddError("0.Structure of the StmtList must be assert true; call drainHead");
                    return;
                }
                else
                {


                    if (parentStmt.BigBlocks.Count != 2)
                    {

                        Output.AddError("1.Structure of the StmtList must be assert true; call drainHead");
                        return;
                    }
                    else
                    {
                        if (!(parentStmt.BigBlocks[0].ec is AtomicStmt && parentStmt.BigBlocks[1].ec is CallStmt))
                        {
                            Output.AddError("2.Structure of the StmtList must be assert true; call drainHead");
                            return;
                        }
                        else
                        {

                            parentStmt.BigBlocks.RemoveAt(0);
                            procState.MarkAsTransformed();
                            AssertCmd tosert = new AssertCmd(Token.NoToken, isBufEmpty.Expr);
                            AtomicStmt isBufAtom = Qoogie.MakeAtomicStmt(new CmdSeq(tosert), null, null);

                            BigBlock asfalse = new BigBlock(Token.NoToken, isBufAtom.label, new CmdSeq(), isBufAtom, null);
                            parentStmt.BigBlocks.Insert(0, asfalse);


                            procState.MarkAsTransformed();
                        }


                    }


                }
        }
        
        */



        // Assert isempty // we do the trick putting emoty atomic block first and then remove this atomic skip block
        public void AsserWDIsEmptyBuffer(ProofState proofState, ProcedureState procState, AtomicStmt atom)
        {

            Qoogie.ResolveStmt(procState.Body);
            AssertCmd isBufEmpty = SetAssertCmdForIsBufEmpty(proofState);
            StmtList parentStmt = Qoogie.GetParentContext(atom);

            if (parentStmt.BigBlocks.Count != 2)
            {

                Output.AddError("1.Structure of the StmtList must be assert true; call drainHead");
                return;
            }
            else {
                if(!(parentStmt.BigBlocks[0].ec is AtomicStmt && parentStmt.BigBlocks[1].ec is CallStmt)){
                    Output.AddError("2.Structure of the StmtList must be assert true; call drainHead");
                    return;
                }
                else{
               /*     AtomicStmt skp = parentStmt.BigBlocks[0].ec as AtomicStmt;
                    if (!(skp.body.BigBlocks[0].simpleCmds[0] is AssertCmd))
                    {

                        Output.AddError("3.Structure of the StmtList must be assert true; call drainHead");
                        return;
                    }
                    else { 
                            AssertCmd tr = skp.body.BigBlocks[0].simpleCmds[0] as AssertCmd;
                            if (tr.Expr != Expr.True)
                            {

                                Output.AddError("4.Structure of the StmtList must be assert true; call drainHead");
                                return;
                            }
                            else {*/
                   // String lbl = atom.label;
                    parentStmt.BigBlocks.RemoveAt(0);
                    procState.MarkAsTransformed();
                    AssertCmd tosert = new AssertCmd(Token.NoToken, isBufEmpty.Expr);
                    AtomicStmt isBufAtom = Qoogie.MakeAtomicStmt(new CmdSeq(tosert), null, null);
                        
                    BigBlock asfalse = new BigBlock(Token.NoToken, isBufAtom.label , new CmdSeq(), isBufAtom, null);
                    parentStmt.BigBlocks.Insert(0, asfalse);


                    procState.MarkAsTransformed();
                            }
                    
                    
                    }
                    
                   
                }

    
      
        public void TsoifyBefore(ProofState proofState)
        {
            List<BigBlock> bodyInsert = SetWhileStarBlock(proofState);
            //  Output.AddLine(" BigBlock call  " + toInsert.);

            foreach (ProcedureState callerProc in callerStmtMap.Keys)
            {
                List<CallStmt> callerStmts = callerStmtMap[callerProc];

                foreach (CallStmt callStmt in callerStmts)
                {

                    if (callStmt.CalleeName == "write" || callStmt.CalleeName == "write_to_ptr" || callStmt.CalleeName == "write_heap"
                        || callStmt.CalleeName == "read" || callStmt.CalleeName == "read_from_ptr" || callStmt.CalleeName == "read_heap")
                    {
                        //  int index;
                        StmtList parentStmt = Qoogie.GetParentContext(callStmt);



                        int index = 0;
                        for (int i = 0; i < parentStmt.BigBlocks.Count; i++)
                        {

                            if (parentStmt.BigBlocks[i].ec == callStmt)
                            { index = i; }

                        }


                        // Create call drainHead
                        List<Expr> pipeIn = new List<Expr>();
                        List<IdentifierExpr> pipeOut = new List<IdentifierExpr>();
                        CallCmd dH = new CallCmd(Token.NoToken, "drainHead", pipeIn, pipeOut);
                        AtomicStmt combined = Qoogie.MakeAtomicStmt(new CmdSeq(dH), null, null);
                        BigBlock newbb = new BigBlock(Token.NoToken, combined.label, new CmdSeq(), combined, null);

                        WhileCmd oldold = bodyInsert[0].ec as WhileCmd;
                        List<PredicateCmd> cmds = new List<PredicateCmd>();

                        WhileCmd newWhile = new WhileCmd(Token.NoToken, oldold.Guard, cmds, Qoogie.DuplicateStatement(new StmtList(bodyInsert, Token.NoToken)));


                        Output.AddLine(" NewWhile'in Call statement'i " + newWhile.Body.BigBlocks[0].LabelName);
                        newWhile.Body.BigBlocks.RemoveAt(0);
                        newWhile.Body.BigBlocks.Add(newbb);
                        Output.AddLine(" NewWhile'in Body'sinin Count'u " + newWhile.Body.BigBlocks.Count.ToString());

                        //    newWhile.Body.BigBlocks.Add(newbb);

                        BigBlock nwBB = new BigBlock(Token.NoToken, null, new CmdSeq(), newWhile, null);


                        CodeTransformations.InsertBefore(parentStmt.BigBlocks[index], nwBB);
                        //    parentStmt.BigBlocks.Insert(index, nwBB);
                        callerProc.MarkAsTransformed();



                    }
                }
            }
        }

        public void TsoifyBefore_old(ProofState proofState)
        {
            List<BigBlock> bodyInsert = SetWhileStarBlock(proofState);
            //  Output.AddLine(" BigBlock call  " + toInsert.);

            foreach (ProcedureState callerProc in callerStmtMap.Keys)
            {
                List<CallStmt> callerStmts = callerStmtMap[callerProc];

                foreach (CallStmt callStmt in callerStmts)
                {

                    if (callStmt.CalleeName == "write" || callStmt.CalleeName == "write_to_ptr" || callStmt.CalleeName == "write_heap"
                        || callStmt.CalleeName == "read" || callStmt.CalleeName == "read_from_ptr" || callStmt.CalleeName == "read_heap")
                    {
                        //  int index;
                        StmtList parentStmt = Qoogie.GetParentContext(callStmt);
                        for (int i = 0; i < parentStmt.BigBlocks.Count; i++)
                        {

                            if (parentStmt.BigBlocks[i].ec == callStmt)
                            {
                                //                   StmtVisitor vstr = new StmtVisitor();

                                // Create call drainHead
                                List<Expr> pipeIn = new List<Expr>();
                                List<IdentifierExpr> pipeOut = new List<IdentifierExpr>();
                                CallCmd dH = new CallCmd(Token.NoToken, "drainHead", pipeIn, pipeOut);
                                AtomicStmt combined = Qoogie.MakeAtomicStmt(new CmdSeq(dH), null, null);
                                BigBlock newbb = new BigBlock(Token.NoToken, combined.label, new CmdSeq(), combined, null);

                                WhileCmd oldold = bodyInsert[0].ec as WhileCmd;
                                List<PredicateCmd> cmds = new List<PredicateCmd>();

                                WhileCmd newWhile = new WhileCmd(Token.NoToken, oldold.Guard, cmds, Qoogie.DuplicateStatement(new StmtList(bodyInsert, Token.NoToken)));


                                Output.AddLine(" NewWhile'in Call statement'i " + newWhile.Body.BigBlocks[0].LabelName);
                                newWhile.Body.BigBlocks.RemoveAt(0);
                                newWhile.Body.BigBlocks.Add(newbb);
                                Output.AddLine(" NewWhile'in Body'sinin Count'u " + newWhile.Body.BigBlocks.Count.ToString());

                                //    newWhile.Body.BigBlocks.Add(newbb);

                                BigBlock nwBB = new BigBlock(Token.NoToken, null, new CmdSeq(), newWhile, null);


                                //CodeTransformations.InsertBefore(parentStmt.BigBlocks[i], nwBB);
                                parentStmt.BigBlocks.Insert(i, nwBB);
                                callerProc.MarkAsTransformed();



                            }
                        }

                    }
                }
            }
        }

        public void TsoifyAfter(ProofState proofState)
        {

            List<BigBlock> bodyInsert = SetWhileStarBlock(proofState);
            //  Output.AddLine(" BigBlock call  " + toInsert.);

            foreach (ProcedureState callerProc in callerStmtMap.Keys)
            {
                List<CallStmt> callerStmts = callerStmtMap[callerProc];

                foreach (CallStmt callStmt in callerStmts)
                {

                    if (callStmt.CalleeName == "write" || callStmt.CalleeName == "write_to_ptr" || callStmt.CalleeName == "write_heap"
                        || callStmt.CalleeName == "read" || callStmt.CalleeName == "read_from_ptr" || callStmt.CalleeName == "read_heap")
                    {
                        //  int index;
                        StmtList parentStmt = Qoogie.GetParentContext(callStmt);
                        for (int i = 0; i < parentStmt.BigBlocks.Count; i++)
                        {

                            if (parentStmt.BigBlocks[i].ec == callStmt)
                            {
                                StmtVisitor vstr = new StmtVisitor();

                                // Create call drainHead
                                List<Expr> pipeIn = new List<Expr>();
                                List<IdentifierExpr> pipeOut = new List<IdentifierExpr>();
                                CallCmd dH = new CallCmd(Token.NoToken, "drainHead", pipeIn, pipeOut);
                                AtomicStmt combined = Qoogie.MakeAtomicStmt(new CmdSeq(dH), null, null);
                                BigBlock newbb = new BigBlock(Token.NoToken, combined.label, new CmdSeq(), combined, null);

                                WhileCmd oldold = bodyInsert[0].ec as WhileCmd;
                                List<PredicateCmd> cmds = new List<PredicateCmd>();

                                WhileCmd newWhile = new WhileCmd(Token.NoToken, oldold.Guard, cmds, Qoogie.DuplicateStatement(new StmtList(bodyInsert, Token.NoToken)));


                                //     Output.AddLine(" NewWhile'in Call statement'i " + newWhile.Body.BigBlocks[0].LabelName);
                                newWhile.Body.BigBlocks.RemoveAt(0);
                                newWhile.Body.BigBlocks.Add(newbb);
                                //      Output.AddLine(" NewWhile'in Body'sinin Count'u " + newWhile.Body.BigBlocks.Count.ToString());

                                //    newWhile.Body.BigBlocks.Add(newbb);

                                BigBlock nwBB = new BigBlock(Token.NoToken, null, new CmdSeq(), newWhile, null);


                                CodeTransformations.InsertAt(parentStmt, nwBB, i + 1);
                                callerProc.MarkAsTransformed();



                            }
                        }

                    }
                }
            }


        }




        // End
        public void Reduce(ProofState proofState)
        {
            if (IsReduced) return;

            ComputeAtomicBlocks();

            // sanity checks
            Debug.Assert(this.isAtomic);

            //-------------------------------------
            // first reduce the called ones
            List<ProcedureState> callees = proofState.callGraph.CollectCallees(this);
            foreach (ProcedureState callee in callees)
            {
                // string name = this.Name + " " + callee.Name;
                callee.ComputeAtomicBlocks();
                Debug.Assert(callee.IsAtomic && !callee.IsReduced);
                callee.Reduce(proofState);
            }

            //-------------------------------------
            // now reduce it

            // inline the body
            // replace call blocks with normal spec
            foreach (ProcedureState callerProc in callerStmtMap.Keys)
            {
                callerProc.ComputeAtomicBlocks();

                List<CallStmt> callerStmts = callerStmtMap[callerProc];
                foreach (CallStmt callStmt in callerStmts)
                {
                    // inline body at the call site
                    CodeTransformations.Inline(callerProc, callStmt, this);
                }
            }
            callerStmtMap.Clear();

            //-------------------------------------
            // if not public then remove this
            if (!this.IsPublic)
            {
                proofState.RemoveProcedureState(this);
            }

            proofState.UpdateCallGraph();

            this.IsReduced = true;

            //------------------
            // no need for pc variable any more
            // TODO: in fact we need it while computing the transition predicates, solve this problem
            //RemoveLocalVar(pcExpr.Decl);

            //List<AtomicBlock> oldBlocks = new List<AtomicBlock>(this.atomicBlocks);
            //foreach(AtomicBlock oldBlock in oldBlocks) {
            //    RemoveAtomicBlock(oldBlock);
            //}

            //// add the spec block

            //Debug.Assert(this.atomicBlocks.Count == 0);

            //Block specblock = new Block(Token.NoToken, "spec", new CmdSeq(this.Spec), new ReturnCmd(Token.NoToken));

            //AtomicBlock specBlock = new AtomicBlock(this, specblock);
            //AddAtomicBlock(specBlock);
        }

        private void InitPc()
        {

            Debug.Assert(ProofState.GetInstance().exceptionType != null);

            // once this is called, all local variables have been set
            Variable pcVar;
            if (!this.localVars.ContainsKey("pc"))
            {
                pcVar = CreateFreshLocalVar("pc", ProofState.GetInstance().exceptionType, false);
            }
            else
            {
                pcVar = GetLocalVar("pc");
                Debug.Assert(pcVar != null && pcVar.TypedIdent.Type.AsCtor.Decl.Name == ProofState.GetInstance().exceptionType.AsCtor.Decl.Name);
            }
            this.pcExpr = new IdentifierExpr(Token.NoToken, pcVar);
        }

        private void InitEx()
        {

            Debug.Assert(ProofState.GetInstance().exceptionType != null);

            // once this is called, all local variables have been set
            Variable exVar;
            if (!this.localVars.ContainsKey("ex"))
            {
                exVar = CreateFreshLocalVar("ex", ProofState.GetInstance().exceptionType, true);
            }
            else
            {
                exVar = GetLocalVar("ex");
                Debug.Assert(exVar != null && exVar.TypedIdent.Type.AsCtor.Decl.Name == ProofState.GetInstance().exceptionType.AsCtor.Decl.Name);
            }
            this.exExpr = new IdentifierExpr(Token.NoToken, exVar);
        }


        //private void InitEntryBlock(Implementation impl) {

        //    CmdSeq newCmds = new CmdSeq();
        //    Block block = new Block(Token.NoToken, "EnterBlock", newCmds,
        //                             new GotoCmd(Token.NoToken, new BlockSeq(impl.Blocks[0])));

        //    impl.Blocks.Insert(0, block);

        //    this.entryBlock = block;
        //}

        //public void AddAtomicStmt(AtomicStmt newbody) {

        //    aplStmtMap.Add(newbody.label, newbody);

        //    //ProofState.GetInstance().AddAtomicStmt(atomicBlock);

        //    //this.atomicBlocks.Add(atomicBlock);

        //    // add blocks to the procedure itself
        //    //foreach (Block block in atomicBlock.blocks)
        //    //{
        //    //    if (!impl.Blocks.Contains(block))
        //    //    {
        //    //        impl.Blocks.Add(block);
        //    //    }
        //    //}

        //    // TODO: we disable clonability of xheaders here, do it elsewhere
        //    // this is for keeping loopinfo.xheader fixed
        //    //foreach(LoopInfo loopInfo in loopInfoMap.Values) {
        //    //    if(atomicBlock.Contains(loopInfo.XHeader)) {
        //    //        atomicBlock.IsClonable = false;
        //    //        break;
        //    //    }
        //    //}
        //}

        //public void RemoveAtomicStmt(AtomicStmt newbody) {

        //    aplStmtMap.Remove(newbody.label);

        //    //ProofState.GetInstance().RemoveAtomicBlock(atomicBlock);

        //    //this.atomicBlocks.Remove(atomicBlock);

        //    //// update the procedure itself
        //    //foreach (Block block in atomicBlock.blocks)
        //    //{
        //    //    impl.Blocks.Remove(block);
        //    //}

        //}

        public APLBlock LookupAPLBlockStarts(Block block)
        {
            foreach (APLBlock atomicBlock in aplBlockMap.Values)
            {
                if (atomicBlock.startBlock.Label == block.Label)
                {
                    return atomicBlock;
                }
            }
            Debug.Assert(false);
            return null;
        }

        public APLBlock LookupAPLBlockContains(Block block)
        {
            foreach (APLBlock atomicBlock in aplBlockMap.Values)
            {
                if (atomicBlock.Contains(block))
                {
                    return atomicBlock;
                }
            }
            Debug.Assert(false);
            return null;
        }

        public void RecomputeBlockPredecessors()
        {
            // compute predecessors
            foreach (Block b in impl.Blocks)
            {
                b.Predecessors = new BlockSeq();
            }

            foreach (Block b in impl.Blocks)
            {
                GotoCmd gtc = b.TransferCmd as GotoCmd;
                if (gtc != null)
                {
                    foreach (Block dest in gtc.labelTargets)
                    {
                        dest.Predecessors.Add(b);
                    }
                }
            }
        }

        //public void PostProcess(Program program) {
        //    RecomputeBlockPredecessors();
        //}

        //private void ComputeAtomicBlocks(Block block, List<Block> newblocks) {

        //    if(newblocks.Contains(block)) return;

        //    //--------------------------------------------

        //    // TODO: what if the loop header accesses more than one global variables ?
        //    // if loop header, do not split
        //    if(loopInfoMap.ContainsKey(block)) {

        //        LoopInfo loopInfo = loopInfoMap[block]; 

        //        LoopBlock loopBlock = new LoopBlock(this, loopInfo);

        //        newblocks.Add(loopInfo.Header);
        //        //newblocks.Add(loopInfo.YHeader);

        //        AddAtomicBlock(loopBlock);

        //        return;
        //    }

        //    //--------------------------------------------

        //    // decompose the block to ground actions
        //    CmdSeq cmds = new CmdSeq();
        //    int i = 0;
        //    for(int n = block.Cmds.Length; i < n; ++i) {
        //        cmds.AddRange(DecomposeToGroundCmds(block.Cmds[i]));
        //    }

        //    //--------------------------------------------

        //    TransferCmd newtransferCmd;
        //    Block newblock;
        //    CmdSeq newcmds;
        //    string newlabel = block.Label;
        //    TransferCmd transferCmd = block.TransferCmd;		
        //    AtomicBlock atomicBlock;

        //    // then create atomic blocks
        //    int counter = 0;
        //    i = 0;
        //    newcmds = new CmdSeq();
        //    do {
        //        if (counter > 0) {
        //            newlabel = block.Label + "@" + counter.ToString();
        //        }			

        //        Cmd cmd = null;
        //        int numGlobalAccesses = 0;
        //        while(i < cmds.Length) {
        //            cmd = cmds[i];
        //            numGlobalAccesses += CodeAnalyses.NumGlobalAccesses(cmd);
        //            if(numGlobalAccesses <= 1 || newcmds.Length == 0) {
        //                newcmds.Add(cmd);
        //                i++;
        //                if(cmd is CallCmd || (i < cmds.Length && cmds[i] is CallCmd)) {
        //                    break;
        //                }
        //            } else {
        //                Debug.Assert(newcmds.Length > 0);
        //                break;
        //            }
        //        }

        //        if (i == cmds.Length) {
        //            // last (or no) command
        //            GotoCmd gotoCmd = transferCmd as GotoCmd;
        //            if(gotoCmd == null) {
        //                newtransferCmd = new ReturnCmd(Token.NoToken);
        //            } else {
        //                newtransferCmd = new GotoCmd(Token.NoToken, gotoCmd.labelNames);
        //            }
        //        } else {
        //            // not last command
        //            newtransferCmd = new GotoCmd(Token.NoToken, new StringSeq(block.Label + "@" + (counter+1).ToString()));
        //        }

        //        if(counter == 0) {
        //            block.Cmds = newcmds;
        //            block.TransferCmd = newtransferCmd;
        //            newblock = block;
        //        } else {
        //            newblock = new Block(block.tok, newlabel, newcmds, newtransferCmd);
        //        }
        //        ++counter;

        //        newblocks.Add(newblock);

        //        Debug.Assert(newcmds.Length == 0 || cmd != null);

        //        if((newcmds.Length > 0) && // for handling empty blocks 
        //           (cmd is CallCmd)) {
        //            // constructor of CallBlock also registers the block to the callee procedure
        //            atomicBlock = new CallBlock(this, newblock, cmd as CallCmd);
        //        } else {
        //            atomicBlock = new AtomicBlock(this, newblock);
        //        }

        //        AddAtomicBlock(atomicBlock);

        //        newcmds = new CmdSeq(); // for now each atomic block has one command

        //    } while(i < cmds.Length); 

        //}

        // given a single command, returns a sequence of new commands
        // if cmd has only one access to a global variable, new sequence contains the given cmd as is
        // otherwise, new commands are created that do the same job as cmd does
        private CmdSeq DecomposeToGroundCmds(Cmd cmd)
        {
            CmdSeq newCmds = new CmdSeq();

            Set readSet = CodeAnalyses.ComputeGlobalReads(cmd);

            if (readSet.Count <= 1)
            {
                newCmds.Add(cmd);
            }
            else
            {
                Hashtable map = new Hashtable();
                foreach (GlobalVariable gvar in readSet)
                {
                    Variable fvar = CreateFreshLocalVar(gvar.TypedIdent.Type);

                    map.Add(gvar, new IdentifierExpr(Token.NoToken, fvar));

                    newCmds.Add(AssignCmd.SimpleAssign(Token.NoToken, new IdentifierExpr(Token.NoToken, fvar), new IdentifierExpr(Token.NoToken, gvar)));
                }

                cmd = CodeAnalyses.SubstituteReads(cmd, map);

                newCmds.Add(cmd);
            }

            return newCmds;
        }

        //private void ComputeLoops() {
        //    RecomputeBlockPredecessors();

        //    this.loopInfoMap = Loops.PreProcessLoops(this, ProofState.GetInstance().program);
        //}

        public Expr MapExprToCallSite(Expr expr, ProcedureState caller, CallCmd callCmd)
        {
            Hashtable map = new Hashtable();

            // inputs
            for (int j = 0, n = impl.InParams.Length; j < n; ++j)
            {
                map[impl.InParams[j]] = callCmd.Ins[j];
            }

            // outputs
            for (int j = 0, n = impl.OutParams.Length; j < n; ++j)
            {
                map[impl.OutParams[j]] = callCmd.Outs[j];
            }

            return Logic.Substitute(map, MapExprFromProcToImpl(expr));
        }

        public Expr RelyForLocals
        {
            get
            {
                Expr rely = Expr.True;
                foreach (Variable lvar in localVars.Values)
                {
                    IdentifierExpr iexpr = new IdentifierExpr(Token.NoToken, lvar);
                    Expr primeexp = this.GetPrimedExpr(lvar);
                    rely = Expr.And(rely, Expr.Eq(primeexp, iexpr));
                }
                return rely;
            }
        }

        public Expr LocalInvariant
        {
            get
            {
                Expr inv = Expr.True;
                foreach (Expr f in localinvs)
                {
                    inv = Expr.And(inv, f);
                }
                return inv;
            }
        }

        public void AddRequires(Expr expr)
        {
            impl.Proc.Requires.Add(new Requires(false, expr));
        }

        public void AddEnsures(Expr expr)
        {
            impl.Proc.Ensures.Add(new Ensures(false, expr));
        }

        public void AddModifies(Variable var)
        {
            impl.Proc.Modifies.Add(new IdentifierExpr(Token.NoToken, var));
            modifiesMap.Add(var, null);
        }

        public void CheckAddModifies(Variable var, bool recurse)
        {
            if (var is GlobalVariable && !this.modifiesMap.ContainsKey(var))
            {
                impl.Proc.Modifies.Add(new IdentifierExpr(Token.NoToken, var));
                modifiesMap.Add(var, null);

                if (recurse)
                {
                    List<ProcedureState> callers = ProofState.GetInstance().callGraph.CollectCallers(this);
                    foreach (ProcedureState caller in callers)
                    {
                        caller.CheckAddModifies(var, false);
                    }
                }
            }
        }

        public Expr Pre
        {
            get
            {
                return this.Requires;
            }
        }

        // with prime, without old(.)
        public Expr Post
        {
            get
            {
                return Logic.ConvertFromOldToPrime(this, this.Ensures);
            }
        }

        public Expr RequiresAtCall(ProcedureState caller, CallCmd callCmd)
        {
            return MapExprToCallSite(this.Pre, caller, callCmd);
        }

        public Expr EnsuresAtCall(ProcedureState caller, CallCmd callCmd)
        {
            return MapExprToCallSite(this.Post, caller, callCmd);
        }

        public Expr Requires
        {
            get
            {
                Expr pre = Expr.True;
                foreach (Requires req in impl.Proc.Requires)
                {
                    if (!req.Free)
                    {
                        pre = Expr.And(pre, req.Condition);
                    }
                }
                return MapExprFromProcToImpl(pre);
            }
        }

        public Expr Ensures
        {
            get
            {
                Expr post = Expr.True;

                foreach (Ensures ens in impl.Proc.Ensures)
                {
                    if (!ens.Free)
                    {
                        post = Expr.And(post, ens.Condition);
                    }
                }

                return MapExprFromProcToImpl(post);
            }
        }

        public ResolutionContext GetResolutionContext(bool twostate)
        {
            ResolutionContext rc = ProofState.GetInstance().GetResolutionContext(twostate);

            foreach (Declaration d in this.localVars.Values)
            {
                d.Register(rc);
            }

            // add primes as well
            foreach (Declaration d in this.primes)
            {
                d.Register(rc);
            }

            return rc;

        }

        public TypecheckingContext GetTypecheckingContext()
        {

            TypecheckingContext tc = ProofState.GetInstance().GetTypecheckingContext();
            tc.Frame = impl.Proc.Modifies;

            foreach (Declaration d in this.localVars.Values)
            {
                d.Typecheck(tc);
            }

            // type check primes as well
            foreach (Declaration d in this.primes)
            {
                d.Typecheck(tc);
            }

            return tc;
        }

        public bool ResolveTypeCheckExpr(Expr expr, bool twostate)
        {
            BoogiePL.Errors.count = 0;

            expr.Resolve(GetResolutionContext(twostate));

            expr.Typecheck(GetTypecheckingContext());

            return BoogiePL.Errors.count == 0;
        }

        public bool ResolveTypeCheckVar(Variable var)
        {
            BoogiePL.Errors.count = 0;

            var.Resolve(GetResolutionContext(false));

            var.Typecheck(GetTypecheckingContext());

            return BoogiePL.Errors.count == 0;
        }


        public Set<Expr> ComputeMapIndices(Variable map)
        {
            return (new MyMapIndiceFinder(map)).DoFindIndices(this.impl);
        }


        public MoverType ComputeBodyMover()
        {
            return InitialAPLBlock.ComputeComposedMover();
        }

        public myGraph GraphView
        {
            get
            {
                ComputeAtomicBlocks();

                myGraph g = new myGraph(impl.Name);

                foreach (APLBlock aplBlock in aplBlockMap.Values)
                {
                    myNode node = aplBlock.GraphView;
                    g.Add(node);
                }

                // myNode snode = new myNode(impl.Name, "Procedure " + impl.Name, myColor.Green, myColor.Black, myColor.Blue, myShape.Box);
                // AtomicBlock! startBlock = LookupAtomicBlockStarts(this.precondBlock);
                // snode.Edges.Add(startBlock.UniqueLabel);
                // g.Add(snode);

                return g;
            }
        }

        public string DotView
        {
            get
            {
                StringWriter strw = new StringWriter();
                strw.Write("digraph "); strw.Write(impl.Name); strw.WriteLine(" { ");

                foreach (APLBlock aplBlock in aplBlockMap.Values)
                {
                    strw.WriteLine(aplBlock.DotView);
                    foreach (APLBlock successor in aplBlock.Successors)
                    {
                        strw.Write(aplBlock.Label);
                        strw.Write(" -> ");
                        strw.Write(successor.Label);
                        strw.WriteLine(";");
                    }
                }

                strw.WriteLine(" } ");
                return strw.ToString();
            }
        }

        internal AtomicStmt GetAtomicBody()
        {
            List<AtomicBlock> atomicBlocks = this.AtomicBlocks;

            Debug.Assert(atomicBlocks.Count == 1);

            return atomicBlocks[0].parent;
        }

        internal AtomicBlock GetAtomicBlock(string atomname)
        {
            Debug.Assert(!this.hasTransformed);

            if (!aplBlockMap.ContainsKey(atomname)) return null;
            return aplBlockMap[atomname] as AtomicBlock;
        }

        //internal AtomicStmt GetAtomicStmt(string atomname)
        //{
        //    if (!aplStmtMap.ContainsKey(atomname)) return null;
        //    return aplStmtMap[atomname] as AtomicStmt;
        //}

        public void AddAuxVar(LocalVariable var)
        {
            if (!impl.LocVars.Has(var))
            {
                impl.LocVars.Add(var);
            }

            AddLocalVar(var, true);
            MakeAuxVar(var);

            Qoogie.AddQKeyValue(var, "isaux");
        }

        public void MakeAuxVar(LocalVariable var)
        {
            Debug.Assert(this.localVars[var.Name] == var);
            auxVars.Add(var.Name, var);
        }

        public void MakeNonAuxVar(LocalVariable var)
        {
            Debug.Assert(this.auxVars[var.Name] == var);
            Debug.Assert(this.localVars[var.Name] == var);
            auxVars.Remove(var.Name);

            // remove the QKeyValue
            Qoogie.RemoveQKeyValue(var, "isaux");
        }

        public bool IsAuxVar(Variable var)
        {
            return auxVars.ContainsKey(var.Name);
        }

        public bool IsHiddenVar(Variable var)
        {
            return hiddenVars.ContainsKey(var.Name);
        }

        public void HideVar(LocalVariable var)
        {
            Debug.Assert(this.localVars[var.Name] == var);
            hiddenVars.Add(var.Name, var);

            Qoogie.AddQKeyValue(var, "ishidden");
        }

        /// <summary>
        /// Returns the hidden variables of this procedure
        /// </summary>
        public VariableSeq HiddenVars
        {
            get
            {
                VariableSeq vseq = new VariableSeq();
                foreach (Variable var in hiddenVars.Values)
                {
                    vseq.Add(var);
                }
                return vseq;
            }
        }

        public VariableSeq PrimedHiddenVars
        {
            get
            {
                VariableSeq vseq = new VariableSeq();
                foreach (Variable var in hiddenVars.Values)
                {
                    vseq.Add(GetPrimedVar(var));
                }
                return vseq;
            }
        }

        public Set<Variable> PrivateLocalVars
        {
            get
            {
                Set<Variable> vars = new Set<Variable>();
                foreach (Variable var in this.impl.LocVars)
                {
                    vars.Add(var);
                }
                return vars;
            }
        }

    }


} // end namespace QED