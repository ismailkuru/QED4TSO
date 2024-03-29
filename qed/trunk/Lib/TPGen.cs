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
using Microsoft.Basetypes;


    public class MultipleHavocException : Exception
    {
        public Variable hVar;

        public MultipleHavocException(Variable var)
            : base("Multiple havoc for variable: " + var.Name)
        {
            this.hVar = var;
        }
    }

    public class TPGenOptions
    {
        public Dictionary<Variable, int> incarIdMap;
        public bool useQuant;
        public bool computeWP;
        public bool computeRW;
        public Set<Variable> readSet;
        public Set<Variable> writeSet;
        public Expr postCondForWP;
        public bool unifyHavocs;
        public bool singleHavoc;
        public Set<Variable> singleHavocExcepts;
        
        public TPGenOptions(bool wp, bool rw, Expr pc)
        {
            this.useQuant = true;
            this.computeWP = wp;
            this.computeRW = rw;
            this.postCondForWP = pc;
            this.unifyHavocs = false;
            this.singleHavoc = !wp; // default handling of havocs
            this.singleHavocExcepts = new Set<Variable>();
            
            this.incarIdMap = new Dictionary<Variable, int>();

            if (computeRW)
            {
                this.readSet = new Set<Variable>();
                this.writeSet = new Set<Variable>();
            }
        }

       
        static public TPGenOptions ComputeRWSets
        {
            get
            {
                return new TPGenOptions(false, true, null);
            }
        }

        static public TPGenOptions ComputeTPred
        {
            get
            {
                return new TPGenOptions(false, false, null);
            }
        }

        //static public TPGenOptions ComputeTPredWoutQuant
        //{
        //    get
        //    {
        //        TPGenOptions options = new TPGenOptions(false, false, null);
        //        options.useQuant = false;
        //        return options;
        //    }
        //}

        static public TPGenOptions ComputeWPre(Expr postCond)
        {
           return new TPGenOptions(true, false, postCond);
        }

        //static public TPGenOptions ComputeWPreWoutQuant(Expr postCond)
        //{
        //    return new TPGenOptions(false, true, false, postCond);
        //}


        internal bool SanityCheck()
        {
            Debug.Assert(!this.useQuant || !this.unifyHavocs);
            Debug.Assert(!this.singleHavoc || !this.computeWP);
            return true;
        }
    }

public class TPGenerator {

    protected TPGenOptions options;

    protected APLBlock atomicBlock;

    public Set<Variable> deadLocals;
	
	protected ProcedureState procState;
	
	protected TPGenerator nextTPGen;

    protected bool hideLocals;

    public bool compactForm;

    // make asserts assume for right mover checks
    public bool assumeAsserts = false;

    // make returns assume false for right mover checks
    public bool suppressReturns = false;

    protected Dictionary<Cmd, List<Variable>> havoc2Incarnation; // map from CallCmd/HavocCmd to incarnation variable

    public void ResetUnifiedHavocs()
    {
        this.havoc2Incarnation = new Dictionary<Cmd, List<Variable>>();
    }

    public TPGenerator Next {
		get {
			return nextTPGen;
		}
		set {
			nextTPGen = value;	
		}
	}
    public APLBlock APLBlock
    {
        get
        {
            return this.atomicBlock;
        }
    }

	
	public Set<Variable> ReadSet {
		get {
            Debug.Assert(options.computeRW);
			return options.readSet;
		}
	}
	
	public Set<Variable> WriteSet {
		get {
            Debug.Assert(options.computeRW);
			return options.writeSet;
		}
	}
	
	protected void AddToWriteSet(Variable var) {
        if (options.computeRW)
        {
            options.writeSet.Add(var);
        }
	}

    protected void UpdateReadSet(Expr expr, Set<Variable> intermSet)
    {
        Set readvars = new Set();
        expr.ComputeFreeVariables(readvars);
        //Output.AddLine("expr: " + expr.ToString());
        foreach (object var in readvars)
        {
            if (var is Variable)
            {
                intermSet.Add(var as Variable);
                if (options.computeRW)
                {
                    options.readSet.Add(var as Variable);
                }
            }
        }
	}

    public TPGenerator(ProcedureState procState, Cmd cmd, bool hide)
        : this(procState, new CmdSeq(cmd), hide)
    {
    }

    public TPGenerator(ProcedureState procState, Cmd cmd, TPGenerator next, bool hide)
        : this(procState, new CmdSeq(cmd), next, hide)
    {
    }

    public TPGenerator(ProcedureState procState, Cmd cmd)
        : this(procState, new CmdSeq(cmd), false)
    {
    }

    public TPGenerator(ProcedureState procState, Cmd cmd, TPGenerator next)
        : this(procState, new CmdSeq(cmd), next, false)
    {
    }

    public TPGenerator(ProcedureState procState, CmdSeq cmdSeq, bool hide)
        : this(CmdBlock.Create(procState, cmdSeq), null, hide, false)
    {
    }

    public TPGenerator(ProcedureState procState, CmdSeq cmdSeq, TPGenerator next, bool hide)
        : this(CmdBlock.Create(procState, cmdSeq), next, hide, false)
    {
    }
	
	public TPGenerator (APLBlock block)
        : this(block, null, false, false)
    {
    }

    public TPGenerator(APLBlock block, bool hide)
        : this(block, null, hide, false)
    {
    }

    public TPGenerator(APLBlock block, bool hide, bool compact)
        : this(block, null, hide, compact)
    {
    }

    public TPGenerator(APLBlock block, TPGenerator next)
        : this(block, next, false, false)
    {
    }

    public TPGenerator(APLBlock block, TPGenerator next, bool hide)
        : this(block, next, hide, false)
    {
    }

    public TPGenerator(APLBlock block, TPGenerator next, bool hide, bool compact)
    {
		this.atomicBlock = block;
        this.procState = block.procState;
		this.nextTPGen = next;
        this.hideLocals = hide;
        this.compactForm = compact;
        this.assumeAsserts = false;
        ResetUnifiedHavocs();
    }
    
    virtual public Expr Compute(TPGenOptions opts) {
        return Compute(opts, new Hashtable(), new Set<Variable>());
    }

    virtual public Expr Compute(TPGenOptions opts, Hashtable incarnationMap, Set<Variable> intermSet)
    {
        this.options = opts;
        return DoCompute(incarnationMap, intermSet);
    }
	
	protected Expr ReadMap(Hashtable incarnationMap, Variable key) {
		Debug.Assert(incarnationMap != null);
		
		object val = null;
		
		val = incarnationMap[key];
		
		if(val != null) return (Expr) val;
		
		return new IdentifierExpr(Token.NoToken, key);
	}

    protected Expr CallNextTPGen(Block nextBlock, Hashtable incarnationMap, Set<Variable> intermSet, TransferCmd tc)
    {
        // assign next pc
        //if (!options.computeWP && (this.hideLocals == nextTPGen.hideLocals))
        //{
        //    incarnationMap[CheckHideVar(procState.pcExpr).Decl] = GetNextPc(nextBlock);
        //}
                
        Expr pred = nextTPGen.Compute(this.options, incarnationMap, intermSet);

        if (!options.computeWP && (this.hideLocals != nextTPGen.hideLocals))
        {
            Expr primespred = ComputePrimesPredicateLocal(incarnationMap, tc);
            pred = Expr.And(primespred, pred);
        }

        return pred;
	}

    //protected Expr GetNextPc(TransferCmd tc)
    //{
    //    //---------------------------------
    //    // handle pc expression here
    //    Expr nextPc = null;
    //    if (tc is ThrowCmd)
    //    {
    //        ThrowCmd thrw = tc as ThrowCmd;
    //        nextPc = thrw.ex;
    //    }
    //    else if (tc is ReturnCmd)
    //    {
    //        nextPc = ProofState.GetInstance().exReturnExpr;
    //    }
    //    else if (tc is GotoCmd)
    //    {
    //        //APLBlock successor = procState.LookupAPLBlockStarts(nextBlock);
    //        //nextPc = LiteralExpr.Literal(successor.Pc);
    //        nextPc = ProofState.GetInstance().exSkipExpr;
    //    }
    //    Debug.Assert(nextPc != null);

    //    return nextPc;
    //}

    virtual protected Expr DoCompute(Hashtable incarnationMap, Set<Variable> intermSet)
    {
        // sanity checks
        Debug.Assert(this.options != null && this.options.SanityCheck());

		//Expr pce = AssumePc(incarnationMap);
		Expr pred = ComputeForBlock(0, this.atomicBlock.startBlock, incarnationMap, intermSet);

        //return options.computeWP ? pred : Expr.And(pce, pred);
        return pred;
    }

    //private Expr AssumePc(Hashtable incarnationMap)
    //{
    //    return Logic.Substitute(incarnationMap, Expr.Eq(CheckHide(procState.pcExpr), ProofState.GetInstance().exSkipExpr));
    //}

    virtual protected Expr ComputeForBlock(int i, Block block, Hashtable incarnationMap, Set<Variable> intermSet)
    {
		Expr predicate = null;
		
		CmdSeq cmds = block.Cmds;

        if (i >= block.Cmds.Length)
        {
            TransferCmd tc = block.TransferCmd;

            BlockSeq gotoBlocks = new BlockSeq();
            if (tc is ThrowCmd)
            {
                ThrowCmd thrw = tc as ThrowCmd;
                if (thrw.catchStmt != null)
                {
                    Debug.Assert(thrw.catchStmt.GotoBlock != null);
                    gotoBlocks.Add(thrw.catchStmt.GotoBlock);
                }
            }
            else if (tc is GotoCmd)
            {
                GotoCmd gotoCmd = tc as GotoCmd;
                gotoBlocks.AddRange(gotoCmd.labelTargets);
            }
            else if (tc is ReturnCmd && suppressReturns)
            {
                if (this.Next != null && !options.computeWP)
                {
                    return Expr.False;
                }
                //else if (this.Next == null && options.computeWP)
                //{
                //    return Expr.False;
                //}
            }

            if (gotoBlocks.Length > 0)
            {
                foreach (Block nextBlock in gotoBlocks)
                {
                    Hashtable localIncarnationMap = incarnationMap.Clone() as Hashtable;
                    Set<Variable> localIntermSet = new Set<Variable>(intermSet);
                    
                    Expr pred;
                    if (this.atomicBlock.Contains(nextBlock))
                    {
                        pred = ComputeForBlock(0, nextBlock, localIncarnationMap, localIntermSet);
                    }
                    else
                    {
                        //---------------------
                        // find out if the goto block belongs to the next one
                        if(suppressReturns) {
                            int index;
                            StmtList parentStmt = Qoogie.GetParentContext(this.atomicBlock.parentApl as AtomicStmt,
                                                                            this.procState.Body, out index);
                            if (index < parentStmt.BigBlocks.Count - 1 && parentStmt.BigBlocks[index + 1].LabelName != nextBlock.Label)
                            {
                                if (this.Next != null && !options.computeWP)
                                {
                                    return Expr.False;
                                }
                                //else if (this.Next == null && options.computeWP)
                                //{
                                //    return Expr.False;
                                //}
                            }
                        }
                        //---------------------
                        pred = FinishCompute(localIncarnationMap, localIntermSet, tc);
                    }
                    predicate = (predicate == null) ? pred : (options.computeWP ? Expr.And(predicate, pred) : Expr.Or(predicate, pred));
                }
            }
            else
            {
                predicate = FinishCompute(incarnationMap, intermSet, tc);
            }
        }
        else
        {
            predicate = ComputeForCommand(i, block, incarnationMap, intermSet);
        }
		
        Debug.Assert(predicate != null);

        if (i == 0)
        {
            predicate = LabeledExprHelper.Block(block, predicate);
        }

		return predicate;
    }


    protected Expr FinishCompute(Hashtable incarnationMap, Set<Variable> intermSet, TransferCmd tc)
    {
        if (nextTPGen != null)
        {
            return CallNextTPGen(null, incarnationMap, intermSet, tc);
        }
        else
        {
            return Expr.And(ComputePrimesPredicateGlobal(incarnationMap),
                            ComputePrimesPredicateLocal(incarnationMap, tc));
        }
    }



    protected MyHider myHider = new MyHider();
    
    public Expr CheckHide(Expr expr) {
		if(this.hideLocals) {
			return myHider.VisitExpr(expr);
		} else {
			return expr;
		}
    }

    public IdentifierExpr CheckHideVar(Variable var)
    {
        IdentifierExpr expr = new IdentifierExpr(Token.NoToken, var);
        return CheckHideVar(expr);
    }

    public IdentifierExpr CheckHideVar(IdentifierExpr iexpr)
    {
        IdentifierExpr hexpr = CheckHide(iexpr) as IdentifierExpr;
        Debug.Assert(hexpr != null);
        return hexpr;
    }
    
    public Expr CheckHide(Variable var) {
		IdentifierExpr expr = new IdentifierExpr(Token.NoToken, var);
		if(this.hideLocals) {
            return myHider.VisitExpr(expr);
		} else {
			return expr;
		}
    }

    public List<Expr> CheckHide(List<Expr> list)
    {
        List<Expr> newList = new List<Expr>(list.Count);
        for (int i = 0; i < list.Count; ++i)
        {
            newList.Add(CheckHide(list[i]));
        }

        return newList;
    }

    // var must not be hidden
    private bool AssertOnlyOneHavoc(Variable var, Hashtable incarnationMap, Set<Variable> intermSet)
    {
        Variable hiddenVar = CheckHideVar(var).Decl;

        if (options.singleHavocExcepts.Contains(hiddenVar) || procState.IsAuxVar(var) || ProofState.GetInstance().IsAuxVar(var) || procState.IsHiddenVar(var) || ProofState.GetInstance().IsHiddenVar(var))
        {
            return false;
        }
        
        if (intermSet.Contains(hiddenVar))
        {
            IdentifierExpr varPrimeExpr = CheckHideVar(procState.GetPrimedExpr(var));
            if (incarnationMap.ContainsKey(hiddenVar) && incarnationMap[hiddenVar].Equals(varPrimeExpr))
            {
                Output.LogLine("WARNING: Variable is havoced more than once: " + hiddenVar.Name);

                throw new MultipleHavocException(hiddenVar);
            }
        }
        return true;
    }

    // var must not be hidden
    private bool AssertUnifyHavocs(Variable var)
    {
        if (procState.IsAuxVar(var) || ProofState.GetInstance().IsAuxVar(var) || procState.IsHiddenVar(var) || ProofState.GetInstance().IsHiddenVar(var))
        {
            return false;
        }
        return true;
    }

    protected Variable CreateNextIncarnation(Variable var)
    {
        int next = 1;
        if (options.incarIdMap.ContainsKey(var))
        {
            next = options.incarIdMap[var];
        }
        options.incarIdMap[var] = next + 1;

        return new Incarnation(var, next);
    }

    // this does not modify incars for now!
    protected void HandleIncarnations(VariableSeq incars, IdentifierExprSeq modSeq, Hashtable incarnationMap, Set<Variable> intermSet, Cmd origCmd)
    {
        for (int i = 0; i < modSeq.Length; ++i)
        {
            IdentifierExpr modExpr = modSeq[i];

            IdentifierExpr iexpr = (IdentifierExpr)CheckHide(modExpr);
            Variable hiddenModVar = iexpr.Decl;

            Variable incarVar = null;

            // if unifyHavoc is enabled, use the same incarnation variable if exists
            if (options.unifyHavocs && AssertUnifyHavocs(modExpr.Decl))
            {
                Debug.Assert(options.singleHavocExcepts.Count == 0);

                if (!havoc2Incarnation.ContainsKey(origCmd))
                {
                    havoc2Incarnation.Add(origCmd, new List<Variable>());
                }

                List<Variable> havocs = havoc2Incarnation[origCmd];
                if (havocs.Count > i)
                {
                    incarVar = havocs[i];
                    Debug.Assert(incarVar != null);
                }
                else
                {
                    incarVar = CreateNextIncarnation(hiddenModVar);
                    havocs.Insert(i, incarVar); // update incars only if we create a new incarnation
                }
            }
            else if (!options.computeWP && options.singleHavoc && AssertOnlyOneHavoc(modExpr.Decl, incarnationMap, intermSet))
            {
                IdentifierExpr modPrimeExpr = procState.GetPrimedExpr(modExpr);
                incarVar = CheckHideVar(modPrimeExpr).Decl;
            }
            else // normal condition
            {
                incarVar = CreateNextIncarnation(hiddenModVar);
                incars.Add(incarVar); // update incars only if we create a new incarnation
            }

            IdentifierExpr incarExpr = new IdentifierExpr(Token.NoToken, incarVar);
            incarnationMap[hiddenModVar] = incarExpr;

            // trigger = new Trigger(Token.NoToken, true, new ExprSeq(CheckHide(procState.GetPrimedExpr(modexpr))), trigger);

            // update write set
            AddToWriteSet(hiddenModVar);

            // this is to check if modVar is read after being havoced
            intermSet.Remove(hiddenModVar);
        }

        // sanity check
        if (options.useQuant && incars.Length > 0)
        {
            Debug.Assert(!options.unifyHavocs);
        }
    }

    protected Expr ComputeForCommand(int i, Block block, Hashtable incarnationMap, Set<Variable> intermSet)
    {
		Cmd cmd = block.Cmds[i];

        #region CommentCmd
        if (cmd is CommentCmd)
        {
            return ComputeForBlock(i + 1, block, incarnationMap, intermSet);
        }
        #endregion

        Cmd origCmd = cmd;

		Expr predicate = null;
		Expr newPredicate = null;
		
		Hashtable clonedIncarnationMap = incarnationMap.Clone() as Hashtable;
        Substitution subst = Substituter.SubstitutionFromHashtable(clonedIncarnationMap);

        #region CallCmd
        if (cmd is CallCmd) {
			CallCmd callCmd = cmd as CallCmd;
			
			ProcedureState calleeState = ProofState.GetInstance().GetProcedureState(callCmd.Proc.Name);
			cmd = calleeState.SpecAtCall(atomicBlock.procState, callCmd);
        }
        #endregion

        #region assume asserts
        if (this.assumeAsserts && cmd is AssertCmd)
        {
            AssertCmd assertCmd = cmd as AssertCmd;
            cmd = new AssumeCmd(assertCmd.tok, assertCmd.Expr);
        }
        #endregion


            #region GatedAction
        if(cmd is GatedAction) {
		
			GatedAction gact = cmd as GatedAction;

            // we skip handling gate here, it is added as an assertion right before the gated action
            
            Trigger trigger = null;
            VariableSeq incars = null;

            Expr actionExpr = CheckHide(gact.action);

            // update read set
            UpdateReadSet(actionExpr, intermSet);

            Expr Q = null;
            while (true)
            {
                try
                {
                    incars = new VariableSeq();

                    Hashtable incarnationMap2 = incarnationMap.Clone() as Hashtable;

                    HandleIncarnations(incars, gact.mod, incarnationMap2, intermSet, origCmd);

                    Hashtable map = new Hashtable();
                    Hashtable oldmap = new Hashtable();

                    // locals
                    foreach (Variable var in procState.localVars.Values)
                    {
                        IdentifierExpr iexpr = CheckHideVar(new IdentifierExpr(Token.NoToken, var));
                        oldmap[iexpr.Decl] = Substituter.Apply(subst, iexpr);
                        map[iexpr.Decl] = ReadMap(incarnationMap2, iexpr.Decl);
                    }

                    // globals
                    foreach (Variable var in ProofState.GetInstance().globalVars.Values)
                    {
                        IdentifierExpr iexpr = new IdentifierExpr(Token.NoToken, var);
                        oldmap[var] = Substituter.Apply(subst, iexpr);
                        map[var] = ReadMap(incarnationMap2, iexpr.Decl);
                    }

                    Q = Logic.Substitute(map, oldmap, actionExpr);

                    predicate = ComputeForBlock(i + 1, block, incarnationMap2, intermSet);

                    break;

                }
                catch (MultipleHavocException ex)
                {
                    //foreach (IdentifierExpr modExpr in gact.mod)
                    //{
                    //    Variable hiddenVar = CheckHideVar(modExpr).Decl;
                    //    if (ex.hVar.Equals(hiddenVar))
                    //    {
                    //        options.singleHavocExcepts.Add(ex.hVar);
                    //    }
                    //    else
                    //    {
                    //        throw ex;
                    //    }
                    //}

                    bool found = false;
                    foreach (IdentifierExpr modExpr in gact.mod)
                    {
                        Variable hiddenVar = CheckHideVar(modExpr).Decl;
                        if (ex.hVar.Equals(hiddenVar))
                        {
                            options.singleHavocExcepts.Add(ex.hVar);
                            found = true;
                            break;
                        }
                    }
                    if (!found)
                    {
                        throw ex;
                    }
                }
            }

            Debug.Assert(Q != null);
			newPredicate = AddTransition(null, null, Q, predicate, incars, trigger);

            //if (options.computeWP)
            //{
            //    if (assumeAsserts)
            //    {
            //        newPredicate = Expr.Imp(P, Expr.Imp(Q, predicate));
            //    }
            //    else
            //    {
            //        newPredicate = Expr.And(P, Expr.Imp(Q, predicate));
            //    }
            //}
            //else
            //{
            //    newPredicate = Expr.And(P, Expr.And(Q, predicate));
            //}

            //if(options.useQuant && incars.Length > 0) {
            //    if (options.computeWP)
            //    {
            //        newPredicate = Logic.ForallExpr(incars, trigger, newPredicate);
            //    }
            //    else
            //    {
            //        newPredicate = Logic.ExistsExpr(incars, trigger, newPredicate);			
            //    }
            //}
           
            #endregion

            #region AssertCmd
        }
        else if (cmd is AssertCmd)
        {
            AssertCmd assertCmd = cmd as AssertCmd;

            Expr P = CheckHide(assertCmd.Expr);

            // update read set
            UpdateReadSet(P, intermSet);

            P = Logic.Substitute(subst, P);

            // label it
            if (options.computeWP && !P.Equals(Expr.True))
            {
                P = LabeledExprHelper.Assert(cmd, P);
            }

            predicate = ComputeForBlock(i + 1, block, incarnationMap, intermSet);

            newPredicate = AddTransition(P, null, null, predicate, null, null);

            //newPredicate = Expr.And(P, predicate);

            #endregion

            #region AssumeCmd
        }
        else if (cmd is AssumeCmd)
        {
            AssumeCmd assumeCmd = cmd as AssumeCmd;

            Expr P = CheckHide(assumeCmd.Expr);

            // update read set
            UpdateReadSet(P, intermSet);

            P = Logic.Substitute(subst, P);

            predicate = ComputeForBlock(i + 1, block, incarnationMap, intermSet);

            newPredicate = AddTransition(null, P, null, predicate, null, null);

            //if (options.computeWP)
            //{
            //    newPredicate = Expr.Imp(P, predicate);
            //}
            //else // TPred
            //{
            //    newPredicate = Expr.And(P, predicate);
            //}

            #endregion

            #region AssignCmd
        }
        else if (cmd is AssignCmd)
        {
            AssignCmd assignCmd = (cmd as AssignCmd).AsSimpleAssignCmd;

            for (int k = 0; k < assignCmd.Lhss.Count; k++)
            {
                SimpleAssignLhs assignLhs = assignCmd.Lhss[k] as SimpleAssignLhs;
                Debug.Assert(assignLhs != null);

                Expr rhs = CheckHide(assignCmd.Rhss[k]);

                // update read set
                UpdateReadSet(rhs, intermSet);

                //if (assignLhs is MapAssignLhs)
                //{
                //    MapAssignLhs mapLhs = assignLhs as MapAssignLhs;
                //    Debug.Assert(mapLhs.Map is SimpleAssignLhs, "For now, we do not allow nested accesses to maps in this situation!");
                //    foreach (Expr index in mapLhs.Indexes)
                //    {
                //        UpdateReadSet(CheckHide(index));
                //    }
                //}
                //else if (assignLhs is FieldAssignLhs)
                //{
                //    FieldAssignLhs fldLhs = assignLhs as FieldAssignLhs;
                //    UpdateReadSet(CheckHide(fldLhs.obj));
                //}

                Variable assignedVar = CheckHideVar(assignLhs.DeepAssignedIdentifier).Decl;

                // update write set
                AddToWriteSet(assignedVar);

                //if (assignLhs is MapAssignLhs)
                //{
                //    MapAssignLhs mapLhs = assignLhs as MapAssignLhs;
                //    Debug.Assert(mapLhs.Map is SimpleAssignLhs, "For now, we do not allow nested accesses to maps in this situation!");
                //    NAryExpr storeExpr = Expr.Store(CheckHide(mapLhs.Map.AsExpr), CheckHide(mapLhs.Indexes), rhs);
                //    storeExpr.TypeParameters = mapLhs.TypeParameters;
                //    rhs = storeExpr;
                //}
                //else if (assignLhs is FieldAssignLhs)
                //{
                //    FieldAssignLhs fldLhs = assignLhs as FieldAssignLhs;
                //    Record record = fldLhs.record;
                //    Debug.Assert(record != null);
                //    NAryExpr storeExpr = Expr.FieldStore(Token.NoToken, CheckHide(fldLhs.obj), fldLhs.fieldName, rhs, record);
                //    storeExpr.TypeParameters = fldLhs.TypeParameters;
                //    rhs = storeExpr;
                //}

                if (!options.computeWP && options.singleHavoc)
                {
                    AssertOnlyOneHavoc(assignLhs.DeepAssignedVariable, incarnationMap, intermSet);
                }

                Expr assignedVal = Logic.Substitute(subst, rhs);
                incarnationMap[assignedVar] = assignedVal;
            }

            predicate = ComputeForBlock(i + 1, block, incarnationMap, intermSet);

            newPredicate = predicate;

            #endregion

            //    #region NewCmd
            //}
            //else if (cmd is NewCmd)
            //{
            //    NewCmd newCmd = cmd as NewCmd;

            //    Expr obj = CheckHide(newCmd.assignLhs.AsExpr);

            //    Record record = newCmd.record;

            //    IdentifierExpr allocMapExpr = CheckHideVar(record.GetFieldMap("alloc"));

            //    // update write set
            //    AddToWriteSet(allocMapExpr.Decl);

            //    // update read set
            //    UpdateReadSet(allocMapExpr, intermSet);
            //    UpdateReadSet(obj, intermSet);

            //    Expr assumeNotAlloc = Logic.Substitute(subst, Expr.Eq(Expr.Select(allocMapExpr, obj), Logic.False));

            //    AssertOnlyOneHavoc(allocMapExpr.Decl, incarnationMap, intermSet);

            //    incarnationMap[allocMapExpr.Decl] = Logic.Substitute(subst, Expr.Store(allocMapExpr, obj, Logic.True));

            //    predicate = ComputeForBlock(i + 1, block, incarnationMap, intermSet);

            //    newPredicate = AddTransition(null, assumeNotAlloc, null, predicate, null, null);

            //    //if (options.computeWP)
            //    //{
            //    //    newPredicate = Expr.Imp(assumeNotAlloc, predicate);
            //    //}
            //    //else // TPred
            //    //{
            //    //    newPredicate = Expr.And(assumeNotAlloc, predicate);
            //    //}

            //    newPredicate = predicate;

            //    #endregion

            //    #region FreeCmd
            //}
            //else if (cmd is FreeCmd)
            //{
            //    FreeCmd freeCmd = cmd as FreeCmd;

            //    Expr obj = CheckHide(freeCmd.obj);

            //    Record record = freeCmd.record;

            //    IdentifierExpr allocMapExpr = CheckHideVar(record.GetFieldMap("alloc"));

            //    // update write set
            //    AddToWriteSet(allocMapExpr.Decl);

            //    // update read set
            //    UpdateReadSet(allocMapExpr, intermSet);
            //    UpdateReadSet(obj, intermSet);

            //    Expr assertAlloc = Logic.Substitute(subst, Expr.Eq(Expr.Select(allocMapExpr, obj), Logic.True));

            //    AssertOnlyOneHavoc(allocMapExpr.Decl, incarnationMap, intermSet);

            //    incarnationMap[allocMapExpr.Decl] = Logic.Substitute(subst, Expr.Store(allocMapExpr, obj, Logic.False));

            //    predicate = ComputeForBlock(i + 1, block, incarnationMap, intermSet);

            //    newPredicate = AddTransition(assertAlloc, null, null, predicate, null, null);

            //    //newPredicate = Expr.And(assertAlloc, predicate);

            //    newPredicate = predicate;

            //    #endregion

            #region JoinCmd
        }
        else if (cmd is JoinCmd)
        {
            predicate = ComputeForBlock(i + 1, block, incarnationMap, intermSet);

            newPredicate = predicate;

            #endregion

            //    #region SimpleAssignCmd
            //}
            //else if (cmd is SimpleAssignCmd)
            //{
            //    SimpleAssignCmd assignCmd = cmd as SimpleAssignCmd;

            //    IdentifierExpr lhs = (IdentifierExpr)CheckHide(assignCmd.Lhs);
            //    Expr rhs = CheckHide(assignCmd.Rhs);

            //    // update read set
            //    UpdateReadSet(rhs);

            //    // update write set
            //    AddToWriteSet(lhs.Decl);

            //    Variable assignedVar = lhs.Decl;
            //    Expr assignedVal = Logic.Substitute(subst, rhs);

            //    incarnationMap[assignedVar] = assignedVal;

            //    predicate = ComputeForBlock(i + 1, block, incarnationMap);

            //    newPredicate = predicate;

            //    #endregion

            //    #region ArrayAssignCmd
            //}
            //else if (cmd is ArrayAssignCmd)
            //{

            //    ArrayAssignCmd arrayCmd = (ArrayAssignCmd)cmd;

            //    Expr index0 = CheckHide(arrayCmd.Index0);
            //    Expr index1 = arrayCmd.Index1 == null ? null : CheckHide(arrayCmd.Index1);
            //    Expr rhs = CheckHide(arrayCmd.Rhs);
            //    IdentifierExpr array = (CheckHide(arrayCmd.Array) as IdentifierExpr);
            //    UpdateExpr storeExp = new UpdateExpr(cmd.tok, array, index0, index1, rhs);
            //    storeExp.Type = arrayCmd.Array.Type;

            //    // update read set
            //    UpdateReadSet(index0);
            //    if (index1 != null) UpdateReadSet(index1);
            //    UpdateReadSet(rhs);

            //    // update write set
            //    AddToWriteSet(array.Decl);

            //    IdentifierExpr lhs = (IdentifierExpr)CheckHide(arrayCmd.Array);
            //    Variable assignedVar = lhs.Decl;

            //    #region Substitute all variables in store(a,E,F,G) with the current map
            //    storeExp = (UpdateExpr)Logic.Substitute(subst, storeExp);
            //    #endregion

            //    incarnationMap[assignedVar] = storeExp;

            //    predicate = ComputeForBlock(i + 1, block, incarnationMap);

            //    newPredicate = predicate;

            //    #endregion

            #region HavocCmd
        }
        else if (cmd is HavocCmd)
        {
            HavocCmd havocCmd = cmd as HavocCmd;

            Debug.Assert(havocCmd.Vars.Length > 0);

            Trigger trigger = null;
            VariableSeq incars = null;

            while (true)
            {
                try
                {
                    incars = new VariableSeq();

                    Hashtable incarnationMap2 = incarnationMap.Clone() as Hashtable;

                    HandleIncarnations(incars, havocCmd.Vars, incarnationMap2, intermSet, origCmd);

                    predicate = ComputeForBlock(i + 1, block, incarnationMap2, intermSet);

                    break;
                }
                catch (MultipleHavocException ex)
                {
                    //foreach (IdentifierExpr modExpr in havocCmd.Vars)
                    //{
                    //    Variable hiddenVar = CheckHideVar(modExpr).Decl;
                    //    if (ex.hVar.Equals(hiddenVar))
                    //    {
                    //        options.singleHavocExcepts.Add(ex.hVar);
                    //    }
                    //    else
                    //    {
                    //        throw ex;
                    //    }
                    //}
                    bool found = false;
                    foreach (IdentifierExpr modExpr in havocCmd.Vars)
                    {
                        Variable hiddenVar = CheckHideVar(modExpr).Decl;
                        if (ex.hVar.Equals(hiddenVar))
                        {
                            options.singleHavocExcepts.Add(ex.hVar);
                            found = true;
                            break;
                        }
                    }
                    if (!found)
                    {
                        throw ex;
                    }
                }
            }

            newPredicate = AddTransition(null, null, null, predicate, incars, trigger);

            //if (options.useQuant && incars.Length > 0)
            //{
            //    Debug.Assert(!options.unifyHavocs);
            //    if (options.computeWP)
            //    {
            //        newPredicate = Logic.ForallExpr(incars, trigger, predicate);
            //    }
            //    else
            //    {
            //        newPredicate = Logic.ExistsExpr(incars, trigger, predicate);
            //    }
            //}
            //else
            //{
            //    newPredicate = predicate;
            //}
            #endregion

            #region AbstractCmd
        }
        //else if (cmd is BeginAbstractCmd)
        //{
        //    BeginAbstractCmd abstractCmd = cmd as BeginAbstractCmd;

        //    Trigger trigger = null;
        //    VariableSeq incars = new VariableSeq();
        //    foreach (IdentifierExpr hexpr in abstractCmd.Vars)
        //    {
        //        IdentifierExpr iexpr = (IdentifierExpr)CheckHide(hexpr);
        //        Variable hvar = iexpr.Decl;

        //        Variable incarVar = CreateNextIncarnation(hvar, mergedMap, origCmd);

        //        IdentifierExpr incarExpr = new IdentifierExpr(Token.NoToken, incarVar);

        //        if (abstractCmd.IsRead)
        //        {
        //            readAbstMap[hvar] = incarExpr;
        //        }
        //        else
        //        {
        //            incarnationMap[hvar] = incarExpr;

        //            // update write set
        //            AddToWriteSet(iexpr.Decl);
        //        }
        //        incars.Add(incarVar);

        //        // trigger = new Trigger(Token.NoToken, true, new ExprSeq(iexpr), trigger);
        //    }

        //    //---------------------------------------------
        //    Expr P = CheckHide(abstractCmd.Assumption);

        //    // update read set
        //    // UpdateReadSet(P);

        //    P = Logic.Substitute(MergeMaps(incarnationMap), P);
        //    //---------------------------------------------

        //    predicate = ComputeForBlock(i + 1, block, incarnationMap);

        //    // the predicate is an assumption:
        //    if (options.computeWP)
        //    {
        //        newPredicate = Expr.Imp(P, predicate);
        //    }
        //    else // TPred
        //    {
        //        newPredicate = Expr.And(P, predicate);
        //    }

        //    if (options.useQuant && incars.Length > 0)
        //    {
        //        newPredicate = Logic.ExistsExpr(incars, trigger, predicate);
        //    }
        //    else
        //    {
        //        newPredicate = predicate;
        //    }
        //    #endregion

        //    #region EndAbstractCmd
        //}
        //else if (cmd is EndAbstractCmd)
        //{
        //    EndAbstractCmd endabstractCmd = cmd as EndAbstractCmd;

        //    foreach (IdentifierExpr hexpr in endabstractCmd.Vars)
        //    {
        //        IdentifierExpr iexpr = (IdentifierExpr)CheckHide(hexpr);
        //        Variable hvar = iexpr.Decl;

        //        readAbstMap.Remove(hvar);
        //    }

        //    newPredicate = ComputeForBlock(i + 1, block, incarnationMap);

        //}
            #endregion

        if (newPredicate == null) {
			Output.AddError("Unexpected kind of command: " + Output.ToString(cmd));			
			Debug.Assert(false);
		}
		return newPredicate;
   }

    private Expr AddTransition(Expr assertion, Expr assumption, Expr transition, Expr predicate, VariableSeq incars, Trigger trigger)
    {
        Expr newPredicate = predicate;
        
        // add transition
        if (transition != null)
        {
            if (options.computeWP)
            {
                newPredicate = Expr.Imp(transition, newPredicate);
            }
            else
            {
                newPredicate = Expr.And(transition, newPredicate);
            }
        }

        // add assumption
        if (assumption != null)
        {
            if (options.computeWP)
            {
                newPredicate = Expr.Imp(assumption, newPredicate);
            }
            else
            {
                newPredicate = Expr.And(assumption, newPredicate);
            }
        }

        // add assertion
        if (assertion != null)
        {
            if (options.computeWP)
            {
                if (assumeAsserts)
                {
                    newPredicate = Expr.Imp(assertion, newPredicate);
                }
                else
                {
                    newPredicate = Expr.And(assertion, newPredicate);
                }
            }
            else
            {
                newPredicate = Expr.And(assertion, newPredicate);
            }
        }

        // do quantification
        if (options.useQuant && incars != null && incars.Length > 0)
        {
            if (options.computeWP)
            {
                newPredicate = Logic.ForallExpr(incars, trigger, newPredicate);
            }
            else
            {
                newPredicate = Logic.ExistsExpr(incars, trigger, newPredicate);
            }
        }

        return newPredicate;
    }

    //--------------------------------------------------------

    virtual protected Expr ComputePrimesPredicateLocal(Hashtable incarnationMap, TransferCmd tc)
    {
        Debug.Assert(incarnationMap != null);

        if (options.computeWP)
        {
            // add the split invariant
            Expr splitinv = ProofState.GetInstance().SplitInvariant;
            return Logic.Substitute(incarnationMap, new Hashtable(), Expr.Imp(splitinv, CheckHide(options.postCondForWP)));
        }

        // computeXP

        Expr localExpr = Expr.True;
        foreach (Variable lvar in procState.localVars.Values)
        {
            // skip dead locals (computed by APLStmt.ComputeDeadLocals)
            if (this.deadLocals != null
                && this.deadLocals.Contains(lvar))
                continue;

            //if(lvar != procState.pcExpr.Decl) { // we will not handle pc here but below
            IdentifierExpr primeexp = procState.GetPrimedExpr(lvar);
            primeexp = CheckHide(primeexp) as IdentifierExpr;

            IdentifierExpr lvarexpr = new IdentifierExpr(Token.NoToken, lvar);
            lvarexpr = CheckHideVar(lvarexpr);

            Expr finalExpr = null;
            if (!procState.IsAuxVar(lvar))
            {
                if (incarnationMap.Contains(lvarexpr.Decl))
                {
                    finalExpr = (Expr)incarnationMap[lvarexpr.Decl];
                    localExpr = Expr.And(localExpr, FinalEqualsExpr(primeexp, finalExpr));
                }
                else if (!procState.IsHiddenVar(lvar))
                {
                    // regular case x == x'
                    if (!compactForm)
                    {
                        finalExpr = lvarexpr;
                        localExpr = Expr.And(localExpr, FinalEqualsExpr(primeexp, finalExpr));
                    }
                }
            }
            //}
        }

        //---------------------------------
        // handle pc expression here
        //Expr pcprime = procState.GetPrimedExpr(procState.pcExpr);
        //Expr nextExpr = Expr.Eq(CheckHide(pcprime), GetNextPc(tc));

        //return Expr.And(localExpr, nextExpr); 
        return localExpr;
    }

   //--------------------------------------------------------

    virtual protected Expr ComputePrimesPredicateGlobal(Hashtable incarnationMap) {

        Debug.Assert(incarnationMap != null);

        if (options.computeWP)
        {
            // add the split invariant
            Expr splitinv = ProofState.GetInstance().SplitInvariant;
            return Logic.Substitute(incarnationMap, new Hashtable(), Expr.Imp(splitinv, CheckHide(options.postCondForWP)));
        }
		
		Expr globalExpr = Expr.True;
		foreach(Variable gvar in ProofState.GetInstance().globalVars.Values) {
            IdentifierExpr primeexp = ProofState.GetInstance().GetPrimedExpr(gvar);
			
			IdentifierExpr gvarexpr = new IdentifierExpr(Token.NoToken, gvar);

            Expr finalExpr = null;
            if (!ProofState.GetInstance().IsAuxVar(gvar))
            {
                if (incarnationMap.Contains(gvar))
                {
                    finalExpr = (Expr)incarnationMap[gvarexpr.Decl];
                    globalExpr = Expr.And(globalExpr, FinalEqualsExpr(primeexp, finalExpr));
                }
                else if (!ProofState.GetInstance().IsHiddenVar(gvar))
                {
                    // regular case x == x'
                    if (!compactForm)
                    {
                        finalExpr = gvarexpr;
                        globalExpr = Expr.And(globalExpr, FinalEqualsExpr(primeexp, finalExpr));
                    }
                }
            }
		}
		
		return globalExpr;
    }

    private Expr FinalEqualsExpr(IdentifierExpr primeExpr, Expr finalExpr)
    {

        Microsoft.Boogie.Type type = primeExpr.Decl.TypedIdent.Type;
#if false
        if (type.IsMap)
        {
            MapType mtype = type as MapType;
            VariableSeq bounds = new VariableSeq();
            List<Expr> indexes = new List<Expr>();
            for (int i = 0; i < mtype.MapArity; ++i)
            {
                BoundVariable bvar = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x" + i.ToString(), mtype.Arguments[i]));
                bounds.Add(bvar);
                indexes.Add(new IdentifierExpr(Token.NoToken, bvar));
            }
            return new ForallExpr(Token.NoToken, bounds, Expr.Eq(Expr.Select(varexpr, indexes), Expr.Select(primeexp, indexes)));
        }
        else
        {
#endif
        // check if finalExpr is equivalent to primeExpr, if so, skip it
        if (finalExpr is IdentifierExpr)
        {
            IdentifierExpr iexpr = finalExpr as IdentifierExpr;
            if (iexpr.Decl == primeExpr.Decl)
            {
                return Expr.True;
            }
        }

        return Logic.EquivExpr(type, primeExpr, finalExpr);
#if false
        }
#endif
    }

}


} // end namespace QED