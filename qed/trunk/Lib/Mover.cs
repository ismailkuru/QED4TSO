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
using System.Threading;
using PureCollections;

public class FixMoverCommand : ProofCommand
{
	bool right;
	bool left;
    bool non;
	string blocklabel;

	public FixMoverCommand(bool r, bool l, bool n, string label)
		: base("fixmover")
	{
		this.right = r;
		this.left = l;
        this.non = n;
		this.blocklabel = label;
	
		desc = "fixmover ";
		if(right) desc += "r";
		if(left) desc += "l";
        if (non) desc += "n";
		desc += " " + blocklabel;
	}

    public static string Usage()
    {
        return "fixmover l|r|n atomicBlockLabel@procedureName";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("fixmover"))
        {
            bool r = false;
            bool l = false;
            bool n = false;
            string rl = parser.NextAsString();
            r = rl.IndexOf("r") >= 0;
            l = rl.IndexOf("l") >= 0;
            n = rl.IndexOf("n") >= 0;

            string label = parser.NextAsString();

            return new FixMoverCommand(r, l, n, label);
        }
        return null;
    }
	
	override public bool Run(ProofState proofState) {
	
		AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);
        if (atomicBlock == null) return false;

        MoverType mover = atomicBlock.Mover;

        if (non)
        {
            mover.None = true;
            mover.BothFixed = true;
        }
        else
        {
            if (right)
            {
                mover.Right = true;
                mover.RightFixed = true;
            }

            if (left)
            {
                mover.Left = true;
                mover.LeftFixed = true;
            }
        }

        atomicBlock.Mover = mover;
        atomicBlock.procState.MarkAsTransformed();
		
		return false;
	}
	
} // end class FixMoverCommand

/***************************************************************************/
/***************************************************************************/
  
public class MoverCommand : ProofCommand
{
	string label;
    bool isproc;
    bool isstandalone;
    public List<MoverCheck> mcs;

	public MoverCommand(string lbl, bool isproc, bool sa)
		: base("mover")
	{
		this.label = lbl;
        this.isproc = isproc;
        this.isstandalone = sa;
        desc = isproc ? ("mover proc " + label) : ("mover " + label);
	}

    public static string Usage()
    {
        return "mover (proc procName)|all|atomicBlockLabel@procedureName";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("mover"))
        {
            string label = parser.NextAsString();
            if (label == "proc")
            {
                label = parser.NextAsString();
                return new MoverCommand(label, true, true);
            }

            return new MoverCommand(label, false, true);
        }
        return null;
    }
	
	override public bool Run(ProofState proofState) {

        foreach (ProcedureState procState in proofState.ProcedureStates)
        {
            procState.ComputeAtomicBlocks();
        }

        List<AtomicBlock> atomicBlocks = new List<AtomicBlock>();

        if (isproc)
        {
            ProcedureState procState = proofState.GetProcedureState(label);
            atomicBlocks.AddRange(procState.AtomicBlocks);
        }
        else
        {
            if (label == "all")
            {
                foreach (ProcedureState procState in proofState.ProcedureStates)
                {
                    // if the procedure is not explicitly marked to be skipped when computing movers 
                    // (its atomic blocks are still included when computing moverness of others)
                    if (!QKeyValue.FindBoolAttribute(procState.impl.Proc.Attributes, "skipmc"))
                    {
                        atomicBlocks.AddRange(procState.AtomicBlocks);
                    }
                }
            }
            else
            {
                AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(label);
                if (atomicBlock == null)
                {
                    Output.AddError("Atomic block does not exists: " + label);
                    return false;
                }

                atomicBlocks.Add(atomicBlock);
            }
        }

        if (this.isstandalone)
        {
            // reset the mover check cache
            MCache.Reset();
        }

        this.mcs = DoRun(proofState, atomicBlocks);

        // update global movercheck list
        ProofState.GetInstance().LastMoverChecks = this.mcs;

        if (this.isstandalone)
        {
            Output.AddLine("Mover Report");
            Output.AddLine(MoverCheck.Report(proofState.LastMoverChecks));
        }

        return false;
	}

    static private List<MoverCheck> DoRun(ProofState proofState, List<AtomicBlock> atomicBlocks)
    {
        List<MoverCheck> mcs = new List<MoverCheck>();

        bool tmp = CommandLineOptions.Clo.RestartProverPerVC;
        CommandLineOptions.Clo.RestartProverPerVC = false;

        List<MoverTypeChecker> checkers = new List<MoverTypeChecker>();

        List<AtomicBlock> allBlocks = proofState.AtomicBlocks;

        // TODO: construct and use the mc map
        
        foreach (AtomicBlock atomicBlock in atomicBlocks)
        {
            Output.AddLine("Checking mover type of " + atomicBlock.UniqueLabel);

            MoverTypeChecker checker = new MoverTypeChecker(proofState, atomicBlock, allBlocks);

            checker.Run(); // sets the mover type of the block as well

            mcs.AddRange(checker.mcs);
        }

        CommandLineOptions.Clo.RestartProverPerVC = tmp;

        return mcs;
    }

    static public void DoRun2(ProofState proofState, List<AtomicBlock> atomicBlocks)
    {
        bool tmp = CommandLineOptions.Clo.RestartProverPerVC;
        CommandLineOptions.Clo.RestartProverPerVC = false;

        List<MoverTypeChecker> checkers = new List<MoverTypeChecker>();

        List<AtomicBlock> allBlocks = proofState.AtomicBlocks;

        foreach (AtomicBlock atomicBlock in atomicBlocks)
        {
            MoverTypeChecker checker = new MoverTypeChecker(proofState, atomicBlock, allBlocks);

            checkers.Add(checker);

            checker.Fork();
        }

        foreach (MoverTypeChecker checker in checkers)
        {
            checker.Join();

            Output.AddLine("Checked mover type of " + checker.AtomicBlock.UniqueLabel);
        }

        CommandLineOptions.Clo.RestartProverPerVC = tmp;
    }


} // end class MoverCommand

public delegate bool MoverTestFunc(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch, MoverCheck mc);

public class MoverCheck
{
    public AtomicBlock thisBlock;
    public AtomicBlock thatBlock;
    public bool isRight;
    public bool wpOK;
    public bool xpOK;
    public ErrorModel errModel;

    public MoverCheck(AtomicBlock thisB, AtomicBlock thatB, bool isr)
    {
        this.thisBlock = thisB;
        this.thatBlock = thatB;
        this.isRight = isr;
        this.wpOK = this.xpOK = false;
    }

    public bool Success
    {
        get
        {
            return this.wpOK && this.xpOK;
        }
    }

    public override string ToString()
    {
        StringBuilder strb = new StringBuilder();
        if (Success)
        {
            strb.Append("Succeess"); // this is usually not printed
        }
        else
        {
            strb.Append(isRight ? "Right-mover" : "Left-mover").Append(" check (").Append(!wpOK ? "WP " : "").Append(!xpOK ? "XP" : "").Append(") failed for ").Append(thisBlock.UniqueLabel).Append(". Other block: ").Append(thatBlock.UniqueLabel);
        }
        return strb.ToString();
    }

    static public string Report(List<MoverCheck> mcs)
    {
        Debug.Assert(mcs != null);
        StringBuilder strb = new StringBuilder();
        foreach (MoverCheck mc in mcs)
        {
            if (!mc.Success)
            {
                strb.AppendLine(mc.ToString());
            }
        }
        return strb.ToString();
    }
}

public class MoverTypeChecker
{
    AtomicBlock atomicBlock;

    ProofState proofState;

    MoverType result;

    MoverType initial;

    Thread thread;

    List<AtomicBlock> allBlocks;

    Checker checker;

    public List<MoverCheck> mcs;

    public MoverType Result
    {
        get
        {
            return result;
        }
    }

    public AtomicBlock AtomicBlock
    {
        get
        {
            return atomicBlock;
        }
    }

    static List<MoverTestFunc> moverTesters;

    static MoverTypeChecker() {
        // set up mover testers
        moverTesters = new List<MoverTestFunc>();

        //moverTesters.Add(new MoverTestFunc(MoverTypeChecker.CheckTrapPred));
        //moverTesters.Add(new MoverTestFunc(MoverTypeChecker.CheckLeftUnSat));
        moverTesters.Add(new MoverTestFunc(MoverTypeChecker.CheckConflict));
        moverTesters.Add(new MoverTestFunc(MoverTypeChecker.CheckWoutQuant));
        moverTesters.Add(new MoverTestFunc(MoverTypeChecker.CheckWithUnifiedHavocs));
        moverTesters.Add(new MoverTestFunc(MoverTypeChecker.CheckWithQuant));
        //moverTesters.Add(new MoverTestFunc(MoverTypeChecker.CheckNonConflict));
    }

    public MoverTypeChecker(ProofState pstate, AtomicBlock block)
        : this(pstate, block, pstate.AtomicBlocks)
    {
    }


    public MoverTypeChecker(ProofState pstate, AtomicBlock block, List<AtomicBlock> blocks)
    {
        this.allBlocks = blocks;
        this.proofState = pstate;
        this.atomicBlock = block;
    }

    public void Fork()
    {
        ThreadStart start = new ThreadStart(this.Run);
        this.thread = new Thread(start);
        this.thread.Start();
    }

    public void Join()
    {
        this.thread.Join();
    }


    public void Run()
    {
        Set<AtomicBlock> straightAtomicBlocks = this.atomicBlock.DeepCollectStraightAtomicBlocks();
        Debug.Assert(straightAtomicBlocks.Count >= 1); // if 1 then it contains this.atomicBlock

        // TODO: eliminate redundant checks
        foreach (AtomicBlock straightAtomicBlock in straightAtomicBlocks)
        {
            TPGenerator thisTPGen = new TPGenerator(straightAtomicBlock); // hide:false
            // set dead locals (only for mover check)
            thisTPGen.deadLocals = straightAtomicBlock.deadLocals;

            straightAtomicBlock.Mover = this.result = Check(this.proofState, thisTPGen); 
        }      
        // now collect all the results
        if (!atomicBlock.parent.isCompound)
        {
            Debug.Assert(this.atomicBlock == straightAtomicBlocks.PickOne());
            this.atomicBlock.Mover = this.result;
        }
        else
        {
            // we should visit the inner atomic stmts to compute the overall mover
            new MoverVisitor().Compute(this.atomicBlock.procState, this.atomicBlock.parent.body);
            this.atomicBlock.Mover = this.atomicBlock.parent.Mover;
        }
    }

    public MoverType Check(ProofState proofState, TPGenerator thisTPGen)
    {
        this.checker = Prover.GetInstance().AcquireChecker();

        this.mcs = new List<MoverCheck>();

        AtomicBlock thisBlock = thisTPGen.APLBlock as AtomicBlock;

        this.initial = thisBlock.Mover.Clone();
        this.result = thisBlock.Mover.Clone();
        // if both fixed, then do nothing
        if (this.initial.Both || this.initial.BothFixed) return this.result;

        this.result.MakeBothMover();

        for (int j = 0, n = allBlocks.Count; j < n && !this.result.None; ++j)
        {
            AtomicBlock thatBlock = allBlocks[j];
            Set<AtomicBlock> straightAtomicBlocks = thatBlock.DeepCollectStraightAtomicBlocks();
            Debug.Assert(straightAtomicBlocks.Count >= 1); // if 1 then it contains this.atomicBlock

            // TODO: eliminate redundant checks
            foreach (AtomicBlock thatStraightBlock in straightAtomicBlocks)
            {
                TPGenerator thatTPGen = new TPGenerator(thatStraightBlock, true);
                // set dead locals (only for mover check)
                thatTPGen.deadLocals = thatStraightBlock.deadLocals;

                TypeCheckMover(proofState, thisTPGen, thatTPGen, this.result);
            }
        }

        Prover.GetInstance().ReleaseChecker(this.checker);

        return this.result;
    }

    protected void TypeCheckMover(ProofState proofState, TPGenerator thisTPGen, TPGenerator thatTPGen, MoverType mover)
    {
        AtomicBlock thisBlock = thisTPGen.APLBlock as AtomicBlock;
        AtomicBlock thatBlock = thatTPGen.APLBlock as AtomicBlock;

        // check right mover
        if (!initial.Right && !mover.RightFixed)
        {
            if (mover.Right)
            {
                bool success = false;
                // first check the cache
                if (!MCache.Get(thisBlock, thatBlock, out success))
                {
                    // now go to the theorem prover
                    success = DoCheck(true, proofState, thisTPGen, thatTPGen);
                    // store the result in the cache
                    MCache.Set(success, thisBlock, thatBlock);
                }
                if (!success)
                {
                    mover.Right = false;
                    Output.AddLine(thisBlock.Label + " !move Right of " + thatBlock.Label);
                }
            }
        }

        // check left mover
        if (!initial.Left && !mover.LeftFixed)
        {
            if (mover.Left)
            {
                bool success = false;
                // first check the cache
                if (!MCache.Get(thatBlock, thisBlock, out success))
                {
                    // now go to the theorem prover
                    success = DoCheck(false, proofState, thatTPGen, thisTPGen);
                    // store the result in the cache
                    MCache.Set(success, thatBlock, thisBlock);
                }
                if (!success)
                {
                    mover.Left = false;
                    Output.AddLine(thisBlock.Label + " !move Left of " + thatBlock.Label);
                }
            }
        }
    }


    protected bool DoCheck(bool isright, ProofState proofState, TPGenerator thisTPGen, TPGenerator thatTPGen)
    {
        bool success = false;

        AtomicBlock thisBlock = thisTPGen.APLBlock as AtomicBlock;
        AtomicBlock thatBlock = thatTPGen.APLBlock as AtomicBlock;

        Expr inv = Expr.And(proofState.Invariant,
                             Expr.And(thisTPGen.CheckHide(thisBlock.procState.LocalInvariant),
                                      thatTPGen.CheckHide(thatBlock.procState.LocalInvariant)));

        //thisTPGen.AtomicBlock.procState.EnableCondAssertsToCheck();
        //thatTPGen.AtomicBlock.procState.EnableCondAssertsToCheck();

        MoverCheck mc = new MoverCheck(thisTPGen.APLBlock as AtomicBlock, thatTPGen.APLBlock as AtomicBlock, isright);
        for (int i = 0, n = moverTesters.Count; i < n; ++i)
        {
            MoverTestFunc func = moverTesters[i];

            if (func(proofState, inv, thisTPGen, thatTPGen, this.checker, mc))
            {
                success = true;
                break;
            }
        }
        // this takes the mc of the last mover check function
        if (!success) mcs.Add(mc);

        //thisTPGen.AtomicBlock.procState.DisableCondAssertsToCheck();
        //thatTPGen.AtomicBlock.procState.DisableCondAssertsToCheck();

        return success;
    }

    static protected bool CheckConflict(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch, MoverCheck mc)
    {
        AtomicBlock thisBlock = thisTPGen.APLBlock as AtomicBlock;
        AtomicBlock thatBlock = thatTPGen.APLBlock as AtomicBlock;

        Pair thisRWSet = thisBlock.ComputeReadWriteSet();
        Set<GlobalVariable> thisReadSet = Util.FilterGlobalVariables(thisRWSet.First as Set<Variable>);
        Set<GlobalVariable> thisWriteSet = Util.FilterGlobalVariables(thisRWSet.Second as Set<Variable>);

        Pair thatRWSet = thatBlock.ComputeReadWriteSet();
        Set<GlobalVariable> thatReadSet = Util.FilterGlobalVariables(thatRWSet.First as Set<Variable>);
        Set<GlobalVariable> thatWriteSet = Util.FilterGlobalVariables(thatRWSet.Second as Set<Variable>);

        if ((thisReadSet.Intersection(thatWriteSet).Count == 0)
               && (thisWriteSet.Intersection(thatReadSet).Count == 0)
               && (thisWriteSet.Intersection(thatWriteSet).Count == 0))
        {
            mc.wpOK = mc.xpOK = true;
            Statistics.Count("MOVER_CHECK_BY_CheckConflict");
            return true;
        }
        return false;
    }

    static protected bool CheckWithQuant(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch, MoverCheck mc)
    {
        if (Logic.MoverCheck(inv, thisTPGen, thatTPGen, true, false, mc))
        {
            Statistics.Count("MOVER_CHECK_BY_CheckWithQuant");
            return true;
        }
        return false;
    }

    static protected bool CheckWoutQuant(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch, MoverCheck mc)
    {
        if (Logic.MoverCheck(inv, thisTPGen, thatTPGen, false, false, mc))
        {
            Statistics.Count("MOVER_CHECK_BY_CheckWithoutQuant");
            return true;
        }
        return false;
    }

    static protected bool CheckWithUnifiedHavocs(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch, MoverCheck mc)
    {
        if (Logic.MoverCheck(inv, thisTPGen, thatTPGen, false, true, mc))
        {
            Statistics.Count("MOVER_CHECK_BY_CheckWithUnifiedHavocs");
            return true;
        }
        return false;
    }

    //static protected bool CheckTrapPred(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch)
    //{

    //    AtomicBlock thisBlock = thisTPGen.APLBlock as AtomicBlock;
    //    AtomicBlock thatBlock = thatTPGen.APLBlock as AtomicBlock;

    //    if(thisBlock.TrapPredicate == null)
    //        return false;

    //    Expr thatPred = thatTPGen.Compute(TPGenOptions.ComputeTPred);

    //    Expr condition = Expr.Imp(Expr.And(inv, thatPred), thisBlock.TrapPredicate);

    //    return Prover.GetInstance().CheckValid(condition, ch);
    //}

    //static protected bool CheckWoutQuant(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch)
    //{
    //    Expr leftWP = ComputeInterleavedGatePredicate(thisTPGen, thatTPGen);
    //    Expr rightWP = ComputeInterleavedGatePredicate(thatTPGen, thisTPGen);

    //    Expr condition = Expr.Imp(Expr.And(inv, rightWP), leftWP);

    //    bool result = false;
    //    if (Prover.GetInstance().CheckValid(condition, ch))
    //    {
    //        Expr leftPred = ComputeInterleavedTransitionPredicateWoutQuant(thisTPGen, thatTPGen);
    //        Expr rightPred = ComputeInterleavedTransitionPredicateWoutQuant(thatTPGen, thisTPGen);

    //        condition = Expr.Imp(Logic.And(inv, rightWP, leftPred), rightPred);

    //        result = Prover.GetInstance().CheckValid(condition, ch);
    //    }

    //    if (result) Statistics.Count("MOVER_CHECK_BY_CheckWoutQuant");

    //    return result;
    //}

    //static protected bool CheckWithQuant(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch)
    //{
    //    Expr leftWP = ComputeInterleavedGatePredicate(thisTPGen, thatTPGen);
    //    Expr rightWP = ComputeInterleavedGatePredicate(thatTPGen, thisTPGen);

    //    Expr condition = Expr.Imp(Expr.And(inv, rightWP), leftWP);

    //    bool result = false;
    //    if (Prover.GetInstance().CheckValid(condition, ch))
    //    {
    //        Expr leftPred = ComputeInterleavedTransitionPredicate(thisTPGen, thatTPGen, false);
    //        Expr rightPred = ComputeInterleavedTransitionPredicate(thatTPGen, thisTPGen, true);

    //        condition = Expr.Imp(Logic.And(inv, rightWP, leftPred), rightPred);

    //        result = Prover.GetInstance().CheckValid(condition, ch);
    //    }

    //    if (result) Statistics.Count("MOVER_CHECK_BY_CheckWithQuant");

    //    return result;
    //}


    //static protected bool CheckWithUnifiedHavocs(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch)
    //{
    //    thisTPGen.ResetUnifiedHavocs();
    //    thatTPGen.ResetUnifiedHavocs();

    //    Expr leftWP = ComputeInterleavedGatePredicateWithUnifiedHavocs(thisTPGen, thatTPGen);
    //    Expr rightWP = ComputeInterleavedGatePredicateWithUnifiedHavocs(thatTPGen, thisTPGen);

    //    Expr condition = Expr.Imp(Expr.And(inv, rightWP), leftWP);

    //    bool result = false;
    //    if (Prover.GetInstance().CheckValid(condition, ch))
    //    {
    //        thisTPGen.ResetUnifiedHavocs();
    //        thatTPGen.ResetUnifiedHavocs();

    //        Expr leftPred = ComputeInterleavedTransitionPredicateWithUnifiedHavocs(thisTPGen, thatTPGen);
    //        Expr rightPred = ComputeInterleavedTransitionPredicateWithUnifiedHavocs(thatTPGen, thisTPGen);

    //        condition = Expr.Imp(Logic.And(inv, rightWP, leftPred), rightPred);

    //        result = Prover.GetInstance().CheckValid(condition, ch);
    //    }

    //    if (result) Statistics.Count("MOVER_CHECK_BY_CheckWithUnifiedHavocs");

    //    return result;
    //}

    //static protected bool CheckNonConflict(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch)
    //{
    //    AtomicBlock thisBlock = thisTPGen.APLBlock as AtomicBlock;
    //    AtomicBlock thatBlock = thatTPGen.APLBlock as AtomicBlock;

    //    Expr leftWP = ComputeInterleavedGatePredicate(thisTPGen, thatTPGen);
    //    Expr rightWP = ComputeInterleavedGatePredicate(thatTPGen, thisTPGen);

    //    // this check is necessary since left may go wrong but right may block, even though they do not mc
    //    Expr condition = Expr.Imp(Expr.And(inv, rightWP), leftWP);

    //    bool result = false;

    //    if (Prover.GetInstance().CheckValid(condition, ch))
    //    {
    //        result = !CheckConflict(proofState, thisBlock, thatBlock);
    //    }

    //    if (result) Statistics.Count("MOVER_CHECK_BY_CheckNonConflict");

    //    return result;
    //}

    //static protected bool CheckConflict(ProofState proofState, AtomicBlock thisBlock, AtomicBlock thatBlock)
    //{
    //    Set<GlobalVariable> thisReadSet = Util.FilterGlobalVariables(thisBlock.ComputeReadSet());
    //    Set<GlobalVariable> thisWriteSet = Util.FilterGlobalVariables(thisBlock.ComputeWriteSet());

    //    Set<GlobalVariable> thatReadSet = Util.FilterGlobalVariables(thatBlock.ComputeReadSet());
    //    Set<GlobalVariable> thatWriteSet = Util.FilterGlobalVariables(thatBlock.ComputeWriteSet());

    //    return (thisReadSet.Intersection(thatWriteSet).Count > 0)
    //           || (thisWriteSet.Intersection(thatReadSet).Count > 0)
    //           || (thisWriteSet.Intersection(thatWriteSet).Count > 0);
    //}


    //static protected bool CheckLeftUnSat(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch)
    //{
    //    Expr rightWP = ComputeInterleavedGatePredicate(thatTPGen, thisTPGen, false);

    //    Expr leftPred = ComputeInterleavedTransitionPredicate(thisTPGen, thatTPGen, false);

    //    Expr condition = Logic.And(inv, rightWP, leftPred);

    //    bool result = Prover.GetInstance().CheckUnSat(condition, ch);

    //    if (result) Statistics.Count("MOVER_CHECK_BY_CheckLeftUnSat");

    //    return result;
    //}


    //static public Expr ComputeInterleavedGatePredicate(TPGenerator thisTPGen, TPGenerator thatTPGen)
    //{
    //    thisTPGen.Next = thatTPGen;
    //    thatTPGen.Next = null;

    //    TPGenOptions options = TPGenOptions.ComputeWPre(Expr.True);

    //    return thisTPGen.Compute(options);
    //}

    //static public Expr ComputeInterleavedGatePredicateWoutQuant(TPGenerator thisTPGen, TPGenerator thatTPGen)
    //{
    //    thisTPGen.Next = thatTPGen;
    //    thatTPGen.Next = null;

    //    return thisTPGen.Compute(TPGenOptions.ComputeWPreWoutQuant(Expr.True));
    //}

    //static public Expr ComputeInterleavedGatePredicateWithUnifiedHavocs(TPGenerator thisTPGen, TPGenerator thatTPGen)
    //{
    //    thisTPGen.Next = thatTPGen;
    //    thatTPGen.Next = null;

    //    TPGenOptions options = TPGenOptions.ComputeWPre(Expr.True);
    //    options.unifyHavocs = true;
    //    options.useQuant = false;
    //    options.singleHavoc = false;

    //    return thisTPGen.Compute(options);
    //}

    //static public Expr ComputeInterleavedTransitionPredicate(TPGenerator thisTPGen, TPGenerator thatTPGen, bool singleHavoc)
    //{
        
    //    thisTPGen.Next = thatTPGen;
    //    thatTPGen.Next = null;

    //    TPGenOptions options = TPGenOptions.ComputeTPred;
    //    options.singleHavoc = singleHavoc;

    //    return thisTPGen.Compute(options);
    //}

    //static public Expr ComputeInterleavedTransitionPredicateWoutQuant(TPGenerator thisTPGen, TPGenerator thatTPGen)
    //{
        
    //    thisTPGen.Next = thatTPGen;
    //    thatTPGen.Next = null;

    //    return thisTPGen.Compute(TPGenOptions.ComputeTPredWoutQuant);
    //}

    //static public Expr ComputeInterleavedTransitionPredicateWithUnifiedHavocs(TPGenerator thisTPGen, TPGenerator thatTPGen)
    //{
    //    thisTPGen.Next = thatTPGen;
    //    thatTPGen.Next = null;

    //    TPGenOptions options = TPGenOptions.ComputeTPred;
    //    options.unifyHavocs = true;
    //    options.useQuant = false;
    //    options.singleHavoc = false;

    //    return thisTPGen.Compute(options);
    //}

    //static public Expr ComputeInterleavedTransitionPredicateNoErrorWoutQuant(TPGenerator thisTPGen, TPGenerator thatTPGen)
    //{
        
    //    thisTPGen.Next = thatTPGen;
    //    thatTPGen.Next = null;

    //    return thisTPGen.Compute(TPGenOptions.ComputeTPredNoErrorWoutQuant);
    //}

} // end class MoverTypeChecker

// this class visits all statements and computes movers of compound statements
public class MoverVisitor : StmtVisitor
{
    internal IDictionary<string, MoverType> summaries;
    // internal Stack<string> callStack;
    internal ProcedureState procState;
    internal bool inAtom = false;

    public MoverVisitor()
    {

    }

    public void Compute(ProcedureState proc)
    {
        this.procState = proc;
        this.callStack = new Stack<string>();
        this.callStack.Push(proc.Name);
        this.summaries = new Dictionary<string, MoverType>();
        this.inAtom = false;
        VisitStmtList(proc.Body);
        Debug.Assert(callStack.Count == 1 && callStack.Pop() == proc.Name);
    }

    public void Compute(ProcedureState proc, StmtList stmt)
    {
        this.procState = proc;
        this.callStack = new Stack<string>();
        this.callStack.Push(proc.Name);
        this.summaries = new Dictionary<string, MoverType>();
        this.inAtom = false;
        VisitStmtList(stmt);
        Debug.Assert(callStack.Count == 1 && callStack.Pop() == proc.Name);
    }

    public override StmtList VisitStmtList(StmtList stmt)
    {
        base.VisitStmtList(stmt);

        MoverType current = stmt.BigBlocks[0].Mover;
        for (int i = 1; i < stmt.BigBlocks.Count; ++i)
        {
            current = MoverType.ComposeSeq(current, stmt.BigBlocks[i].Mover);
        }
        stmt.Mover = current;

        // if in atom, then it must be at least non-mover
        if (this.inAtom && stmt.Mover == null) 
            stmt.Mover = MoverType.NonMover;

        return stmt;
    }

    public override BigBlock VisitBigBlock(BigBlock bb)
    {
        base.VisitBigBlock(bb);

        MoverType current = MoverType.BothMover;
        if (bb.ec != null)
        {
            current = bb.ec.Mover;
        }
        bb.Mover = current == null ? null : current.Clone();

        // if in atom, then it must be at least non-mover
        if (this.inAtom && bb.Mover == null)
            bb.Mover = MoverType.NonMover;

        return bb;
    }

    public override IfCmd VisitIfCmd(IfCmd ifCmd)
    {
        base.VisitIfCmd(ifCmd);

        MoverType current = ifCmd.thn.Mover;
        if (ifCmd.elseBlock != null)
        {
            current = MoverType.ComposeCho(current, ifCmd.elseBlock.Mover);
        }
        Debug.Assert(ifCmd.elseIf == null);
        ifCmd.Mover = current == null ? null : current.Clone();

        // if in atom, then it must be at least non-mover
        if (this.inAtom && ifCmd.Mover == null)
            ifCmd.Mover = MoverType.NonMover;

        return ifCmd;
    }

    public override WhileCmd VisitWhileCmd(WhileCmd whileCmd)
    {
        base.VisitWhileCmd(whileCmd);

        MoverType current = MoverType.ComposeLoop(whileCmd.Body.Mover);
        whileCmd.Mover = current == null ? null : current.Clone();

        // if in atom, then it must be at least non-mover
        if (this.inAtom && whileCmd.Mover == null)
            whileCmd.Mover = MoverType.NonMover;

        return whileCmd;
    }

    public override ForeachStmt VisitForeachStmt(ForeachStmt foreachStmt)
    {
        base.VisitForeachStmt(foreachStmt);

        MoverType current = MoverType.ComposeLoop(foreachStmt.Body.Mover);
        foreachStmt.Mover = current == null ? null : current.Clone();

        // if in atom, then it must be at least non-mover
        if (this.inAtom && foreachStmt.Mover == null)
            foreachStmt.Mover = MoverType.NonMover;

        return foreachStmt;
    }

    public override ParallelStmt VisitParallelStmt(ParallelStmt parStmt)
    {
        base.VisitParallelStmt(parStmt);

        MoverType current = parStmt.bodies[0].Mover;
        for (int i = 1; i < parStmt.bodies.Count; ++i)
        {
            current = MoverType.ComposePar(current, parStmt.bodies[i].Mover);
        }
        parStmt.Mover = current == null ? null : current.Clone();

        // if in atom, then it must be at least non-mover
        if (this.inAtom && parStmt.Mover == null)
            parStmt.Mover = MoverType.NonMover;

        return parStmt;
    }

    public override CobeginStmt VisitCobeginStmt(CobeginStmt cobgn)
    {
        base.VisitCobeginStmt(cobgn);

        MoverType current = cobgn.bodies[0].Mover;
        for (int i = 1; i < cobgn.bodies.Count; ++i)
        {
            current = MoverType.ComposePar(current, cobgn.bodies[i].Mover);
        }
        cobgn.Mover = current == null ? null : current.Clone();

        // if in atom, then it must be at least non-mover
        if (this.inAtom && cobgn.Mover == null)
            cobgn.Mover = MoverType.NonMover;

        return cobgn;
    }

    public override AtomicStmt VisitAtomicStmt(AtomicStmt atomicStmt)
    {
        if (!(atomicStmt is StraightAtomicStmt) && atomicStmt.isCompound)
        {
            bool oldInAtom = this.inAtom;
            this.inAtom = true;

            // dive into the atom
            base.VisitAtomicStmt(atomicStmt);
            
            this.inAtom = oldInAtom;

            atomicStmt.Mover = atomicStmt.body.Mover == null ? MoverType.NonMover : atomicStmt.body.Mover;
        }
        return atomicStmt;
    }

    public override CallStmt VisitCallStmt(CallStmt callStmt)
    {
        // no need to visit the cmd itself
        //base.VisitCallStmt(callStmt);

        MoverType current;
        string calleeName = callStmt.CalleeName;
        if (summaries.ContainsKey(calleeName))
        {
            current = summaries[calleeName] == null ? null : summaries[calleeName].Clone();
        }
        else
        {
            // go deep into the procedure
            // if recursive call, then only use the mover in the procedure state
            ProcedureState calleeState = ProofState.GetInstance().GetProcedureState(calleeName);
            if (callStack.Contains(calleeName))
            {
                // recursion is detected
                current = calleeState.Mover == null ? null : calleeState.Mover.Clone(); 
            }
            else
            {
                callStack.Push(calleeName);

                VisitStmtList(calleeState.Body);

                string name = callStack.Pop();
                Debug.Assert(name == calleeName);

                current = calleeState.Body.Mover;
                summaries.Add(calleeName, current  == null ? null : current.Clone());
            }
        }
        callStmt.Mover = current == null ? null : current.Clone();

        // if in atom, then it must be at least non-mover
        if (this.inAtom && callStmt.Mover == null)
            callStmt.Mover = MoverType.NonMover;

        return callStmt;
    }
}
} // end namespace QED
