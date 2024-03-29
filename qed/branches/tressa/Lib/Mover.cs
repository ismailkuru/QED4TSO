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

public class FixMoverCommand : ProofCommand
{
	bool right;
	bool left;
	string blocklabel;

	public FixMoverCommand(bool r, bool l, string label)
		: base("fixmover")
	{
		this.right = r;
		this.left = l;
		this.blocklabel = label;
	
		desc = "fixmover ";
		if(right) desc += "r";
		if(left) desc += "l";
		desc += " " + blocklabel;
	}

    public static string Usage()
    {
        return "fixmover l|r atomicBlockLabel@procedureName";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("fixmover"))
        {
            bool r = false;
            bool l = false;
            string rl = parser.NextAsString();
            r = rl.IndexOf("r") >= 0;
            l = rl.IndexOf("l") >= 0;

            string label = parser.NextAsString();

            return new FixMoverCommand(r, l, label);
        }
        return null;
    }
	
	override public bool Run(ProofState proofState) {
	
		AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(blocklabel);
        if (atomicBlock == null) return false;

		if(right) {
			atomicBlock.Mover.Right = true;
			atomicBlock.Mover.RightFixed = true;
		}	
		
		if(left) {
			atomicBlock.Mover.Left = true;
			atomicBlock.Mover.LeftFixed = true;
		}		
		
		return false;
	}
	
} // end class FixMoverCommand

/***************************************************************************/
/***************************************************************************/
  
public class MoverCommand : ProofCommand
{
	string label;
    bool isproc;
    StringBuilder strb;
    bool printReport;

	public MoverCommand(string lbl, bool isproc, bool print)
		: base("mover")
	{
		this.label = lbl;
        this.isproc = isproc;
        this.strb = null; // initialized later in Run
        this.printReport = print;
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

    public string Report
    {
        get
        {
            return this.strb.ToString();
        }
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
                    atomicBlocks.AddRange(procState.AtomicBlocks);
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

        this.strb = new StringBuilder();
        DoRun(proofState, atomicBlocks, this.strb);

        if (this.printReport)
        {
            Output.AddLine("Mover Report");
            Output.AddLine(this.Report);
        }

        return false;
	}

    static public void DoRun(ProofState proofState, List<AtomicBlock> atomicBlocks, StringBuilder strb)
    {
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

            strb.Append(checker.Report);
        }

        proofState.LastMoverReport = "Mover Report\n" + strb.ToString();

        CommandLineOptions.Clo.RestartProverPerVC = tmp;
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

        StringBuilder strb = new StringBuilder();
        foreach (MoverTypeChecker checker in checkers)
        {
            checker.Join();

            Output.AddLine("Checked mover type of " + checker.AtomicBlock.UniqueLabel);

            strb.Append(checker.Report);
        }

        proofState.LastMoverReport = "Mover Report\n" + strb.ToString();

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
    // for tressa
    public bool isLeft { get { return !isRight; } }

    public MoverCheck(AtomicBlock thisB, AtomicBlock thatB, bool isr)
    {
        this.thisBlock = thisB;
        this.thatBlock = thatB;
        this.isRight = isr;
        this.wpOK = this.xpOK = false;
    }

    public override string ToString()
    {
        StringBuilder strb = new StringBuilder();
        strb.Append("Failed ").Append(isRight ? "RightMover" : "LeftMover").Append(" check: ").Append(thisBlock.UniqueLabel).Append(" -> ").Append(thatBlock.UniqueLabel).Append(" (").Append("Failed checks: ").Append(!wpOK ? "WP " : "").Append(!xpOK ? "XP" : "").Append(")");
        return strb.ToString();
    }
}

public class MoverTypeChecker
{
    AtomicBlock atomicBlock;

    ProofState proofState;

    MoverType result;

    Thread thread;

    List<AtomicBlock> allBlocks;

    Checker checker;

    List<MoverCheck> mcs;

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

    public string Report
    {
        get
        {
            StringBuilder strb = new StringBuilder();
            foreach (MoverCheck mc in mcs)
            {
                strb.AppendLine(mc.ToString());
            }
            return strb.ToString();
        }
    }

    static MoverTypeChecker() {
        // set up mover testers
        moverTesters = new List<MoverTestFunc>();

        //moverTesters.Add(new MoverTestFunc(MoverTypeChecker.CheckTrapPred));
        //moverTesters.Add(new MoverTestFunc(MoverTypeChecker.CheckLeftUnSat));
        // for tressa
        // moverTesters.Add(new MoverTestFunc(MoverTypeChecker.CheckWithTressa));
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
        TPGenerator tpGen = new TPGenerator(this.atomicBlock); // hide:false

        this.atomicBlock.Mover = this.result = Check(this.proofState, tpGen);        
    }

    public MoverType Check(ProofState proofState, TPGenerator thisTPGen)
    {
        this.checker = Prover.GetInstance().AcquireChecker();

        this.mcs = new List<MoverCheck>();

        AtomicBlock thisBlock = thisTPGen.APLBlock as AtomicBlock;

        this.result = thisBlock.Mover.Clone();
        this.result.MakeBothMover();

        for (int j = 0, n = allBlocks.Count; j < n && !this.result.None; ++j)
        {
            AtomicBlock thatBlock = allBlocks[j];
            TPGenerator thatTPGen = new TPGenerator(thatBlock, true);

            TypeCheckMover(proofState, thisTPGen, thatTPGen, this.result);
        }

        Prover.GetInstance().ReleaseChecker(this.checker);

        proofState.LastMoverReport = this.Report;

        return this.result;
    }

    protected void TypeCheckMover(ProofState proofState, TPGenerator thisTPGen, TPGenerator thatTPGen, MoverType mover)
    {
        AtomicBlock thisBlock = thisTPGen.APLBlock as AtomicBlock;
        AtomicBlock thatBlock = thatTPGen.APLBlock as AtomicBlock;

        // check right mover
        if (!mover.RightFixed)
        {
            if (mover.Right)
            {
                bool success = DoCheck(true, proofState, thisTPGen, thatTPGen);
                if (!success)
                {
                        mover.Right = false;
                }
            }
        }

        // check left mover
        if (!mover.LeftFixed)
        {
            if (mover.Left)
            {

                bool success = DoCheck(false, proofState, thatTPGen, thisTPGen);
                if (!success)
                {
                    mover.Left = false;
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
                // for tressa; the only effect of tressa in mover check is reduced to checking whether the tressa claim is strengthened
                TPGenOptions thisOptions = TPGenOptions.ComputeSPost(inv); // this inv might be redundant
                thisOptions.unifyHavocs = false;
                thisOptions.useQuant = true;

                thisTPGen.Next = thatTPGen; thatTPGen.Next = null;
                Expr thisSP = thisTPGen.ComputeSP(thisOptions, inv);

                TPGenOptions thatOptions = TPGenOptions.ComputeSPost(inv); // this inv might be redundant
                thatOptions.unifyHavocs = false;
                thatOptions.useQuant = true;

                thatTPGen.Next = thisTPGen; thisTPGen.Next = null;
                Expr thatSP = thatTPGen.ComputeSP(thatOptions, inv);

                bool tressa_sanity;
                tressa_sanity = Prover.GetInstance().CheckValid(Expr.Imp(thatSP, thisSP)); 
                
                if (tressa_sanity) // prior to tressa; success was set to true for all values of tressa_sanity
                {
                    success = true;
                    break;
                }
            }
        }
        // this takes the mc of the last mover check function
        if (!success) mcs.Add(mc);

        //thisTPGen.AtomicBlock.procState.DisableCondAssertsToCheck();
        //thatTPGen.AtomicBlock.procState.DisableCondAssertsToCheck();

        return success;
    }

    // for tressa
    static protected bool CheckWithTressa(ProofState proofState, Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, Checker ch, MoverCheck mc)
    {
        if (Logic.MoverCheck(inv, thisTPGen, thatTPGen, mc))
        {
            Statistics.Count("MOVER_CHECK_BY_CheckWithTressa");
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


public class MoverType
{

    public bool RightFixed = false;
    public bool LeftFixed = false;

    public bool Right = false;
    public bool Left = false;
    public bool None
    {
        get
        {
            return ((!Right) && (!Left));
        }
    }

    public bool Both
    {
        get
        {
            return ((Right) && (Left));
        }
    }

    public void MakeBothMover()
    {
        this.Right = true;
        this.Left = true;
    }

    private MoverType(bool right, bool left)
    {
        this.RightFixed = false;
        this.LeftFixed = false;
        this.Right = right;
        this.Left = left;
    }

    public static MoverType RightMover { get { return new MoverType(true, false); } }
    public static MoverType LeftMover { get { return new MoverType(false, true); } }
    public static MoverType BothMover { get { return new MoverType(true, true); } }
    public static MoverType NonMover { get { return new MoverType(false, false); } }

    override public string ToString()
    {
        if (!Right && !Left) return "N";
        if (Right && Left) return "B";
        if (Right && !Left) return "R";
        return "L";
    }

    public static MoverType Parse(string s)
    {
        switch (s)
        {
            case "B": return BothMover;
            case "N": return NonMover;
            case "R": return RightMover;
            case "L": return LeftMover;
        }
        Debug.Assert(false, "Incorrect string for mover identification!");
        return null;
    }

    public override bool Equals(object o)
    {
        if (o == null)
            return false;
        MoverType mtype = o as MoverType;
        if (mtype == null)
            return false;
        return ((mtype.Left == this.Left) && (mtype.Right == this.Right));
    }

    public static MoverType ComposeSeq(MoverType fmover, MoverType smover)
    {
        if (fmover == null || smover == null)
        {
            return null;
        }

        MoverType result = null;

        if (fmover.None)
        {
            if (smover.Left)
            {
                result = MoverType.NonMover;
            }
        }
        else if (fmover.Both && smover.Both)
        {
            result = MoverType.BothMover;
        }
        else if (fmover.Right)
        {
            if (smover.Left || smover.None)
            {
                result = MoverType.NonMover;
            }
            else if (smover.Right)
            {
                result = MoverType.RightMover;
            }
        }
        else if (fmover.Left)
        {
            if (smover.Left)
            {
                result = MoverType.LeftMover;
            }
        }

        return result;
    }

    public static MoverType ComposeCho(MoverType fmover, MoverType smover)
    {
        if (fmover == null || smover == null)
        {
            return null;
        }

        MoverType result = null;

        if (fmover == smover)
        {
            result = fmover;
        }
        else
        {
            result = MoverType.NonMover;
        }

        return result;
    }

    public MoverType Clone()
    {
        MoverType mover = new MoverType(this.Right, this.Left);
        mover.LeftFixed = this.LeftFixed;
        mover.RightFixed = this.RightFixed;
        return mover;
    }

    internal static MoverType FromEnum(AtomicStmt.Mover mover)
    {
        switch (mover)
        {
            case AtomicStmt.Mover.None:
                return MoverType.NonMover;
            case AtomicStmt.Mover.Left:
                return MoverType.LeftMover;
            case AtomicStmt.Mover.Right:
                return MoverType.RightMover;
            case AtomicStmt.Mover.Both:
                return MoverType.BothMover;
        }
        Debug.Assert(false);
        return null;
    }

    internal AtomicStmt.Mover ToEnum()
    {
        if (!Left && !Right)
        {
            return AtomicStmt.Mover.None;
        }
        else if (Left && !Right)
        {
            return AtomicStmt.Mover.Left;
        }
        else if (!Left && Right)
        {
            return AtomicStmt.Mover.Right;
        }
        return AtomicStmt.Mover.Both;

    }
}

} // end namespace QED
