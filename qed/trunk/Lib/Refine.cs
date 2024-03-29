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
    using QInvariant = InvariantStore.QInvariant;
  

public abstract class RefineCommand : ProofCommand
{
	protected RelyGuarantee rg;

    protected Expr inv;

    public VariableSeq auxVars;

    public StringSeq auxVarNames;
	
    protected Variable errVar;

    protected bool restartProver;

    public enum Inference {Assignments, Assertions, Both};

    protected Inference inference;

    //protected Dictionary<ProcedureState,Expr> preCondMap;
	
	public RefineCommand() : base("refine") {
		
        //this.preCondMap = new Dictionary<ProcedureState,Expr>();
        this.auxVarNames = new StringSeq();

        this.inference = Inference.Both;
	}	
	
    //override public bool Run(ProofState proofState) {
    //    if (inference == Inference.Both)
    //    {
    //        InferAssertions(proofState);
    //    }
    //    else
    //    {
    //        InferAssignments(proofState);
    //    }
    //    return false;		
    //}
	
	override public bool Run(ProofState proofState)
    {
        StartRefine(proofState);

        if (!CheckAnnotateTransitions(proofState))
        {
            EndRefineFail(proofState);

            Output.AddLine("Failed to annotate transitions !");
            
            return false;
        }
		
        // TODO: enable later
        if (!CheckValidity(proofState))
        {
            EndRefineFail(proofState);

            Output.AddError("ERROR: Validity check for the refine command failed");

            return false;
        }
        else
        {
            Output.AddLine("Validity check succeeded");
        }

        if (!CheckAddInvariant(proofState))
        {
            EndRefineFail(proofState);

            Output.AddLine("Failed to introduce the invariant!");
            
            return false;
        }

		AnnotateProgram(proofState);
				
		EndRefineSuccess(proofState);

        Output.AddLine("Annotated the program successfully");

        return false;
    }

    protected bool CheckAddInvariant(ProofState proofState)
    {
        if (!InvariantCommand.DoRun(proofState, new QInvariant(null, null, this.inv)))
        {
            return false;
        }
        return true;
    }

    protected virtual Set<Block> InferAssignments(ProofState proofState, AtomicBlock atomicBlock, Expr assertion, AssignCmd assignCmd)
    {
        ProcedureState procState = atomicBlock.procState;
        Expr trans = atomicBlock.TransitionPredicate;
        Expr pcprime = procState.GetPrimedExpr(procState.pcExpr);
        Expr invs = proofState.InvariantForProc(procState);
               
        Set<Block> blockToAnnotate = new Set<Block>();

        Set<Block> exitBlocks = atomicBlock.ExitBlocks;
        foreach (Block exitBlock in exitBlocks)
        {
            Expr pcExpr;

            if (exitBlock.TransferCmd is ThrowCmd)
            {
                ThrowCmd thrw = exitBlock.TransferCmd as ThrowCmd;
                pcExpr = Expr.Eq(pcprime, thrw.ex);                
            }
            else if (exitBlock.TransferCmd is ReturnCmd)
            {
                pcExpr = Expr.Eq(pcprime, proofState.exReturnExpr);
            }
            else
            {
                Debug.Assert(exitBlock.TransferCmd is GotoCmd);
                pcExpr = Expr.Eq(pcprime, proofState.exSkipExpr);
            }

            Expr condition = Expr.Imp(Logic.And(invs, trans, pcExpr), assertion);
            if (Prover.GetInstance().CheckValid(condition))
            {
                blockToAnnotate.Add(exitBlock);
            }
        }

        if(blockToAnnotate.Count > 0) {
            StmtDuplicator duplicator = new StmtDuplicator();
            foreach (Block b in blockToAnnotate)
            {
                CodeTransformations.InstrumentExit(atomicBlock.parent.body, new CmdSeq(duplicator.Visit(assignCmd) as Cmd), true, b.Label);
                
               // b.Cmds.Add(duplicator.Visit(assignCmd) as Cmd);
            }

            foreach (AssignLhs lhs in assignCmd.Lhss)
            {
                procState.CheckAddModifies(lhs.DeepAssignedVariable, true);
            }
        }

        return blockToAnnotate;
    }
    
    abstract protected Expr ComputeTransitionAnnotation(ProofState proofState);

    virtual protected void StartRefine(ProofState proofState)
    {
        this.auxVars = new VariableSeq();

        restartProver = CommandLineOptions.Clo.RestartProverPerVC;
        CommandLineOptions.Clo.RestartProverPerVC = true;

        Qoogie2Boogie.AssumeFalseAtLoops = false;
        Qoogie2Boogie.CheckPc = true;
    }

    virtual protected void AnnotateProgram(ProofState proofState)
    {
        this.errVar = AuxIntroCommand.DoRun(proofState, "errx", BasicType.Bool);

        IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
        IdentifierExpr perrExpr = proofState.GetPrimedExpr(errExpr.Decl);

        // update rely so that error does not change
        this.rg.Rely = Expr.And(this.rg.Rely, Expr.Eq(errExpr, perrExpr));

        // preserves transitions
        Expr preservesAux = Expr.True;
        foreach (Variable auxVar in auxVars)
        {
            IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVar);
            IdentifierExpr auxPrimeExp = ProofState.GetInstance().GetPrimedExpr(auxVar);

            preservesAux = Expr.And(preservesAux, Expr.Eq(auxExp, auxPrimeExp));
        }

        Expr preservesError = Expr.Eq(errExpr, perrExpr);

        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            if ((!procState.IsReduced) || procState.IsPublic)
            {
                //-------------------------
                // control blocks preserve aux var, atomic blocks are annotated below
                // TODO: call blocks take how aux var is modified from the procedure                
                foreach (APLBlock aplBlock in procState.Atoms)
                {
                    if (aplBlock is ControlBlock)
                    {
                        aplBlock.PushTransition(preservesAux);
                        aplBlock.PushTransition(preservesError);
                    }
                    else if (aplBlock is CallBlock)
                    {
                        aplBlock.PushTransition(preservesError);
                    }
                }
            }
        }
    }

    protected void EndRefine(ProofState proofState)
    {
        Qoogie2Boogie.AssumeFalseAtLoops = true;
        Qoogie2Boogie.CheckPc = false;

        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            procState.MarkAsTransformed();
        }

        foreach (Variable auxVar in auxVars)
        {
            proofState.MakeNonAuxVar((GlobalVariable)auxVar);
        }

        CommandLineOptions.Clo.RestartProverPerVC = restartProver;
    }

    virtual protected void EndRefineSuccess(ProofState proofState)
    {
        EndRefine(proofState);
        
        proofState.RemoveAuxVar((GlobalVariable)errVar);
    }

    virtual protected void EndRefineFail(ProofState proofState)
    {
        EndRefine(proofState);

        proofState.LastErrorTrace = rg.LastErrorTrace;
    }
	
    //virtual protected Expr PreCondForProc(ProcedureState procState) {
    //    return preCondMap.ContainsKey(procState) ? preCondMap[procState] : Expr.True;
    //}
	
    //virtual protected void AddPreCondForProc(ProcedureState procState, Expr expr) {
    //    if(preCondMap.ContainsKey(procState)) {
    //        preCondMap[procState] = Expr.And(preCondMap[procState], expr);
    //    } else {
    //        preCondMap[procState] = expr;
    //    }
    //}

    protected bool DoAnnotateProc(ProofState proofState, ProcedureState procState, Expr formula)
    {
        foreach (APLBlock aplBlock in procState.Atoms)
        {
            aplBlock.PushTransition(formula);

            //check invariant preservation
            AtomicBlock atomicBlock = aplBlock as AtomicBlock;
            if (atomicBlock != null)
            {
                if (!atomicBlock.IsInvariant(proofState.Invariant))
                {
                    // error
                    Output.AddError("Could not annotate the block (violates the invariant):" + atomicBlock.UniqueLabel);
                    atomicBlock.PopTransition();
                    return false;
                }
            }
        }
        return true;
    }

    protected bool CheckAnnotateTransitions(ProofState proofState)
    {
        Expr annotExpr = ComputeTransitionAnnotation(proofState);
        proofState.ResolveTypeCheckExpr(annotExpr, false);

        // IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVar);

        bool result = true;

        // first add regular transitions
        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            if ((!procState.IsReduced) || procState.IsPublic)
            {
                Output.LogLine("Refine: Annotating procedure: " + procState.impl.Name);

                procState.ForceComputeAtomicBlocks();

                // annotate blocks with the transition predicate
                if (!DoAnnotateProc(proofState, procState, annotExpr))
                {
                    result = false;
                    break;
                }
            }
        }

        return result;
    }

    protected bool CheckValidity(ProofState proofState)
    {
        bool result = true;

        // first add regular transitions
        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            if ((!procState.IsReduced) || procState.IsPublic)
            {
                Output.LogLine("Refine: Checking procedure: " + procState.impl.Name);
                
                Expr precond = Expr.True; // Expr.And(PreCondForProc(procState), Expr.Not(errExpr));
                Expr postcond = Expr.True;
                if (!rg.CheckProcedure(proofState, procState, precond, postcond))
                {
                    result = false;
                    Output.AddError("Procedure failed: " + procState.impl.Name);
                    break;
                }
            }
        }

        return result;

        //// now add transitions for preconditions
        //Expr assertAux = Expr.Eq(auxExp, ProofState.GetInstance().tidExpr);

        //foreach(ProcedureState procState in proofState.procedureStates.Values) {
        //    if((!procState.IsReduced) || procState.IsPublic) {
        //        Expr inv = proofState.InvariantForProc(procState);
        //        if(Prover.GetInstance().CheckValid(Expr.Imp(Expr.And(inv, procState.Requires), this.syncPredicate))) {

        //            AddPreCondForProc(procState, assertAux);

        //            // add assertion to call blocks
        //            foreach(CallBlock callBlock in procState.CallerBlocks) {
        //                Expr labeledAssertAux = LabeledExprHelper.NegAuxAssert(callBlock, assertAux);
        //                Expr labeledAnnot = Expr.Or(Expr.And(assertAux, Expr.Eq(errExpr, perrExpr)),
        //                                             Expr.And(labeledAssertAux, Expr.Eq(perrExpr, Expr.True)));
        //                callBlock.TransitionPredicate = Expr.And(Expr.And(callBlock.RecomputeTransitionPredicate(), annotExpr), labeledAnnot);
        //            }
        //        }
        //    }
        //}

        //bool result = true;

        //// finally check
        //foreach(ProcedureState procState in proofState.procedureStates.Values) {
        //    if((!procState.IsReduced) || procState.IsPublic) {
        //        // now check
        //        Expr precond = Expr.Not(errExpr); // Expr.And(PreCondForProc(procState), Expr.Not(errExpr));
        //        Expr postcond = Expr.Not(perrExpr);
        //        if(!rg.CheckProcedure(proofState, procState, precond, postcond)) {
        //            result = false;
        //            break;
        //        }
        //    }
        //}

        //return result;
    }
	
	virtual protected Set<AtomicBlock> AnnotateProcedure(ProofState proofState, ProcedureState procState, AnnotationSet annotationSet) {
		
        //Expr annotExpr = ComputeTransitionAnnotation();

        IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
        IdentifierExpr perrExpr = proofState.GetPrimedExpr(errExpr.Decl);
		
		bool done = false;

        annotationSet.AnnotatePreds();

		while(!done) {
		
			//foreach(AtomicBlock atomicBlock in procState.AtomicBlocks) {
            //    // atomicBlock.RecomputeTransitionPredicate(TPGenOptions.ComputeTPred);
            //    atomicBlock.PushTransition(annotExpr);	// this is not pop-ed					
            //}
			
			// now check
            Expr precond = Expr.Not(errExpr); //  Expr.And(PreCondForProc(procState), Expr.Not(errExpr));
            Expr postcond = Expr.Not(perrExpr);
			if(!rg.CheckProcedure(proofState, procState, precond, postcond)) {
				// remove the failed assertions
				annotationSet.Disable(Prover.GetInstance().GetErrorLabels());
			} else {
				done = true;
			} // end if
            Output.AddLine("Progress...");
		} // end while

        VariableSeq modifiedVars = annotationSet.GetModifiedVars();
        foreach (Variable modVar in modifiedVars)
        {
            procState.CheckAddModifies(modVar, true);
        }

        // now do code annotation
        annotationSet.AnnotateCodes();

        return annotationSet.GetAnnotatedBlocks();
	}
	
} // end class RefineCommand

public class RefineMutexCommand : RefineCommand
{
    public Expr syncPredicate;

    public RefineMutexCommand(Expr predicate, string auxname)
        : base()
    {
        this.syncPredicate = predicate;
        this.auxVarNames.Add(auxname);

        desc = "mutex " + auxname + " " + Output.ToString(this.syncPredicate);
    }

    public static string Usage()
    {
        return "mutex variableName predicateFormula";
    }

    // TODO: make other command classes like this
    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("mutex"))
        {
            string aux = parser.NextAsString();
            Expr pred = parser.RestAsExpr();
            return new RefineMutexCommand(pred, aux);
        }
        return null;
    }

    override protected void AnnotateProgram(ProofState proofState)
    {
        base.AnnotateProgram(proofState);

        IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
        IdentifierExpr perrExpr = proofState.GetPrimedExpr(errExpr.Decl);

        IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVars[0]);
        IdentifierExpr auxPrimeExp = ProofState.GetInstance().GetPrimedExpr(auxVars[0]);

        Expr assertAux = Expr.Eq(auxExp, ProofState.GetInstance().tidExpr);
        Expr assertAuxPrime = Expr.Eq(auxPrimeExp, ProofState.GetInstance().tidExpr);
        Expr assertZero = Expr.Eq(auxExp, Expr.Literal(0));
        Expr assertNotZero = Expr.Neq(auxExp, Expr.Literal(0));
        Expr assertZeroPrime = Expr.Eq(auxPrimeExp, Expr.Literal(0));

        AnnotationSet annotationSet = new AnnotationSet(errExpr, perrExpr);
        Set<AtomicBlock> annotatedAuxBlocks = new Set<AtomicBlock>();
        Set<AtomicBlock> annotatedAuxAssignBlocks = new Set<AtomicBlock>();
        Set<AtomicBlock> annotatedZeroAssignBlocks = new Set<AtomicBlock>();
        Set<AtomicBlock> annotatedZeroBlocks = new Set<AtomicBlock>();
        Set<AtomicBlock> annotatedNotZeroBlocks = new Set<AtomicBlock>();

        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            if ((!procState.IsReduced) || procState.IsPublic)
            {
                Output.LogLine("Refine: Annotating procedure: " + procState.impl.Name);

                // infer assignments
                foreach (AtomicBlock atomicBlock in procState.AtomicBlocks)
                {
                    // acquires
                    Set<Block> acquireBlocks = InferAssignments(proofState, atomicBlock, Expr.And(assertZero, assertAuxPrime), AssignCmd.SimpleAssign(Token.NoToken, auxExp, ProofState.GetInstance().tidExpr));
                    if (acquireBlocks.Count > 0)
                    {
                        annotatedAuxAssignBlocks.Add(atomicBlock);
                    }

                    // releases
                    Set<Block> releaseBlocks = InferAssignments(proofState, atomicBlock, assertZeroPrime, AssignCmd.SimpleAssign(Token.NoToken, auxExp, LiteralExpr.Literal(0)));
                    if (releaseBlocks.Count > 0)
                    {
                        annotatedZeroAssignBlocks.Add(atomicBlock);

                        // assert that the lock is held by the current thread or not held
                        AssertCmd assertCmd = new AssertCmd(Token.NoToken, Expr.Or(assertAux, assertZero));
                        atomicBlock.InstrumentEntry(new CmdSeq(assertCmd));
                    }
                }



                //----------------------------------------------------------------------
                Output.AddLine("Adding annotation for \"entry assert aux == tid\".");
                annotationSet.Clear();
                annotationSet.Init(procState.AtomicBlocks, assertAux, new AssertCmd(Token.NoToken, assertAux), true);
                annotatedAuxBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                //----------------------------------------------------------------------
                Output.AddLine("Adding annotation for \"entry assert aux == 0\".");
                annotationSet.Clear();
                annotationSet.Init(procState.AtomicBlocks, annotatedAuxBlocks, assertZero, new AssertCmd(Token.NoToken, assertZero), true);
                annotatedZeroBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                //----------------------------------------------------------------------
                Output.AddLine("Adding annotation for \"entry assert aux != 0\".");
                annotationSet.Clear();
                annotationSet.Init(procState.AtomicBlocks, annotatedAuxBlocks.Union(annotatedZeroBlocks), assertNotZero, new AssertCmd(Token.NoToken, assertNotZero), true);
                annotatedNotZeroBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                //----------------------------------------------------------------------
                //Output.AddLine("Adding annotation for \"exit assign aux := tid\".");
                //annotationSet.Clear();
                //annotationSet.Init(procState.AtomicBlocks, annotatedAuxBlocks.Union(annotatedNotZeroBlocks), assertAuxPrime, AssignCmd.SimpleAssign(Token.NoToken, auxExp, ProofState.GetInstance().tidExpr), false);
                //annotatedAuxAssignBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                //----------------------------------------------------------------------
                //Output.AddLine("Adding annotation for \"exit assign aux := 0\".");
                //annotationSet.Clear();
                //annotationSet.Init(procState.AtomicBlocks, annotatedAuxAssignBlocks.Union(annotatedZeroBlocks).Union(annotatedNotZeroBlocks), assertZeroPrime, AssignCmd.SimpleAssign(Token.NoToken, auxExp, Expr.Literal(0)), false);
                //AnnotateProcedure(proofState, procState, annotationSet);
            }
        } // end foreach procedure
    }

    override protected void StartRefine(ProofState proofState)
    {
        base.StartRefine(proofState);

        proofState.ResolveTypeCheckExpr(this.syncPredicate, false);

        //foreach(ProcedureState procState in proofState.procedureStates.Values) {
        //    procState.RecomputeTransitionPredicates();
        //}

        // create the auxiliary variable
        Variable auxVar = AuxIntroCommand.DoRun(proofState, auxVarNames[0], BasicType.Int);
        auxVars.Add(auxVar); // auxVars[0] is our aux var
        IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVar);
        IdentifierExpr auxPrimeExp = proofState.GetPrimedExpr(auxVar);

        Expr tidExpr = proofState.tidExpr;

        this.inv = Expr.Iff(Expr.Not(syncPredicate),
                            Expr.Eq(auxExp, Expr.Literal(0)));

        Expr rely = Expr.Imp(Expr.Eq(auxExp, tidExpr),
                              Expr.Eq(auxPrimeExp, auxExp));

        Expr guar = Expr.Imp(Expr.And(Expr.Neq(auxExp, Expr.Literal(0)),
                                      Expr.Neq(auxExp, tidExpr)),
                              Expr.Eq(auxPrimeExp, auxExp));

        this.rg = new RelyGuarantee(Expr.And(proofState.Invariant, this.inv),
                                    Expr.And(proofState.Rely, rely),
                                    Expr.And(proofState.Guar, guar));

    }

    override protected Expr ComputeTransitionAnnotation(ProofState proofState)
    {
        // add the extra condition to each transition predicate
        IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVars[0]);
        IdentifierExpr auxPrimeExp = proofState.GetPrimedExpr(auxVars[0]);
        Expr pred = this.syncPredicate;
        Expr predprime = proofState.MakePrime(pred);
        Expr notpred = Expr.Not(pred);
        Expr notpredprime = Expr.Not(predprime);
        Expr tidExpr = proofState.tidExpr;

        Expr annotExpr = Logic.And(
                                    Expr.Imp(Expr.Iff(pred, predprime), Expr.Eq(auxExp, auxPrimeExp)),
                                    Expr.Imp(Expr.And(notpred, predprime), Expr.Eq(auxPrimeExp, tidExpr)),
                                    Expr.Imp(Expr.And(pred, notpredprime), Expr.Eq(auxPrimeExp, Expr.Literal(0))));

        return annotExpr;
    }

} // end class RefineMutexCommand

//public class RefineMutex2Command : RefineMutexCommand
//{
//    public RefineMutex2Command(Expr predicate, string auxname)
//        : base(predicate, auxname)
//    {
//        desc = "mutex2 " + auxname + " " + Output.ToString(this.syncPredicate);
//        this.inference = Inference.Assignments;
//    }

//    public static string Usage()
//    {
//        return "mutex2 variableName predicateFormula";
//    }

//    // TODO: make other command classes like this
//    public static ProofCommand Parse(CmdParser parser)
//    {
//        if (parser.NextAsString().Equals("mutex2"))
//        {
//            string aux = parser.NextAsString();
//            Expr pred = parser.RestAsExpr();
//            return new RefineMutex2Command(pred, aux);
//        }
//        return null;
//    }

//    protected override bool DoInferAssignments(ProofState proofState)
//    {
//        IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVars[0]);
//        IdentifierExpr auxPrimeExp = ProofState.GetInstance().GetPrimedExpr(auxVars[0]);

//        Expr assertAux = Expr.Eq(auxExp, ProofState.GetInstance().tidExpr);
//        Expr assertAuxPrime = Expr.Eq(auxPrimeExp, ProofState.GetInstance().tidExpr);
//        Expr assertZero = Expr.Eq(auxExp, Expr.Literal(0));
//        Expr assertNotZero = Expr.Neq(auxExp, Expr.Literal(0));
//        Expr assertZeroPrime = Expr.Eq(auxPrimeExp, Expr.Literal(0));


//        if (base.DoInferAssignments(proofState))
//        {
//            foreach (ProcedureState procState in proofState.procedureStates.Values)
//            {
//                if ((!procState.IsReduced) || procState.IsPublic)
//                {
//                    foreach (AtomicBlock atomicBlock in procState.AtomicBlocks)
//                    {
//                        // acquires
//                        InferAssignments(proofState, atomicBlock, Expr.And(assertZero, assertAuxPrime), AssignCmd.SimpleAssign(Token.NoToken, auxExp, ProofState.GetInstance().tidExpr));
                        
//                        // releases
//                        Set<Block> releaseBlocks = InferAssignments(proofState, atomicBlock, assertZeroPrime, AssignCmd.SimpleAssign(Token.NoToken, auxExp, LiteralExpr.Literal(0)));
//                        if (releaseBlocks.Count > 0)
//                        {
//                            // assert that the lock is held by the current thread or not held
//                            AssertCmd assertCmd = new AssertCmd(Token.NoToken, Expr.Or(assertAux, assertZero));
//                            atomicBlock.InstrumentEntry(new CmdSeq(assertCmd));
//                        }
//                    }
//                    procState.MarkAsTransformed();
//                }
//            }
//        }

//        foreach (Variable auxVar in auxVars)
//        {
//            proofState.MakeNonAuxVar((GlobalVariable)auxVar);
//        }

//        return true;
//    }
//}

public class RefinePointerCommand : RefineCommand
{
    public ForallExpr syncPredicate;

    public Variable map;

    public RefinePointerCommand(ForallExpr predicate, string auxname)
        : base()
    {
        this.syncPredicate = predicate;
        this.auxVarNames.Add(auxname);

        desc = "mutexptr " + auxname + " " + Output.ToString(this.syncPredicate);
    }

    public static string Usage()
    {
        return "mutexptr variableName predicateFormula";
    }

    // TODO: make other command classes like this
    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("mutexptr"))
        {
            string aux = parser.NextAsString();
            Expr pred = parser.RestAsExpr();
            return new RefinePointerCommand((pred as ForallExpr), aux);
        }
        return null;
    }

    override protected void AnnotateProgram(ProofState proofState)
    {
        base.AnnotateProgram(proofState);

        IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
        IdentifierExpr perrExpr = proofState.GetPrimedExpr(errExpr.Decl);

        AnnotationSet annotationSet = new AnnotationSet(errExpr, perrExpr);
        
        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            if ((!procState.IsReduced) || procState.IsPublic)
            {
                Set<Expr> mapIndices = procState.ComputeMapIndices(this.map);

                foreach (Expr mapIndex in mapIndices)
                {
                    Output.AddLine("Annotating for the map index: " + Output.ToString(mapIndex));

                    Expr auxExp = AuxExprForIndex(mapIndex);
                    Expr auxPrimeExp = AuxPrimeExprForIndex(mapIndex);

                    Expr assertAux = AssertAuxForIndex(mapIndex);
                    Expr assertAuxPrime = AssertAuxPrimeForIndex(mapIndex);
                    Expr assertZero = AssertZeroForIndex(mapIndex);
                    Expr assertNotZero = AssertNotZeroForIndex(mapIndex);
                    Expr assertZeroPrime = AssertZeroPrimeForIndex(mapIndex);

                    //-------------------------
                    Output.LogLine("Refine: Annotating procedure: " + procState.impl.Name);

                    Set<AtomicBlock> annotatedAuxBlocks = new Set<AtomicBlock>();
                    Set<AtomicBlock> annotatedAuxAssignBlocks = new Set<AtomicBlock>();
                    Set<AtomicBlock> annotatedZeroAssignBlocks = new Set<AtomicBlock>(); 
                    Set<AtomicBlock> annotatedZeroBlocks = new Set<AtomicBlock>();
                    Set<AtomicBlock> annotatedNotZeroBlocks = new Set<AtomicBlock>();

                    //----------------------------------------------------------------------
                    // infer assignments
                    foreach (AtomicBlock atomicBlock in procState.AtomicBlocks)
                    {
                        // acquires
                        Set<Block> acquireBlocks = InferAssignments(proofState, atomicBlock, Expr.And(assertZero, assertAuxPrime), AssignCmd.MapAssign(Token.NoToken, new IdentifierExpr(Token.NoToken, auxVars[0]), mapIndex, ProofState.GetInstance().tidExpr));
                        if (acquireBlocks.Count > 0)
                        {
                            annotatedAuxAssignBlocks.Add(atomicBlock);
                        }

                        // releases
                        Set<Block> releaseBlocks = InferAssignments(proofState, atomicBlock, assertZeroPrime, AssignCmd.MapAssign(Token.NoToken, new IdentifierExpr(Token.NoToken, auxVars[0]), mapIndex, LiteralExpr.Literal(0)));
                        if (releaseBlocks.Count > 0)
                        {
                            annotatedZeroAssignBlocks.Add(atomicBlock);

                            // assert that the lock is held by the current thread or not held
                            AssertCmd assertCmd = new AssertCmd(Token.NoToken, Expr.Or(assertAux, assertZero));
                            atomicBlock.InstrumentEntry(new CmdSeq(assertCmd));
                        }
                    }

                    ////----------------------------------------------------------------------
                    Output.AddLine("Adding annotation for \"entry assert aux == tid\".");
                    annotationSet.Clear();
                    annotationSet.Init(procState.AtomicBlocks, assertAux, new AssertCmd(Token.NoToken, assertAux), true);
                    annotatedAuxBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                    ////----------------------------------------------------------------------
                    Output.AddLine("Adding annotation for \"entry assert aux == 0\".");
                    annotationSet.Clear();
                    annotationSet.Init(procState.AtomicBlocks, annotatedAuxBlocks, assertZero, new AssertCmd(Token.NoToken, assertZero), true);
                    annotatedZeroBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                    ////----------------------------------------------------------------------
                    Output.AddLine("Adding annotation for \"entry assert aux != 0\".");
                    annotationSet.Clear();
                    annotationSet.Init(procState.AtomicBlocks, annotatedAuxBlocks.Union(annotatedZeroBlocks), assertNotZero, new AssertCmd(Token.NoToken, assertNotZero), true);
                    annotatedNotZeroBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                    ////----------------------------------------------------------------------
                    //Output.AddLine("Adding annotation for \"exit assign aux := tid\".");
                    //annotationSet.Clear();
                    //annotationSet.Init(procState.AtomicBlocks, annotatedAuxBlocks.Union(annotatedNotZeroBlocks), assertAuxPrime, AssignCmd.MapAssign(Token.NoToken, new IdentifierExpr(Token.NoToken, auxVars[0]), mapIndex, ProofState.GetInstance().tidExpr), false);
                    //annotatedAuxAssignBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                    ////----------------------------------------------------------------------
                    //Output.AddLine("Adding annotation for \"exit assign aux := 0\".");
                    //annotationSet.Clear();
                    //annotationSet.Init(procState.AtomicBlocks, annotatedAuxAssignBlocks.Union(annotatedZeroBlocks).Union(annotatedNotZeroBlocks), assertZeroPrime, AssignCmd.MapAssign(Token.NoToken, new IdentifierExpr(Token.NoToken, auxVars[0]), mapIndex, Expr.Literal(0)), false);
                    //AnnotateProcedure(proofState, procState, annotationSet);
                    //break;
                } // for each map index
                //break;
            }
        } // end foreach procedure
    }

    override protected void StartRefine(ProofState proofState)
    {

        base.StartRefine(proofState);

        proofState.ResolveTypeCheckExpr(this.syncPredicate, false);

        //foreach(ProcedureState procState in proofState.procedureStates.Values) {
        //    procState.RecomputeTransitionPredicates();
        //}

        // determine the essential map
        this.map = (new MyMapSearcher()).DoSearch(syncPredicate.Body);

        VariableSeq dummies = syncPredicate.Dummies;
        Variable dummy = dummies[0];

        // create the auxiliary variable
        Variable auxVar = AuxIntroCommand.DoRun(proofState, auxVarNames[0], new MapType(Token.NoToken, new TypeVariableSeq(), new TypeSeq(dummy.TypedIdent.Type), BasicType.Int));
        auxVars.Add(auxVar); // auxVars[0] is our aux var
        // always call GetPrime after adding it to the proofstate
        Expr auxExp = AuxExprForIndex(dummy);
        Expr auxPrimeExp = AuxPrimeExprForIndex(dummy);

        Expr tidExpr = proofState.tidExpr;

        Trigger trigger = new Trigger(Token.NoToken, true, new ExprSeq(MapExprForIndex(dummy)),
                                new Trigger(Token.NoToken, true, new ExprSeq(AuxExprForIndex(dummy))));
        
        this.inv = new ForallExpr(Token.NoToken, dummies, trigger, Expr.Iff(Expr.Not(syncPredicate.Body),
                                                                            Expr.Eq(auxExp, Expr.Literal(0))));

        trigger = new Trigger(Token.NoToken, true, new ExprSeq(auxExp));
        
        Expr rely = new ForallExpr(Token.NoToken, dummies, trigger, 
                            Expr.Imp(Expr.Eq(auxExp, tidExpr),
                                     Expr.Eq(auxPrimeExp, auxExp)));

        Expr guar = new ForallExpr(Token.NoToken, dummies, trigger,
                            Expr.Imp(Expr.And(Expr.Neq(auxExp, Expr.Literal(0)),
                                              Expr.Neq(auxExp, tidExpr)),
                                     Expr.Eq(auxPrimeExp, auxExp)));

        this.rg = new RelyGuarantee(Expr.And(proofState.Invariant, this.inv),
                                    Expr.And(proofState.Rely, rely),
                                    Expr.And(proofState.Guar, guar));

    }

    override protected Expr ComputeTransitionAnnotation(ProofState proofState)
    {
        // add the extra condition to each transition predicate
        VariableSeq dummies = syncPredicate.Dummies;
        Variable dummy = dummies[0];

        Expr auxExp = AuxExprForIndex(dummy);
        Expr auxPrimeExp = AuxPrimeExprForIndex(dummy);
        Expr pred = syncPredicate.Body;
        Expr predprime = proofState.MakePrime(pred, new VariableSeq(dummy)); // do not touch dummy
        Expr notpred = Expr.Not(pred);
        Expr notpredprime = Expr.Not(predprime);

        Expr tidExpr = proofState.tidExpr;       

        Trigger trigger = new Trigger(Token.NoToken, true, new ExprSeq(MapExprForIndex(dummy)),
                          new Trigger(Token.NoToken, true, new ExprSeq(MapPrimeExprForIndex(dummy))));

        Expr annotExpr = new ForallExpr(Token.NoToken, dummies, trigger,
                                  Logic.And(
                                             Expr.Imp(Expr.Iff(pred, predprime), Expr.Eq(auxExp, auxPrimeExp)),
                                             Expr.Imp(Expr.And(notpred, predprime), Expr.Eq(auxPrimeExp, tidExpr)),
                                             Expr.Imp(Expr.And(pred, notpredprime), Expr.Eq(auxPrimeExp, Expr.Literal(0)))));

        return annotExpr;
    }

    protected Expr SyncPredicateForIndex(Expr index)
    {
        VariableSeq dummies = syncPredicate.Dummies;
        Variable dummy = dummies[0];

        Hashtable map = new Hashtable();
        map.Add(dummy, index);

        return Logic.Substitute(map, this.syncPredicate.Body);
    }

    // helper functions to construct aux expressions with a given index

    protected Expr MapExprForIndex(Variable index)
    {
        return Expr.Select(new IdentifierExpr(Token.NoToken, this.map), new IdentifierExpr(Token.NoToken, index));
    }

    protected Expr MapPrimeExprForIndex(Variable index)
    {
        return Expr.Select(ProofState.GetInstance().GetPrimedExpr(this.map), new IdentifierExpr(Token.NoToken, index));
    }

    protected Expr AuxExprForIndex(Variable index)
    {
        return AuxExprForIndex(new IdentifierExpr(Token.NoToken, index));
    }

    protected Expr AuxPrimeExprForIndex(Variable index)
    {
        return AuxPrimeExprForIndex(new IdentifierExpr(Token.NoToken, index));
    }

    protected Expr AuxExprForIndex(Expr index)
    {
        return Expr.Select(new IdentifierExpr(Token.NoToken, auxVars[0]), index);
    }

    protected Expr AuxPrimeExprForIndex(Expr index)
    {
        return Expr.Select(ProofState.GetInstance().GetPrimedExpr(auxVars[0]), index);
    }

    protected Expr AssertAuxForIndex(Expr index)
    {
        return Expr.Eq(AuxExprForIndex(index), ProofState.GetInstance().tidExpr);
    }

    protected Expr AssertAuxPrimeForIndex(Expr index)
    {
        return Expr.Eq(AuxPrimeExprForIndex(index), ProofState.GetInstance().tidExpr);
    }

    protected Expr AssertZeroForIndex(Expr index)
    {
        return Expr.Eq(AuxExprForIndex(index), Expr.Literal(0));
    }

    protected Expr AssertNotZeroForIndex(Expr index)
    {
        return Expr.Neq(AuxExprForIndex(index), Expr.Literal(0));
    }

    protected Expr AssertZeroPrimeForIndex(Expr index)
    {
        return Expr.Eq(AuxPrimeExprForIndex(index), Expr.Literal(0));
    }

} // end class RefineCommand

public class RefineStableCommand : RefineCommand
{
    public Expr syncPredicate;

    public RefineStableCommand(Expr predicate, string auxname)
        : base()
    {
       this.syncPredicate = predicate;
       this.auxVarNames.Add(auxname);

        desc = "stable " + auxname + " " + Output.ToString(this.syncPredicate);
    }

    public static string Usage()
    {
        return "stable variableName predicateFormula";
    }

    // TODO: make other command classes like this
    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("stable"))
        {
            string aux = parser.NextAsString();
            Expr pred = parser.RestAsExpr();
			return new RefineStableCommand(pred, aux);
        }
        return null;
    }

    override protected void AnnotateProgram(ProofState proofState)
    {
        base.AnnotateProgram(proofState);

        IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
        IdentifierExpr perrExpr = proofState.GetPrimedExpr(errExpr.Decl);

        IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVars[0]);
        IdentifierExpr auxPrimeExp = ProofState.GetInstance().GetPrimedExpr(auxVars[0]);

        Expr assertAux = Expr.Eq(auxExp, Expr.True);
        Expr assertAuxPrime = Expr.Eq(auxPrimeExp, Expr.True);
        Expr assertZero = Expr.Eq(auxExp, Expr.False);
        
        AnnotationSet annotationSet = new AnnotationSet(errExpr, perrExpr);
        Set<AtomicBlock> annotatedAuxBlocks = new Set<AtomicBlock>();
        Set<AtomicBlock> annotatedZeroBlocks = new Set<AtomicBlock>();
        
        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            if ((!procState.IsReduced) || procState.IsPublic)
            {
                Output.LogLine("Refine: Annotating procedure: " + procState.impl.Name);

                //----------------------------------------------------------------------
                Output.AddLine("Adding annotation for \"entry assert aux == true\".");
                annotationSet.Clear();
                annotationSet.Init(procState.AtomicBlocks, assertAux, new AssertCmd(Token.NoToken, assertAux), true);
                annotatedAuxBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                //----------------------------------------------------------------------
                Output.AddLine("Adding annotation for \"entry assert aux == false\".");
                annotationSet.Clear();
                annotationSet.Init(procState.AtomicBlocks, annotatedAuxBlocks, assertZero, new AssertCmd(Token.NoToken, assertZero), true);
                AnnotateProcedure(proofState, procState, annotationSet);

                //----------------------------------------------------------------------
                Output.AddLine("Adding annotation for \"exit assign aux := true\".");
                annotationSet.Clear();
                annotationSet.Init(procState.AtomicBlocks, annotatedAuxBlocks, assertAuxPrime, AssignCmd.SimpleAssign(Token.NoToken, auxExp, Expr.True), false);
                AnnotateProcedure(proofState, procState, annotationSet);
            }
        } // end foreach procedure
    }
    
    override protected void StartRefine(ProofState proofState)
    {
        base.StartRefine(proofState);

        proofState.ResolveTypeCheckExpr(this.syncPredicate, false);

        //foreach (ProcedureState procState in proofState.procedureStates.Values)
        //{
        //    procState.RecomputeTransitionPredicates();
        //}

        // create the auxiliary variable
        Variable auxVar = AuxIntroCommand.DoRun(proofState, auxVarNames[0], BasicType.Bool);
        auxVars.Add(auxVar); // auxVars[0] is our aux var
        IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVar);
        IdentifierExpr auxPrimeExp = proofState.GetPrimedExpr(auxVar);

        this.inv = Expr.Iff(syncPredicate, auxExp);

        Expr rely, guar;

        guar = rely = Expr.Imp(Expr.Eq(auxExp, Expr.True),
                               Expr.Eq(auxPrimeExp, Expr.True));

        this.rg = new RelyGuarantee(Expr.And(proofState.Invariant, this.inv),
                                    Expr.And(proofState.Rely, rely),
                                    Expr.And(proofState.Guar, guar));
    }

    override protected Expr ComputeTransitionAnnotation(ProofState proofState)
    {
        // add the extra condition to each transition predicate
        IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVars[0]);
        IdentifierExpr auxPrimeExp = proofState.GetPrimedExpr(auxVars[0]);
        Expr pred = this.syncPredicate;
        Expr predprime = proofState.MakePrime(pred);
        Expr notpred = Expr.Not(pred);
        Expr notpredprime = Expr.Not(predprime);

        Expr annotExpr = Logic.And(
                                    Expr.Imp(predprime, Expr.Eq(auxPrimeExp, Expr.True)),
                                    Expr.Imp(notpredprime, Expr.Eq(auxPrimeExp, Expr.False)),
                                    Expr.Imp(Expr.Iff(pred, predprime), Expr.Eq(auxExp, auxPrimeExp)));
        return annotExpr;
    }


} // end class RefineStableCommand

public class RefineReadWriteCommand : RefineCommand
{
    public Expr syncPredicateRead;
    public Expr syncPredicateWrite;

    public RefineReadWriteCommand(Expr predicateR, Expr predicateW, string auxname)
        : base()
    {
        this.syncPredicateRead = predicateR;
        this.syncPredicateWrite = predicateW;

        this.auxVarNames.Add(auxname + "R");
        this.auxVarNames.Add(auxname + "W");

        desc = "rwlock " + auxname + " " + Output.ToString(this.syncPredicateRead) + "#" + Output.ToString(this.syncPredicateWrite);
    }

    public static string Usage()
    {
        return "rwlock variableName readpredicateFormula#writepredicateFormula";
    }

    // TODO: make other command classes like this
    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("rwlock"))
        {
            string aux = parser.NextAsString();
			List<Expr> preds = parser.RestAsExprList('#');
			return new RefineReadWriteCommand(preds[0], preds[1], aux);
        }
        return null;
    }

    override protected void AnnotateProgram(ProofState proofState)
    {
        base.AnnotateProgram(proofState);

        IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
        IdentifierExpr perrExpr = proofState.GetPrimedExpr(errExpr.Decl);

        IdentifierExpr auxExp = new IdentifierExpr(Token.NoToken, auxVars[1]);
        IdentifierExpr auxPrimeExp = ProofState.GetInstance().GetPrimedExpr(auxVars[1]);

        Expr assertAux = Expr.Eq(auxExp, ProofState.GetInstance().tidExpr);
        Expr assertAuxPrime = Expr.Eq(auxPrimeExp, ProofState.GetInstance().tidExpr);
        Expr assertZero = Expr.Eq(auxExp, Expr.Literal(0));
        Expr assertNotZero = Expr.Neq(auxExp, Expr.Literal(0));
        Expr assertZeroPrime = Expr.Eq(auxPrimeExp, Expr.Literal(0));

        AnnotationSet annotationSet = new AnnotationSet(errExpr, perrExpr);
        Set<AtomicBlock> annotatedAuxBlocks = new Set<AtomicBlock>();
        Set<AtomicBlock> annotatedAuxAssignBlocks = new Set<AtomicBlock>();
        Set<AtomicBlock> annotatedZeroBlocks = new Set<AtomicBlock>();
        Set<AtomicBlock> annotatedNotZeroBlocks = new Set<AtomicBlock>();

        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            if ((!procState.IsReduced) || procState.IsPublic)
            {
                Output.LogLine("Refine: Annotating procedure: " + procState.impl.Name);

                //----------------------------------------------------------------------
                Output.AddLine("Adding annotation for \"entry assert auxW == tid\".");
                annotationSet.Clear();
                annotationSet.Init(procState.AtomicBlocks, assertAux, new AssertCmd(Token.NoToken, assertAux), true);
                annotatedAuxBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                //----------------------------------------------------------------------
                Output.AddLine("Adding annotation for \"entry assert aux == 0\".");
                annotationSet.Clear();
                annotationSet.Init(procState.AtomicBlocks, annotatedAuxBlocks, assertZero, new AssertCmd(Token.NoToken, assertZero), true);
                annotatedZeroBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                //----------------------------------------------------------------------
                Output.AddLine("Adding annotation for \"entry assert auxW != 0\".");
                annotationSet.Clear();
                annotationSet.Init(procState.AtomicBlocks, annotatedAuxBlocks.Union(annotatedZeroBlocks), assertNotZero, new AssertCmd(Token.NoToken, assertNotZero), true);
                annotatedNotZeroBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                //----------------------------------------------------------------------
                Output.AddLine("Adding annotation for \"exit assign auxW := tid\".");
                annotationSet.Clear();
                annotationSet.Init(procState.AtomicBlocks, annotatedAuxBlocks.Union(annotatedNotZeroBlocks), assertAuxPrime, AssignCmd.SimpleAssign(Token.NoToken, auxExp, ProofState.GetInstance().tidExpr), false);
                annotatedAuxAssignBlocks = AnnotateProcedure(proofState, procState, annotationSet);

                //----------------------------------------------------------------------
                Output.AddLine("Adding annotation for \"exit assign auxW := 0\".");
                annotationSet.Clear();
                annotationSet.Init(procState.AtomicBlocks, annotatedAuxAssignBlocks.Union(annotatedZeroBlocks).Union(annotatedNotZeroBlocks), assertZeroPrime, AssignCmd.SimpleAssign(Token.NoToken, auxExp, Expr.Literal(0)), false);
                AnnotateProcedure(proofState, procState, annotationSet);
            }
        } // end foreach procedure
    }

    override protected void StartRefine(ProofState proofState)
    {
        base.StartRefine(proofState);

        //foreach(ProcedureState procState in proofState.procedureStates.Values) {
        //    procState.RecomputeTransitionPredicates();
        //}

        // create the auxiliary variable
        Variable auxVarRead = AuxIntroCommand.DoRun(proofState, auxVarNames[0], new MapType(Token.NoToken, new TypeVariableSeq(), new TypeSeq(BasicType.Int), BasicType.Bool));
        auxVars.Add(auxVarRead); // auxVars[0] is our aux read var
        IdentifierExpr auxExpRead = new IdentifierExpr(Token.NoToken, auxVarRead);
        IdentifierExpr auxPrimeExpRead = proofState.GetPrimedExpr(auxVarRead);

        Variable auxVarWrite = AuxIntroCommand.DoRun(proofState, auxVarNames[1], BasicType.Int);
        auxVars.Add(auxVarWrite); // auxVars[1] is our aux write var
        IdentifierExpr auxExpWrite = new IdentifierExpr(Token.NoToken, auxVarWrite);
        IdentifierExpr auxPrimeExpWrite = proofState.GetPrimedExpr(auxVarWrite);

        Expr tidExpr = proofState.tidExpr;
        
        Variable dummy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "i", BasicType.Int));

        this.inv = Logic.And(
                            Expr.Imp(syncPredicateRead, Expr.Not(syncPredicateWrite)),
                            Expr.Iff(Expr.Not(syncPredicateWrite),
                                     Expr.Eq(auxExpWrite, Expr.Literal(0))),
                            Expr.Iff(syncPredicateRead,
                                     new ExistsExpr(Token.NoToken, new VariableSeq(dummy), Expr.Eq(AuxExprForIndex(dummy), Expr.True))));

        Expr rely = Expr.And(
                        Expr.Imp(Expr.Eq(auxExpWrite, tidExpr),
                                 Expr.Eq(auxPrimeExpWrite, auxExpWrite)),
                        Expr.Eq(AuxExprForIndex(tidExpr),
                                AuxPrimeExprForIndex(tidExpr)));

        Expr guar = Expr.And(
                        Expr.Imp(Expr.And(Expr.Neq(auxExpWrite, Expr.Literal(0)),
                                          Expr.Neq(auxExpWrite, tidExpr)),
                                 Expr.Eq(auxPrimeExpWrite, auxExpWrite)),
                        new ForallExpr(Token.NoToken, new VariableSeq(dummy),
                                       Expr.Imp(Expr.Neq(new IdentifierExpr(Token.NoToken, dummy), tidExpr),
                                                Expr.Eq(AuxExprForIndex(dummy), AuxPrimeExprForIndex(dummy)))));

        this.rg = new RelyGuarantee(Expr.And(proofState.Invariant, this.inv),
                                    Expr.And(proofState.Rely, rely),
                                    Expr.And(proofState.Guar, guar));

    }

    override protected Expr ComputeTransitionAnnotation(ProofState proofState)
    {
        // add the extra condition to each transition predicate

        Expr tidExpr = proofState.tidExpr;

        Variable dummy = Logic.CreateDummyBoundVar(BasicType.Int);
        Expr leaveReadsAsIs = new ForallExpr(Token.NoToken, new VariableSeq(dummy),
                                             Expr.Eq(AuxExprForIndex(dummy), AuxPrimeExprForIndex(dummy)));
        
        dummy = Logic.CreateDummyBoundVar(BasicType.Int);
        Expr leaveReadsAsIsExcept = new ForallExpr(Token.NoToken, new VariableSeq(dummy),
                                                   Expr.Imp(Expr.Neq(new IdentifierExpr(Token.NoToken, dummy), tidExpr),
                                                            Expr.Eq(AuxExprForIndex(dummy), AuxPrimeExprForIndex(dummy))));

        IdentifierExpr auxExpWrite = new IdentifierExpr(Token.NoToken, auxVars[1]);
        IdentifierExpr auxPrimeExpWrite = ProofState.GetInstance().GetPrimedExpr(auxVars[1]);

        Expr predW = this.syncPredicateWrite;
        Expr predprimeW = proofState.MakePrime(predW);
        Expr notpredW = Expr.Not(predW);
        Expr notpredprimeW = Expr.Not(predprimeW);

        Expr predR = this.syncPredicateRead;
        Expr predprimeR = proofState.MakePrime(predR);
        Expr notpredR = Expr.Not(predR);
        Expr notpredprimeR = Expr.Not(predprimeR);

        Expr annotExpr = Logic.And(
                                 Expr.Imp(Expr.Iff(predW, predprimeW), Logic.And(
                                                                                 Expr.Eq(auxExpWrite, auxPrimeExpWrite),
                                                                                 leaveReadsAsIs)),
                                 Expr.Imp(Expr.And(notpredW, predprimeR), Logic.And(
                                                                                 Expr.Eq(AuxPrimeExprForIndex(tidExpr), Expr.True),
                                                                                 Expr.Eq(auxPrimeExpWrite, Expr.Literal(0)),
                                                                                 leaveReadsAsIsExcept)),
                                 Expr.Imp(Expr.And(notpredR, predprimeW), Logic.And(
                                                                                 Expr.Eq(AuxPrimeExprForIndex(tidExpr), Expr.False),
                                                                                 Expr.Eq(auxPrimeExpWrite, tidExpr),
                                                                                 leaveReadsAsIsExcept)),
                                 Expr.Imp(Expr.And(predW, notpredprimeW), Logic.And(
                                                                                 Expr.Eq(auxPrimeExpWrite, Expr.Literal(0)),
                                                                                 leaveReadsAsIs)));

        return annotExpr;
    }

    // helper functions to construct aux expressions with a given index

    protected Expr AuxExprForIndex(Variable index)
    {
        return AuxExprForIndex(new IdentifierExpr(Token.NoToken, index));
    }

    protected Expr AuxPrimeExprForIndex(Variable index)
    {
        return AuxPrimeExprForIndex(new IdentifierExpr(Token.NoToken, index));
    }

    protected Expr AuxExprForIndex(Expr index)
    {
        return Expr.Select(new IdentifierExpr(Token.NoToken, auxVars[0]), index);
    }

    protected Expr AuxPrimeExprForIndex(Expr index)
    {
        return Expr.Select(ProofState.GetInstance().GetPrimedExpr(auxVars[0]), index);
    }

    //override protected bool CheckValidity(ProofState proofState)
    //{

    //    IdentifierExpr errExpr = new IdentifierExpr(Token.NoToken, errVar);
    //    IdentifierExpr perrExpr = ProofState.GetInstance().GetPrimedExpr(errVar);

    //    Expr annotExpr = ComputeTransitionAnnotation();

    //    // first add regular annotations
    //    foreach (ProcedureState procState in proofState.procedureStates.Values)
    //    {
    //        if ((!procState.IsReduced) || procState.IsPublic)
    //        {
    //            Output.LogLine("Refine: Checking procedure: " + procState.impl.Name);
    //            procState.ClearTransitionPredicates();

    //            foreach (AtomicBlock atomicBlock in procState.atomicBlocks)
    //            {
    //                atomicBlock.TransitionPredicate = Expr.And(Expr.And(atomicBlock.TransitionPredicate, annotExpr), Expr.Iff(perrExpr, errExpr));
    //            }
    //        }
    //    }

    //    IdentifierExpr auxExpWrite = new IdentifierExpr(Token.NoToken, auxVarWrite);

    //    // now add annotations for preconditions
    //    Expr assertAuxWrite = Expr.Eq(auxExpWrite, ProofState.GetInstance().tidExpr);
    //    Expr assertAuxRead = Expr.Eq(AuxExprForIndex(proofState.tidExpr), Expr.True);

    //    foreach (ProcedureState procState in proofState.procedureStates.Values)
    //    {
    //        if ((procState.IsReduced) || procState.IsPublic)
    //        {
    //            Expr inv = proofState.InvariantForProc(procState);

    //            // for write
    //            if (Prover.GetInstance().CheckValid(Expr.Imp(Expr.And(inv, procState.Requires), this.syncPredicateWrite)))
    //            {

    //                AddPreCondForProc(procState, assertAuxWrite);

    //                // add assertion to call blocks
    //                foreach (CallBlock callBlock in procState.callerBlocks)
    //                {
    //                    Expr labeledAssertAux = LabeledExprHelper.NegAuxAssert(callBlock, assertAuxWrite);
    //                    Expr labeledAnnot = Expr.Or(Expr.And(assertAuxWrite, Expr.Eq(errExpr, perrExpr)),
    //                                                 Expr.And(labeledAssertAux, Expr.Eq(perrExpr, Expr.True)));
    //                    callBlock.TransitionPredicate = Expr.And(Expr.And(callBlock.RecomputeTransitionPredicate(), annotExpr), labeledAnnot);
    //                }
    //            }

    //            // for read
    //            if (Prover.GetInstance().CheckValid(Expr.Imp(Expr.And(inv, procState.Requires), this.syncPredicateRead)))
    //            {

    //                AddPreCondForProc(procState, assertAuxRead);

    //                // add assertion to call blocks
    //                foreach (CallBlock callBlock in procState.callerBlocks)
    //                {
    //                    Expr labeledAssertAux = LabeledExprHelper.NegAuxAssert(callBlock, assertAuxRead);
    //                    Expr labeledAnnot = Expr.Or(Expr.And(assertAuxRead, Expr.Eq(errExpr, perrExpr)),
    //                                                 Expr.And(labeledAssertAux, Expr.Eq(perrExpr, Expr.True)));
    //                    callBlock.TransitionPredicate = Expr.And(Expr.And(callBlock.RecomputeTransitionPredicate(), annotExpr), labeledAnnot);
    //                }
    //            }
    //        }
    //    }

    //    bool result = true;

    //    // finally check
    //    foreach (ProcedureState procState in proofState.procedureStates.Values)
    //    {
    //        if ((!procState.IsReduced) || procState.IsPublic)
    //        {
    //            // now check
    //            Expr precond = Expr.And(PreCondForProc(procState), Expr.Not(errExpr));
    //            Expr postcond = Expr.Not(perrExpr);
    //            if (!rg.CheckProcedure(proofState, procState, precond, postcond))
    //            {
    //                result = false;
    //                break;
    //            }
    //        }
    //    }

    //    return result;
    //}

    //override protected void EndRefineSuccess(ProofState proofState)
    //{

    //    Expr annotExpr = ComputeTransitionAnnotation();

    //    foreach (ProcedureState procState in proofState.procedureStates.Values)
    //    {
    //        foreach (AtomicBlock atomicBlock in procState.atomicBlocks)
    //        {
    //            atomicBlock.PushAnnotation(annotExpr);
    //        }
    //    }

    //    proofState.invs.Add(this.inv);
    //    // proofState.rely.Add(this.rely);
    //    // proofState.guar.Add(this.guar);

    //    proofState.RemoveAuxVar((GlobalVariable)errVar);
    //}

    //override protected void EndRefineFail(ProofState proofState)
    //{
    //    foreach (ProcedureState procState in proofState.procedureStates.Values)
    //    {
    //        procState.ClearTransitionPredicates();
    //    }

    //    proofState.RemoveAuxVar((GlobalVariable)auxVarRead);
    //    proofState.RemoveAuxVar((GlobalVariable)auxVarWrite);

    //    proofState.RemoveAuxVar((GlobalVariable)errVar);
    //}

} // end class RefineReadWriteCommand
} // end namespace QED