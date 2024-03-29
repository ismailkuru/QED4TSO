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
    using System.Text;


    public class Logic
    {

        public static Microsoft.Boogie.Type BooleanType { get { return True.Decl.TypedIdent.Type; } }
        public static IdentifierExpr True;
        public static IdentifierExpr False;

        static public IdentifierExpr MakeHiddenExpr(Variable var)
        {
            return new IdentifierExpr(Token.NoToken, MakeHiddenVar(var));
        }

        static public Variable MakeHiddenVar(Variable var)
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, var.Name + "_hidden", var.TypedIdent.Type));
        }

        static public IdentifierExpr MakePrimedExpr(Variable var)
        {
            return new IdentifierExpr(Token.NoToken, MakePrimedVar(var));
        }

        // for tressa
        static public IdentifierExpr MakeDoublePrimedExpr(Variable var)
        {
            return new IdentifierExpr(Token.NoToken, MakeDoublePrimedVar(var));
        }

        static public Variable MakePrimedVar(Variable var)
        {
            TypedIdent tident = new TypedIdent(Token.NoToken, var.Name + "_prime", var.TypedIdent.Type);
            if (var is GlobalVariable)
            {
                return new GlobalVariable(Token.NoToken, tident);
            }
            else
            {
                return new LocalVariable(Token.NoToken, tident);
            }
        }

        // for tressa
        static public Variable MakeDoublePrimedVar(Variable var)
        {
            TypedIdent tident = new TypedIdent(Token.NoToken, var.Name + "_primeprime", var.TypedIdent.Type);
            if (var is GlobalVariable)
            {
                return new GlobalVariable(Token.NoToken, tident);
            }
            else
            {
                return new LocalVariable(Token.NoToken, tident);
            }
        }

        static int nextDummyId = 0;

        static public Expr Rename(VariableSeq dummies, Expr body)
        {
            if (dummies == null || dummies.Length == 0)
            {
                return body;
            }

            Hashtable dummyMap = new Hashtable();
            foreach (Variable dummy in dummies)
            {
                Debug.Assert(!dummyMap.Contains(dummy));
                Variable newDummy = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, dummy.Name + "_dum_" + nextDummyId.ToString(), dummy.TypedIdent.Type));
                dummyMap.Add(dummy, new IdentifierExpr(Token.NoToken, newDummy));
            }

            ++nextDummyId;

            Expr newBody = Substitute(dummyMap, body);

            return newBody;
        }

        static public Expr Rename(VariableSeq dummies, Expr body, out VariableSeq outDummies)
        {
            VariableSeq newDummies = new VariableSeq();

            if (dummies == null || dummies.Length == 0)
            {
                outDummies = newDummies;
                return body;
            }

            Hashtable dummyMap = new Hashtable();
            foreach (Variable dummy in dummies)
            {
                Debug.Assert(!dummyMap.Contains(dummy));
                Variable newDummy = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, dummy.Name + "_dum_" + nextDummyId.ToString(), dummy.TypedIdent.Type));
                dummyMap.Add(dummy, new IdentifierExpr(Token.NoToken, newDummy));
                newDummies.Add(newDummy);
            }

            ++nextDummyId;

            Expr newBody = Substitute(dummyMap, body);

            outDummies = newDummies;
            return newBody;
        }


        static public Expr ExistsExpr(VariableSeq dummies, Expr body)
        {
            if (dummies == null || dummies.Length == 0)
            {
                return body;
            }
            VariableSeq newDummies;
            Expr newBody = Rename(dummies, body, out newDummies);
            return new ExistsExpr(Token.NoToken, newDummies, newBody);
        }

        static public Expr ExistsExpr(VariableSeq dummies, Trigger trigger, Expr body)
        {
            if (dummies == null || dummies.Length == 0)
            {
                return body;
            }
            VariableSeq newDummies;
            Expr newBody = Rename(dummies, body, out newDummies);
            return new ExistsExpr(Token.NoToken, newDummies, trigger, newBody);
        }

        static public Expr ForallExpr(VariableSeq dummies, Expr body)
        {
            if (dummies == null || dummies.Length == 0)
            {
                return body;
            }
            VariableSeq newDummies;
            Expr newBody = Rename(dummies, body, out newDummies);
            return new ForallExpr(Token.NoToken, newDummies, newBody);
        }

        static public Expr ForallExpr(VariableSeq dummies, Trigger trigger, Expr body)
        {
            if (dummies == null || dummies.Length == 0)
            {
                return body;
            }
            VariableSeq newDummies;
            Expr newBody = Rename(dummies, body, out newDummies);
            return new ForallExpr(Token.NoToken, newDummies, trigger, newBody);
        }

        public static Expr Substitute(Hashtable map, Hashtable mapold, Expr expr)
        {
            return Logic.Substitute(Substituter.SubstitutionFromHashtable(map), Substituter.SubstitutionFromHashtable(mapold), expr);
        }

        public static Expr Substitute(Substitution subst, Substitution substold, Expr expr)
        {
            return (Expr)new MySubstituter(subst, substold).Visit(expr);
        }

        public static Expr Substitute(Hashtable map, Expr expr)
        {
            return Logic.Substitute(Substituter.SubstitutionFromHashtable(map), expr);
        }

        public static List<Expr> SubstituteList(Hashtable map, List<Expr> list)
        {
            List<Expr> newList = new List<Expr>();
            for (int i = 0; i < list.Count; ++i)
            {
                newList[i] = Substitute(map, list[i]);
            }

            return newList;
        }

        public static Expr Substitute(Hashtable map, Expr expr, VariableSeq dontTouch)
        {
            return (Expr)new MySubstituter(Substituter.SubstitutionFromHashtable(map), dontTouch).Visit(expr);
        }

        public static Expr Substitute(Substitution subst, Expr expr)
        {
            return (Expr)new MySubstituter(subst).Visit(expr);
        }

        //static public Expr HideLocals(AtomicBlock atomicBlock) {
        //    Expr trp = atomicBlock.TransitionPredicate;

        //    return (Expr) new MyHider().Visit(trp);
        //}

        static public Expr EquivExpr(Microsoft.Boogie.Type t, Expr expr1, Expr expr2)
        {
            return t == BasicType.Bool ? Expr.Iff(expr1, expr2) : Expr.Eq(expr1, expr2);
        }

        static public void ResolveTypeCheckExpr(ProofState proofState, ProcedureState procState, Expr expr, bool twostate)
        {
            if (procState == null)
            {
                proofState.ResolveTypeCheckExpr(expr, twostate);
            }
            else
            {
                procState.ResolveTypeCheckExpr(expr, twostate);
            }
        }

        static public Expr ParseFormula(ProofState proofState, string procname, string strExpr, bool twostate)
        {
            Expr expr = Qoogie.ParseExpr(strExpr);
            ProcedureState procState = null;
            if (procname != "*" && procname != "")
            {
                procState = proofState.GetProcedureState(procname);
            }
            expr = new MyExprTranslator().DoTranslate(proofState, procState, expr);
            ResolveTypeCheckExpr(proofState, procState, expr, twostate);
            return expr;
        }

        static public Expr And(params Expr[] exprs)
        {
            Expr expr = null;
            foreach (Expr e in exprs)
            {
                if (expr == null)
                {
                    expr = e;
                }
                else
                {
                    expr = Expr.And(expr, e);
                }
            }
            return expr;
        }

        static public Expr Or(params Expr[] exprs)
        {
            Expr expr = null;
            foreach (Expr e in exprs)
            {
                if (expr == null)
                {
                    expr = e;
                }
                else
                {
                    expr = Expr.Or(expr, e);
                }
            }
            return expr;
        }

        static public bool IsExprsEqual(Expr expr1, Expr expr2)
        {
            return Output.ToString(expr1) == Output.ToString(expr2);
        }

        static int nextDummyVarId = 0;
        static public Variable CreateDummyBoundVar(Type type)
        {
            return new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "dummy" + (nextDummyVarId++), type));
        }


        static public Expr ConvertFromOldToPrime(ProcedureState procState, Expr expr)
        {
            Expr newExpr = Logic.Substitute(Substituter.SubstitutionFromHashtable(procState.AllPrimesMap),
                                            Substituter.SubstitutionFromHashtable(new Hashtable()),
                                            expr);

            return newExpr;
        }

        static public Expr ComputeSeqComposedTransitionPredicate(AtomicBlock thisBlock, AtomicBlock thatBlock)
        {
            TPGenerator thisTPGen = new TPGenerator(thisBlock, false);
            TPGenerator thatTPGen = new TPGenerator(thatBlock, false);

            thisTPGen.Next = thatTPGen;
            thatTPGen.Next = null;

            return thisTPGen.Compute(TPGenOptions.ComputeTPred);
        }

        static public Expr ComputeChoComposedTransitionPredicate(AtomicBlock thisBlock, AtomicBlock thatBlock)
        {
            TPGenerator thisTPGen = new TPGenerator(thisBlock, false);
            TPGenerator thatTPGen = new TPGenerator(thatBlock, false);

            thisTPGen.Next = null;
            thatTPGen.Next = null;

            return Expr.Or(
                thisTPGen.Compute(TPGenOptions.ComputeTPred),
                thatTPGen.Compute(TPGenOptions.ComputeTPred)
                );
        }

        static public bool CheckSimulation(Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, VariableSeq auxVars)
        {
            bool wpok = false;
            bool xpok = false;

            bool result = CheckSimulation(inv, thisTPGen, thatTPGen, false, false, auxVars, ref wpok, ref xpok);
            if (result) Statistics.Count("SimulationCheck_WithoutQuant");
            else
            {
                result = CheckSimulation(inv, thisTPGen, thatTPGen, false, true, auxVars, ref wpok, ref xpok);
                if (result) Statistics.Count("SimulationCheck_WithUnifiedHavocs");
                else
                {
                    result = CheckSimulation(inv, thisTPGen, thatTPGen, true, false, auxVars, ref wpok, ref xpok);
                    if (result) Statistics.Count("SimulationCheck_WithQuant");
                }
            }
            return result;
        }


        static public bool CheckSimulation(Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, bool useQuant, bool unifyHavocs, VariableSeq auxVars, ref bool wpok, ref bool xpok)
        {
            if (unifyHavocs)
            {
                thisTPGen.ResetUnifiedHavocs();
                thatTPGen.ResetUnifiedHavocs();
            }

            TPGenOptions thisOptions = TPGenOptions.ComputeWPre(Expr.True);
            thisOptions.unifyHavocs = unifyHavocs;
            thisOptions.useQuant = useQuant;
            Expr thisWP = thisTPGen.Compute(thisOptions);

            TPGenOptions thatOptions = TPGenOptions.ComputeWPre(Expr.True);
            thatOptions.unifyHavocs = unifyHavocs;
            thatOptions.useQuant = useQuant;
            Expr thatWP = thatTPGen.Compute(thatOptions);
            
            Expr condition = null;

            if (!wpok)
            {
				condition = Expr.And(inv, Expr.Not(thisWP));
				
				// quantify hidden variables
				VariableSeq hiddenVars = thisTPGen.APLBlock.procState.HiddenVars;
				hiddenVars.AddRange(ProofState.GetInstance().HiddenVars);
				if (hiddenVars.Length > 0)
					condition = new ExistsExpr(Token.NoToken, hiddenVars, condition);

				wpok = Prover.GetInstance().CheckUnSat(condition);
				
				if (!wpok)
				{
					condition = Expr.Imp(condition, Expr.Not(thatWP));
					wpok = Prover.GetInstance().CheckValid(condition);
				}
            }

            if (unifyHavocs)
            {
                thisTPGen.ResetUnifiedHavocs();
                thatTPGen.ResetUnifiedHavocs();
            }

            if(!xpok)
            {
                thisOptions = TPGenOptions.ComputeTPred;
                thisOptions.unifyHavocs = unifyHavocs;
                thisOptions.useQuant = useQuant;
                thisOptions.singleHavoc = false;
                Expr thisTrp = thisTPGen.Compute(thisOptions);

                condition = Logic.And(inv, thisTrp);

				// quantify hidden variables
				VariableSeq hiddenVars = thisTPGen.APLBlock.procState.HiddenVars;
				hiddenVars.AddRange(thisTPGen.APLBlock.procState.PrimedHiddenVars);
				hiddenVars.AddRange(ProofState.GetInstance().HiddenVars);
				hiddenVars.AddRange(ProofState.GetInstance().PrimedHiddenVars);
				if (hiddenVars.Length > 0)
					condition = new ExistsExpr(Token.NoToken, hiddenVars, condition);

                xpok = Prover.GetInstance().CheckUnSat(condition);

                if (!xpok)
                {
                    thatOptions = TPGenOptions.ComputeTPred;
                    thatOptions.unifyHavocs = unifyHavocs;
                    thatOptions.useQuant = useQuant;
                    thatOptions.singleHavoc = useQuant && !unifyHavocs;
                    Expr thatTrp = thatTPGen.Compute(thatOptions);

                    condition = Expr.Imp(condition, Expr.Or(Expr.Not(thatWP), thatTrp));
                    xpok = Prover.GetInstance().CheckValid(condition);
                }
            }

            return (wpok && xpok);
        }

        static public bool MoverCheck(Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, bool useQuant, bool unifyHavocs, MoverCheck mc)
        {
            //--------------------------------------------
            //if (isright)
            //{
            //    // check post, see [POPL'10]
            //    if (!Logic.CheckPost(inv, thisTPGen, thatTPGen))
            //    {
            //        return new MoverCheck(thisTPGen.APLBlock as AtomicBlock, thatTPGen.APLBlock as AtomicBlock, isright, "Post check failed!");
            //    }
            //}
            //--------------------------------------------------------------------

            if (unifyHavocs)
            {
                thisTPGen.ResetUnifiedHavocs();
                thatTPGen.ResetUnifiedHavocs();
            }

            //-----------------------------------------------
            if (mc.isRight) thisTPGen.assumeAsserts = true;
            //-----------------------------------------------

            //-----------------------------------------------
            // compute prestate constraint, see [POPL'10]
            Expr preState = Expr.True;
            //TPGenOptions preStateOptions = TPGenOptions.ComputeWPre(Expr.True);
            //preStateOptions.unifyHavocs = unifyHavocs;
            //preStateOptions.useQuant = useQuant;
            //if (isright)
            //{
            //    preState = thisTPGen.Compute(preStateOptions);
            //}
            //else
            //{
            //    preState = thatTPGen.Compute(preStateOptions);
            //}
            //-----------------------------------------------

            TPGenOptions thisOptions = TPGenOptions.ComputeWPre(Expr.True);
            thisOptions.unifyHavocs = unifyHavocs;
            thisOptions.useQuant = useQuant;

            thisTPGen.Next = thatTPGen; thatTPGen.Next = null;
            Expr thisWP = thisTPGen.Compute(thisOptions);
            
            TPGenOptions thatOptions = TPGenOptions.ComputeWPre(Expr.True);
            thatOptions.unifyHavocs = unifyHavocs;
            thatOptions.useQuant = useQuant;

            thatTPGen.Next = thisTPGen; thisTPGen.Next = null;
            Expr thatWP = thatTPGen.Compute(thatOptions);

            Expr condition = null;

            if (!mc.wpOK)
            {
                condition = Logic.And(preState, inv, Expr.Not(thisWP));

				// quantify hidden variables
				VariableSeq hiddenVars = thisTPGen.APLBlock.procState.HiddenVars;
				hiddenVars.AddRange(ProofState.GetInstance().HiddenVars);
				if (hiddenVars.Length > 0)
					condition = new ExistsExpr(Token.NoToken, hiddenVars, condition);

                mc.wpOK = Prover.GetInstance().CheckValid(condition);

				if (!mc.wpOK)
				{
					condition = Expr.Imp(condition, Expr.Not(thatWP));
					mc.wpOK = Prover.GetInstance().CheckValid(condition);
				}
            }
            if (unifyHavocs)
            {
                thisTPGen.ResetUnifiedHavocs();
                thatTPGen.ResetUnifiedHavocs();
            }

            if (!mc.xpOK)
            {
                thisOptions = TPGenOptions.ComputeTPred;
                thisOptions.unifyHavocs = unifyHavocs;
                thisOptions.useQuant = useQuant;
                thisOptions.singleHavoc = false;

                thisTPGen.Next = thatTPGen; thatTPGen.Next = null;
                Expr thisTrp = thisTPGen.Compute(thisOptions);

                condition = Logic.And(preState, inv, thisTrp);

				// quantify hidden variables
				VariableSeq hiddenVars = thisTPGen.APLBlock.procState.HiddenVars;
				hiddenVars.AddRange(thisTPGen.APLBlock.procState.PrimedHiddenVars);
				hiddenVars.AddRange(ProofState.GetInstance().HiddenVars);
				hiddenVars.AddRange(ProofState.GetInstance().PrimedHiddenVars);
				if (hiddenVars.Length > 0)
					condition = new ExistsExpr(Token.NoToken, hiddenVars, condition);

                mc.xpOK = Prover.GetInstance().CheckUnSat(condition);

                if (!mc.xpOK)
                {
                    thatOptions = TPGenOptions.ComputeTPred;
                    thatOptions.unifyHavocs = unifyHavocs;
                    thatOptions.useQuant = useQuant;
                    thatOptions.singleHavoc = useQuant && !unifyHavocs;

                    thatTPGen.Next = thisTPGen; thisTPGen.Next = null;
                    Expr thatTrp = thatTPGen.Compute(thatOptions);

                    condition = Expr.Imp(condition, Expr.Or(Expr.Not(thatWP), thatTrp));
                    mc.xpOK = Prover.GetInstance().CheckValid(condition);
                }
            }

            //-----------------------------------------------
            if (mc.isRight) thisTPGen.assumeAsserts = false;
            //-----------------------------------------------

            return (mc.wpOK && mc.xpOK);
        }

        // for tressa; MoverCheck is overloaded with a different set of formal parameters
        static public bool MoverCheck(Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen, MoverCheck mc)
        {

            //-----------------------------------------------
            // for tressa; not really, the mover check has changed in general; this will be a test-case.
            // eventually, the other right mover checks will have to be updated.
            // if (mc.isRight) thisTPGen.assumeAsserts = true;
            //-----------------------------------------------

            //-----------------------------------------------
            // compute prestate constraint, see [POPL'10]
            // Expr preState = Expr.True;
            //TPGenOptions preStateOptions = TPGenOptions.ComputeWPre(Expr.True);
            //preStateOptions.unifyHavocs = unifyHavocs;
            //preStateOptions.useQuant = useQuant;
            //if (isright)
            //{
            //    preState = thisTPGen.Compute(preStateOptions);
            //}
            //else
            //{
            //    preState = thatTPGen.Compute(preStateOptions);
            //}
            //-----------------------------------------------

            // update to calculate strongest post condition
            TPGenOptions thisOptions = TPGenOptions.ComputeSPost(inv); // this inv might be redundant
            thisOptions.unifyHavocs = false;
            thisOptions.useQuant = true;

            thisTPGen.Next = thatTPGen; thatTPGen.Next = null;
            Expr thisSP = thisTPGen.ComputeSP(thisOptions, inv); 
            // Expr thisSP = thisTPGen.Compute(thisOptions, inv);


            TPGenOptions thatOptions = TPGenOptions.ComputeSPost(inv); // this inv might be redundant
            thatOptions.unifyHavocs = false;
            thatOptions.useQuant = true;

            thatTPGen.Next = thisTPGen; thisTPGen.Next = null;
            Expr thatSP = thatTPGen.ComputeSP(thatOptions, inv);
            // Expr thatSP = thatTPGen.Compute(thatOptions, inv); // at this point, both sp's have been calculated

            // enumerate all the variables in either of the atomic actions (hence the free variables of the sp's).

            ProofState ps = ProofState.GetInstance();
            ICollection gVars = ps.globalVars.Values;
            ICollection LVarsthis = thisTPGen.APLBlock.procState.localVars.Values;
            ICollection LVarsthat = thatTPGen.APLBlock.procState.localVars.Values;
            
            Hashtable varmap_nontodouble = new Hashtable();
            Hashtable varmap_nontosingle = new Hashtable();
            Hashtable varmap_singletodouble = new Hashtable();

            foreach (Variable v in gVars)
            {
                IdentifierExpr vexprp = ps.GetPrimedExpr(v);
                IdentifierExpr vexprpp = MakeDoublePrimedExpr(v);
                varmap_nontodouble.Add(v, vexprpp);
                varmap_nontosingle.Add(v, vexprp);
                varmap_singletodouble.Add(vexprp.Decl, vexprpp);
            }
            foreach (Variable v in LVarsthis)
            {
                Variable hv = thisTPGen.CheckHideVar(v).Decl;
                IdentifierExpr hexprp = thisTPGen.CheckHideVar(thisTPGen.APLBlock.procState.GetPrimedExpr(v).Decl);
                IdentifierExpr hexprpp = MakeDoublePrimedExpr(hv);
                varmap_nontodouble.Add(hv, hexprpp);
                varmap_nontosingle.Add(hv, hexprp);
                varmap_singletodouble.Add(hexprp.Decl, hexprpp);
            }
            foreach (Variable v in LVarsthat)
            {
                Variable hv = thatTPGen.CheckHideVar(v).Decl;
                IdentifierExpr hexprp = thatTPGen.CheckHideVar(thatTPGen.APLBlock.procState.GetPrimedExpr(v).Decl);
                IdentifierExpr hexprpp = MakeDoublePrimedExpr(hv);
                varmap_nontodouble.Add(hv, hexprpp);
                varmap_nontosingle.Add(hv, hexprp);
                varmap_singletodouble.Add(hexprp.Decl, hexprpp);
            }
            
            Expr condition = null;
            Expr cond_reused = null;

            thisTPGen.ResetUnifiedHavocs();
            thatTPGen.ResetUnifiedHavocs();

            if (!mc.xpOK)
            {
                thisOptions = TPGenOptions.ComputeTPred;
                thisOptions.unifyHavocs = false;
                thisOptions.useQuant = true;
                thisOptions.singleHavoc = true;

                thisTPGen.Next = thatTPGen; thatTPGen.Next = null;
                Expr thisTrp = thisTPGen.Compute(thisOptions);

                condition = Logic.And(inv, thisTrp); 

                // quantify hidden variables
                VariableSeq hiddenVars = thisTPGen.APLBlock.procState.HiddenVars;
                hiddenVars.AddRange(thisTPGen.APLBlock.procState.PrimedHiddenVars);
                hiddenVars.AddRange(ProofState.GetInstance().HiddenVars);
                hiddenVars.AddRange(ProofState.GetInstance().PrimedHiddenVars);
                if (hiddenVars.Length > 0)
                    condition = new ExistsExpr(Token.NoToken, hiddenVars, condition);

                mc.xpOK = Prover.GetInstance().CheckUnSat(condition); // checks whether the transition is impossible

                // cond_reused is to be used in the hack below.
                cond_reused = condition; 

                if (!mc.xpOK)
                {
                    // checking whether this < that ---- this stands for the right-hand side, that for the left-hand side.
                    // this was already calculated above, calculating that.
                    thatOptions = TPGenOptions.ComputeTPred;
                    thatOptions.unifyHavocs = false;
                    thatOptions.useQuant = true;
                    thatOptions.singleHavoc = true;

                    thatTPGen.Next = thisTPGen; thisTPGen.Next = null;
                    Expr thatTrp = thatTPGen.Compute(thatOptions);

                    // not necessary after modification; thisSP and thatSP are already over primed variables
                    // Expr thisSPprime = Logic.Substitute(varmap_nontosingle, thisSP);
                    // Expr thatSPprime = Logic.Substitute(varmap_nontosingle, thatSP);

                    // inv && tau_this ==> [ (!psi_this ==> !psi_that) && (!psi_that || tau_that) ]
                    // this formula is not entirely true. 
                    // the real sound formula should have the final conjunct as follows:
                    // (!psi_that(s') && (exists s0. tau_that(s0,s')) || tau_that(s,s'))
                    // however, existential quantification is problematic, so beware!!
                    condition = Expr.Imp(condition, 
                                         Expr.And(Expr.Imp(Expr.Not(thisSP), Expr.Not(thatSP)), 
                                                  Expr.Or(Expr.Not(thatSP), thatTrp))); 
                    mc.xpOK = Prover.GetInstance().CheckValid(condition);
                    if (mc.isLeft)
                    {
                        // give mc.xpOK yet another chance with hack.
                        // for left-mover check, the condition has to be updated with the hack.
                        // inv && tau_this && psi_alpha ==> [ (!psi_this ==> !psi_that) && (!psi_that || tau_that) ]
                        // this is not efficient; the hack check should proceed the normal check.
                        if (!mc.xpOK) 
                        {
                            thatOptions = TPGenOptions.ComputeSPost(inv);
                            thatOptions.unifyHavocs = false;
                            thatOptions.useQuant = true;
                            thatTPGen.Next = null;
                            Expr alphaSP = thisTPGen.ComputeSP(thatOptions,inv);
                            // Expr alphaSP = thisTPGen.Compute(thatOptions, inv);
                            // not necessary; alphaSP is already over primed variables
                            // Expr alphaSPprime = Logic.Substitute(varmap_nontosingle, alphaSP);

                            condition = Expr.Imp(Expr.And(cond_reused, alphaSP),
                                                 Expr.And(Expr.Imp(Expr.Not(thisSP), Expr.Not(thatSP)),
                                                          Expr.Or(Expr.Not(thatSP), thatTrp)));
                            mc.xpOK = Prover.GetInstance().CheckValid(condition);
                        }
                        if (mc.xpOK)
                        {
                            // if right-mover was being checked, the following is not necessary.
                            // note that, for left-mover thatTPgen holds alpha, thisTPGen holds beta.
                            thatOptions = TPGenOptions.ComputeTPred;
                            thatOptions.unifyHavocs = false;
                            thatOptions.useQuant = true;
                            thatOptions.singleHavoc = true;
                            thatTPGen.Next = null;
                            Expr alphaTrp = thatTPGen.Compute(thatOptions);

                            thisOptions = TPGenOptions.ComputeTPred;
                            thisOptions.unifyHavocs = false;
                            thisOptions.useQuant = true;
                            thisOptions.singleHavoc = true;
                            thisTPGen.Next = null;
                            Expr betaTrp = thisTPGen.Compute(thisOptions);

                            thisOptions = TPGenOptions.ComputeSPost(inv);
                            thisOptions.unifyHavocs = false;
                            thisOptions.useQuant = true;
                            thisTPGen.Next = null;
                            Expr betaSP = thisTPGen.ComputeSP(thisOptions,inv);
                            // Expr betaSP = thisTPGen.Compute(thisOptions, inv);

                            Expr tau_betanontodouble = Logic.Substitute(varmap_singletodouble, betaTrp);
                            Expr tau_alphadoubletosingle = Logic.Substitute(varmap_nontodouble, alphaTrp);
                            Expr psi_betadouble = Logic.Substitute(varmap_singletodouble, betaSP);
                            // Expr psi_betadouble = Logic.Substitute(varmap_nontodouble, betaSP);
                            // not necessary, betaSP is already over primed variables
                            // Expr psi_betasingle = Logic.Substitute(varmap_nontosingle, betaSP);

                            // inv && tau_beta(s0,s2) && !psi_beta(s2) && tau_alpha(s2,s1) ==> !psi_beta(s1)
                            condition = Expr.Imp(Logic.And(inv, tau_betanontodouble,
                                                           Expr.Not(psi_betadouble),
                                                           tau_alphadoubletosingle),
                                                 Expr.Not(betaSP));

                            mc.xpOK = Prover.GetInstance().CheckValid(condition);
                        }
					}
                }
            }

            //-----------------------------------------------
            // this remains unchanged throughout this method, no need to reassign a value.
            // if (mc.isRight) thisTPGen.assumeAsserts = false;
            //-----------------------------------------------
            // for tressa, mc.wpOK is irrelevant; just set it to the value of xpOK
            mc.wpOK = mc.xpOK;

            return (mc.wpOK && mc.xpOK);
        }

        public static bool CheckPost(Expr inv, TPGenerator thisTPGen, TPGenerator thatTPGen)
        {
            Debug.Assert(thisTPGen.Next == null && thatTPGen.Next == null);

            Expr gate = thatTPGen.Compute(TPGenOptions.ComputeWPre(Expr.True));
            Expr tran = thisTPGen.Compute(TPGenOptions.ComputeTPred);

            Expr gatePrime = thatTPGen.APLBlock.procState.MakePrime(gate);

            Expr condition = Expr.Imp(
                                    Logic.And(inv, gate, tran),
                                    gatePrime);
            return Prover.GetInstance().CheckValid(condition);
        }

        public static Expr MakeOld(IdentifierExpr identifierExpr)
        {
            return new OldExpr(Token.NoToken, identifierExpr);
        }

        public static Expr MakeOld(Variable var)
        {
            return MakeOld(new IdentifierExpr(Token.NoToken, var));
        }

        public static Expr MakeOld(Expr expr)
        {
            return (Expr)new MyOldMaker().Visit(expr);
        }

        internal static Expr FrameCondition(Expr map, List<Expr> indexes)
        {
            MapType mt = map.Type.AsMap;

            VariableSeq dummySeq = new VariableSeq();
            List<Expr> dummyList = new List<Expr>();
            for (int i = 0; i < indexes.Count; ++i)
            {
                Variable dummy = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "dummy", mt.Arguments[i]));
                dummySeq.Add(dummy);
                dummyList.Add(new IdentifierExpr(Token.NoToken, dummy));
            }

            Expr oldFselect = Expr.Select(new OldExpr(Token.NoToken, map), dummyList);
            Expr newFselect = Expr.Select(map, dummyList);

            Expr body = Expr.True;
            for (int i = 0; i < indexes.Count; ++i)
            {
                body = Expr.And(body, Expr.Eq(dummyList[i], indexes[i]));
            }
            body = Expr.Or(body, Expr.Eq(oldFselect, newFselect));

            return Logic.ForallExpr(dummySeq, body);
        }

        internal static Set<Expr> GetTopConjuncts(Expr inv)
        {
            Set<Expr> set = new Set<Expr>();

            Queue<Expr> q = new Queue<Expr>();
            q.Enqueue(inv);

            while (q.Count > 0)
            {
                Expr e = q.Dequeue();
                bool enqueued = false;

                if (e is NAryExpr)
                {
                    NAryExpr ne = e as NAryExpr;
                    if (ne.Fun is BinaryOperator)
                    {
                        BinaryOperator bo = ne.Fun as BinaryOperator;
                        if (bo.Op == BinaryOperator.Opcode.And)
                        {
                            q.Enqueue(ne.Args[0]);
                            q.Enqueue(ne.Args[1]);
                            enqueued = true;
                        }
                    }
                }

                if (!enqueued)
                {
                    set.Add(e);
                }
            }
            return set;
        }

    } // end class Logic

} // end namespace QED