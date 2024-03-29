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
    using QInvariant = InvariantStore.QInvariant;


    public class InvariantStore
    {
        public class QInvariant
        {
            internal Expr Formula;
            internal string Name;
            internal string Desc;
            internal bool RTChecked;
            internal bool Introduced;

            public QInvariant(string name, string desc, Expr formula)
            {
                this.Name = name;
                this.Desc = desc;
                this.Formula = formula;
                this.RTChecked = this.Introduced = false;
            }

            static internal QInvariant Parse(string line)
            {
                CmdParser parser = new CmdParser(line);

                string name = parser.NextAsString();
                string desc = "";
                if (parser.NextStartsWith("\""))
                {
                    desc = parser.NextAsString();
                    desc = desc.Substring(1, desc.Length - 2);
                }
                Expr formula = parser.NextAsExpr();

                return new QInvariant(name, desc, formula);
            }

            public override string ToString()
            {
                StringBuilder strb = new StringBuilder();
                if (this.Name != null)
                {
                    strb.Append(this.Name);
                }
                if (this.Desc != null && this.Desc != "")
                {
                    strb.Append("\"").Append(this.Desc).Append("\" ");
                }
                strb.Append(this.Formula.ToString());

                return strb.ToString();
            }
            
        }

        internal int nextid = 0;
        internal Hashtable map = new Hashtable();
        public ICollection<QInvariant> GetInvariants()
        {
            ICollection<QInvariant> set = new Set<QInvariant>();
            foreach (QInvariant qinv in this.map.Values)
            {
                set.Add(qinv);
            }
            return set;
        }

        static private InvariantStore instance;
        static public InvariantStore GetInstance()
        {
            if (instance == null)
            {
                instance = new InvariantStore();
            }
            return instance;
        }
        private InvariantStore()
        {
            this.Clear();
        }

        static public InvariantStore LoadFromFile(string filename)
        {
            InvariantStore store = new InvariantStore();
            using (StreamReader reader = new StreamReader(filename))
            {
                while (!reader.EndOfStream)
                {
                    string line = reader.ReadLine();
                    QInvariant inv = QInvariant.Parse(line);
                    if (inv != null)
                    {
                        store.Add(inv);
                    }
                }
            }
            InvariantStore.instance = store;
            return store;
        }

        // adds a new invariant if its name does not exist in the current map
        public void Add(QInvariant inv)
        {
            string name = inv.Name;
            if (name == null)
            {
                name = "Inv" + nextid.ToString();
                ++nextid;

                Debug.Assert(!map.ContainsKey(name));
                this.map.Add(name, inv);
            }
            else
            {
                if (!map.ContainsKey(name))
                {
                    this.map.Add(name, inv);
                }
            }
        }

        public QInvariant Get(string name)
        {
            if (name == null || !map.ContainsKey(name))
            {
                return null;
            }
            return this.map[name] as QInvariant;
        }

        public string Report()
        {
            StringBuilder strb = new StringBuilder();
            foreach (string name in map.Keys)
            {
                strb.Append(Get(name).ToString()).AppendLine();
            }
            return strb.ToString();
        }

        internal void Clear()
        {
            this.map.Clear();
            this.nextid = 0;
        }
    }


    public class InvariantCheck
    {
        public AtomicBlock atomicBlock;
        public VariableSeq hiddenVars;
        public Expr invariant;
        public bool success = true;
        public Set<Expr> failingInvs;
        public ErrorModel errModel;

        public InvariantCheck(AtomicBlock ablock, VariableSeq hvars, Expr inv)
        {
            this.atomicBlock = ablock;
            this.invariant = inv;
            this.hiddenVars = hvars;
        }

        public void SetFailure(Set<Expr> fcores, ErrorModel emodel)
        {
            this.success = false;
            this.failingInvs = fcores == null ? new Set<Expr>() : new Set<Expr>(fcores);
            this.errModel = emodel;
        }

        // this requires that there is no old() in trans but primes, and trans is not compact but full
        //static public bool IsReflexive(ProcedureState procState, Expr invs, Expr gate, Expr trans)
        //{
        //    // transition[V/V']
        //    trans = procState.MakeUnprimed(trans);

        //    // (inv && gate) ==> transition[V/V']
        //    Expr condition = Expr.Imp(Expr.And(invs, gate), trans);

        //    return Prover.GetInstance().CheckValid(condition);
        //}

        // this requires that there is no old() in trans but primes, and trans is not compact but full
        static public Set<Expr> DoCheck(VariableSeq hiddenVars, Expr inv, ProcedureState procState, Expr gate, Expr trans)
        {
            //----------------------------------------
            // label the conjuncts
            // Expr invp = ProofState.GetInstance().MakePrime(inv);

            //----------------------------------------
            Expr invLeft = Expr.And(ProofState.GetInstance().InvariantForProc(procState), inv);
            Expr invRight = inv;
            if (hiddenVars.Length > 0)
            {
                invLeft = Logic.ExistsExpr(hiddenVars, invLeft);
                invRight = Logic.ExistsExpr(hiddenVars, invRight);
            }
            //----------------------------------------

            Hashtable invMap = new Hashtable();
            Set<Expr> conjuncts = Logic.GetTopConjuncts(invRight);
            int count = 0;
            invRight = Expr.True;
            foreach (Expr c in conjuncts)
            {
                string lbl = "InvLbl_" + (count++);
                Expr pe = procState.MakePrime(c);
                invMap.Add(lbl, c);

                invRight = Expr.And(invRight, new LabeledExpr(lbl, pe, false));
            }
            
            //----------------------------------------
            // inv ==> (!gate || (gate && trans ==> invp))
            // Expr condition = Expr.Imp(inv, Expr.Or(Expr.Not(gate), Expr.Imp(Expr.And(gate, trans), invp)));
            Expr condition = Expr.Imp(invLeft, Expr.Imp(Expr.And(gate, trans), invRight));

            bool result = Prover.GetInstance().CheckValid(condition);

            //----------------------------------------
            if (!result)
            {
                Set<Expr> failed = new Set<Expr>();
                foreach (string lbl in Prover.GetInstance().failedLabels)
                {
                    if (lbl.StartsWith("InvLbl_"))
                    {
                        failed.Add(invMap[lbl] as Expr);
                    }
                }
                if (failed.Count == 0)
                {
                    Output.AddError("Invariant check failed with no failed labels!");
                }
                return failed;
            }
            return null;
        }

        public bool Run()
        {
            Expr gate = this.atomicBlock.GatePredicate(Expr.True);
            Expr trans = this.atomicBlock.TransitionPredicate;

            Set<Expr> failed = DoCheck(this.hiddenVars, this.invariant, this.atomicBlock.procState, gate, trans);
            if (failed == null)
            {
                return true;
            }

            SetFailure(failed, Prover.GetInstance().GetErrorModel());

            // code for failing checks
            StringBuilder strb = new StringBuilder();
            strb.AppendLine(">> Begin failed invariants");
            foreach (Expr e in failed)
            {
                strb.AppendLine(Output.ToString(e));
            }
            strb.AppendLine(">> End failed invariants");
            Output.AddLine(strb.ToString());
#if false
            // generate model for the failed block
            Prover.EnableModel = true;

            // repeat the check again
            failed = DoCheck(this.invariant, gate, trans);
            SetFailure(failed, Prover.GetInstance().GetErrorModel());

            Prover.EnableModel = false;
#endif
            ProofState.GetInstance().LastInvariantChecks = new List<InvariantCheck>();
            ProofState.GetInstance().LastInvariantChecks.Add(this);

            return false;
        }

        public override string ToString()
        {
            if (this.success)
            {
                return "Success"; // this is usually not printed
            }
            else
            {
                StringBuilder strb = new StringBuilder("Atomic block " + this.atomicBlock.UniqueLabel + " does not preserve the invariant!\n");
                strb.AppendLine(">> Begin failed invariants");
                foreach (Expr e in this.failingInvs)
                {
                    strb.AppendLine(Output.ToString(e));
                }
                strb.AppendLine(">> End failed invariants");
                return strb.ToString();
            }
        }

        //static public string Report(List<MoverCheck> mcs)
        //{
        //    Debug.Assert(mcs != null);
        //    StringBuilder strb = new StringBuilder();
        //    foreach (MoverCheck mc in mcs)
        //    {
        //        if (!mc.Success)
        //        {
        //            strb.AppendLine(mc.ToString());
        //        }
        //    }
        //    return strb.ToString();
        //}
    }

    public class FormulaCommand : ProofCommand
    {
        public string Name;
        public string Desc;
        public Expr Formula;

        public FormulaCommand(string name, string desc, Expr formula)
            : base("formula")
        {
            this.Name = name;
            this.Desc = desc;
            this.Formula = formula;

            desc = "formula " + formula;
        }

        public static string Usage()
        {
            return "formula name \"description\" invariantFormula";
        }

        public static ProofCommand Parse(CmdParser parser)
        {
            if (parser.NextAsString().Equals("formula"))
            {
                string name = parser.NextAsString();
                string desc = "";
                if (parser.NextStartsWith("\""))
                {
                    desc = parser.NextAsString();
                    desc = desc.Substring(1, desc.Length - 2);
                }
                Expr formula = parser.RestAsExpr();
                return new FormulaCommand(name, desc, formula);
            }
            return null;
        }

        override public bool Run(ProofState proofState)
        {
            proofState.ResolveTypeCheckExpr(this.Formula, false);

            QInvariant qinv = new QInvariant(this.Name, this.Desc, this.Formula);
            InvariantStore.GetInstance().Add(qinv);

            Output.Add("Added the invariant:" + qinv.ToString());

            return false;
        }

        override public void Print()
        {
            Output.LogLine("formula " + this.Name + " \"" + this.Desc + "\"" + " " + this.Formula.ToString());
        }

    } // end class InvariantIntroCommand

public class InvariantCommand : ProofCommand
{
    public string nameOrExpr;
    public QInvariant Invariant;

	public InvariantCommand(string noe)
		: base("invariant")
	{
		this.nameOrExpr = noe;
		
		desc = "invariant" + " " + noe;
	}

    public static string Usage()
    {
        return "invariant invariantFormula | nameOfFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("invariant"))
        {
            string inv = parser.RestAsString();
            return new InvariantCommand(inv);
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {
        this.Invariant = InvariantStore.GetInstance().Get(nameOrExpr);
        if (this.Invariant == null)
        {
            // expression
            this.Invariant = new QInvariant(null, null, Qoogie.ParseExpr(this.nameOrExpr));
        }

        proofState.ResolveTypeCheckExpr(this.Invariant.Formula, false);
        this.Invariant.RTChecked = true;

        DoRun(proofState, this.Invariant);

        return false;

    }

    static public bool DoRun(ProofState proofState, QInvariant invariant)
    {
        Debug.Assert(invariant != null);

        bool tmp = CommandLineOptions.Clo.RestartProverPerVC;
        CommandLineOptions.Clo.RestartProverPerVC = false;

        Expr invs = Expr.And(proofState.Invariant, invariant.Formula);
        
        if (Prover.GetInstance().CheckValid(Expr.Imp(invs, Expr.False)))
        {
            Output.AddError("The invariant implies False !!!");
            return false;
        }


        bool result = true;

        if (Prover.GetInstance().CheckValid(Expr.Imp(proofState.Invariant, invariant.Formula)))
        {
            Output.AddLine("The invariant is already implied by the existing invariant!");
            // TODO: for now we keep implied invariants as well 
            // return false;
        }
        else
        {
            if (proofState.config.GetBool("Invariant", "CheckWithRG", false))
            {
                // TODO: the first invariant check below does not consider assertions, use the second one for a correct treatment !!!

                RelyGuarantee rg = new RelyGuarantee(invs, proofState.Rely, proofState.Guar);

                foreach (ProcedureState procState in proofState.procedureStates.Values)
                {
                    if ((!procState.IsReduced) || procState.IsPublic)
                    {
                        if (!rg.CheckProcedure(proofState, procState))
                        {
                            Output.LogLine("The new invariant does not hold!");

                            proofState.LastErrorTrace = rg.LastErrorTrace;
                            result = false;
                            break;
                        }
                    }
                }
            }
            else
            {
                List<AtomicBlock> atomicBlocks = proofState.AtomicBlocks;
                foreach (AtomicBlock atomicBlock in atomicBlocks)
                {
                    if (!atomicBlock.IsInvariant(invariant.Formula)) // calls the InvariantCheck class
                    {
                        result = false;
                        break;
                    }
                }
            }
        }

        // check if the new invariant is safe to add to the proof state
        if (result)
        {
            proofState.AddCheckedInvariant(invariant);
            Output.LogLine("Added the new program invariant: " + Output.ToString(invariant.Formula));
        }

        CommandLineOptions.Clo.RestartProverPerVC = tmp;

        return result;
    }	
	
	static public bool DoRun(ProofState proofState) {

        bool tmp = CommandLineOptions.Clo.RestartProverPerVC;
        CommandLineOptions.Clo.RestartProverPerVC = false;

        bool result = true;

        foreach (QInvariant invariant in proofState.invStore.GetInvariants())
        {
            proofState.ResolveTypeCheckExpr(invariant.Formula, false);
            invariant.RTChecked = true;
            
            Expr invs = invariant.Formula;

            if (Prover.GetInstance().CheckValid(Expr.Imp(invs, Expr.False)))
            {
                Output.AddError("The invariant implies False !!!");
                return false;
            }

            if (proofState.config.GetBool("Invariant", "CheckWithRG", false))
            {
                // TODO: the first invariant check below does not consider assertions, use the second one for a correct treatment !!!

                RelyGuarantee rg = new RelyGuarantee(invs, proofState.Rely, proofState.Guar);

                foreach (ProcedureState procState in proofState.procedureStates.Values)
                {
                    if ((!procState.IsReduced) || procState.IsPublic)
                    {
                        if (!rg.CheckProcedure(proofState, procState))
                        {
                            Output.LogLine("The new invariant does not hold!");

                            proofState.LastErrorTrace = rg.LastErrorTrace;
                            result = false;
                            break;
                        }
                    }
                }
            }
            else
            {
                List<AtomicBlock> atomicBlocks = proofState.AtomicBlocks;
                foreach (AtomicBlock atomicBlock in atomicBlocks)
                {
                    if (!atomicBlock.IsInvariant(invs)) // calls the InvariantCheck class
                    {
                        result = false;
                        break;
                    }
                }
            }

            // check if the new invariant is safe to add to the proof state
            if (result)
            {
                proofState.AddCheckedInvariant(invariant);
                Output.LogLine("Added the new program invariant: " + Output.ToString(invariant.Formula));
            }
            else
            {
                Output.LogLine("Failed while adding invariant: " + Output.ToString(invariant.Formula));
                break;
            }

        } // end foreach invariant

        CommandLineOptions.Clo.RestartProverPerVC = tmp;

        if (result && Prover.GetInstance().CheckValid(proofState.Invariant))
        {
            Output.AddLine("The current invariant is TRUE!");
            return true; // accept the invariant
        }

		return result;		
	}	
	
	override public void Print() {
		Output.LogLine("invariant " + this.nameOrExpr);
	}
	
} // end class InvariantCommand

//*************************************************************

public class LocalInvariantCommand : ProofCommand
{
	public Expr formula;
	public string procname;

	public LocalInvariantCommand(Expr inv, string name)
		: base("localinv")
	{
		this.formula = inv;
		this.procname = name;
		
		desc = "localinv" + " " + this.procname + " " +  Output.ToString(this.formula);
	}

    public static string Usage()
    {
        return "localinv procedureName invariantFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("localinv"))
        {
            string procname = parser.NextAsString();
            Expr linv = parser.RestAsExpr();
            return new LocalInvariantCommand(linv, procname);
        }
        return null;
    }
	
	override public bool Run(ProofState proofState) {
		
		ProcedureState procState = proofState.GetProcedureState(procname);
		procState.ResolveTypeCheckExpr(this.formula, false);

        bool tmp = CommandLineOptions.Clo.RestartProverPerVC;
        CommandLineOptions.Clo.RestartProverPerVC = false;

        Expr inv = proofState.InvariantForProc(procState);
        Expr invs = Expr.And(inv, this.formula);

        if (Prover.GetInstance().CheckValid(Expr.Imp(invs, Expr.False)))
        {
            Output.AddError("The invariant implies False !!!");
            return false;
        }

        bool result = true;

        if (Prover.GetInstance().CheckValid(Expr.Imp(inv, this.formula)))
        {
            Output.AddLine("The invariant is already implied by the existing invariant!");
            // TODO: for now we keep implied invariants as well 
            // return false;
        }
        else
        {
            if (proofState.config.GetBool("Invariant", "CheckWithRG", false))
            {
                // check the validity
                RelyGuarantee rg = new RelyGuarantee(invs, proofState.Rely, proofState.Guar);

                if ((!procState.IsReduced) || procState.IsPublic)
                {
                    if (!rg.CheckProcedure(proofState, procState))
                    {
                        Output.AddError("The new invariant does not hold!");

                        proofState.LastErrorTrace = rg.LastErrorTrace;

                        result = false;
                    }
                }
            }
            else
            {
                List<AtomicBlock> atomicBlocks = procState.AtomicBlocks;
                foreach (AtomicBlock atomicBlock in atomicBlocks)
                {
                    if (!atomicBlock.IsInvariant(this.formula))
                    {
                        result = false;
                        break;
                    }
                }
            }
        }

        // check if the new invariant is safe to add to the proof state
        if (result)
        {
            // if we reach here, the new invariant is safe to add to the procedure state
            procState.localinvs.Add(this.formula);

            Output.AddLine("Added the new program invariant: " + Output.ToString(this.formula));
        }

        CommandLineOptions.Clo.RestartProverPerVC = tmp;

        return false;
	}	
	
} // end class LocalInvariantCommand

public class TransInvCommand : ProofCommand
{
    public Expr formula;

    public TransInvCommand(Expr inv)
        : base("transinv")
    {
        this.formula = inv;

        desc = "transinv" + " " + Output.ToString(this.formula);
    }

    public static string Usage()
    {
        return "transinv invariantFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("transinv"))
        {
            Expr tinv = parser.RestAsExpr();
            return new TransInvCommand(tinv);
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {

        proofState.ResolveTypeCheckExpr(this.formula, true);

        Expr rely = Expr.And(proofState.Rely, this.formula);
        Expr guar = Expr.And(proofState.Guar, this.formula);

        // check the validity
        RelyGuarantee rg = new RelyGuarantee(proofState.Invariant, rely, guar);

        foreach (ProcedureState procState in proofState.procedureStates.Values)
        {
            if ((!procState.IsReduced) || procState.IsPublic)
            {
                if (!rg.CheckProcedure(proofState, procState))
                {
                    Output.LogLine("The new transition invariant does not hold!");
                    return true;
                }
            }
        }

        // if we reach here, the new transition invariant is safe to add to the proof state
        proofState.rely.Add(this.formula);
        proofState.guar.Add(this.formula);

        Output.LogLine("Added the new transition invariant: " + Output.ToString(this.formula));

        return false;

    }

} // end class InvariantCommand

public class SplitInvariantCommand : ProofCommand
{
    public Expr formula;

    public SplitInvariantCommand(Expr inv)
        : base("splitinv")
    {
        this.formula = inv;

        desc = "splitinv" + " " + Output.ToString(this.formula);
    }

    public static string Usage()
    {
        return "splitinv invariantFormula";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("splitinv"))
        {
            Expr sinv = parser.RestAsExpr();
            return new SplitInvariantCommand(sinv);
        }
        return null;
    }

    override public bool Run(ProofState proofState)
    {

        proofState.ResolveTypeCheckExpr(this.formula, true);

        proofState.splitInvariants.Add(this.formula);

        Output.LogLine("Added the new split invariant: " + Output.ToString(this.formula));

        return false;

    }

} // end class SplitInvariantCommand
} // end namespace QED