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
    using System.Text;
    using Microsoft.Basetypes;
    using QInvariant = InvariantStore.QInvariant;


    public class ProofState
    {

        public static volatile ProofState instance;

        public Program program;

        public Hashtable globalVars;

        public Hashtable auxVars;

        public Hashtable hiddenVars;

        public VariableSeq primes;

        public IdentifierExpr tidExpr;

        public IdentifierExpr tidxExpr;

        public Microsoft.Boogie.Type exceptionType;

        public IdentifierExpr exSkipExpr;
        public IdentifierExpr exReturnExpr;
        public IdentifierExpr exBreakExpr;
        public IdentifierExpr exContinueExpr;

        public Microsoft.Boogie.Type mutexType;
        public Variable mutexOwnerVar;
        public Procedure lockProc;
        public Procedure unlockProc;

        public Microsoft.Boogie.Type allocType;

        public IdentifierExpr allocExpr;
        public IdentifierExpr deallocExpr;
        public IdentifierExpr nullExpr;

        public Function subtypeFunction;
        public IDictionary<string, string> subtypeMap;

        //public IdentifierExpr errorExpr;

        public IdentifierExpr ownerMapExpr;

        public Hashtable primesMap;

        public string file;

        public IDictionary<string, ProcedureState> procedureStates;

        //public List<Expr> invs;
        public InvariantStore invStore;

        public List<Expr> splitInvariants;

        public List<Expr> rely;

        public List<Expr> guar;

        public ErrorTrace errorTrace;

        public Configuration config;

        public CallGraph callGraph;

        public List<MoverCheck> moverChecks; // from the last mover command
        public List<InvariantCheck> invariantChecks; // from the last mover command

        public ErrorTrace LastErrorTrace
        {
            get
            {
                return errorTrace;
            }
            set
            {
                errorTrace = value;
            }
        }

        public List<MoverCheck> LastMoverChecks
        {
            get
            {
                return moverChecks;
            }
            set
            {
                moverChecks = value;
            }
        }

        public List<InvariantCheck> LastInvariantChecks
        {
            get
            {
                return invariantChecks;
            }
            set
            {
                invariantChecks = value;
            }
        }


        //protected Hashtable atomicBlockMap;

        static public ProofState CreateInstance(Program prog, Configuration conf)
        {
            instance = new ProofState(prog, conf);
            instance.Init();
            return instance;
        }

        static public ProofState GetInstance()
        {
            Debug.Assert(instance != null);
            return instance;
        }

        public static void ResetInstance()
        {
            instance = null;
        }

        private ProofState(Program prog, Configuration conf)
        {
            this.program = prog;

            this.config = conf;

            this.procedureStates = new Dictionary<string, ProcedureState>();

            this.rely = new List<Expr>();

            this.guar = new List<Expr>();

            //InitErrorState();

            //InitOwnerMap(); // TODO: open ownermap later
        }

        public void Init()
        {
            InitTid();

            InitExceptions();

            InitAlloc();

            // inits this.inv
            InitInvariants();

            InitGlobalVars();

            // init logic class
            InitLogic();

            InitLocks();

            InitAPLStmtIds();

            this.procedureStates.Clear();
        }

        private void InitAPLStmtIds()
        {
            int max = 0;
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                if (decl is Implementation)
                {
                    Implementation impl = decl as Implementation;
                    Set<BigBlock> bbs = new BigBlocksCollector().Collect(impl.StructuredStmts);
                    foreach (BigBlock bb in bbs)
                    {
                        if (!bb.Anonymous)
                        {
                            string l = bb.LabelName;
                            Debug.Assert(l != null);
                            if (l.StartsWith("Atomic_") || l.StartsWith("Call_") || l.StartsWith("Try_") || l.StartsWith("Catch_") || l.StartsWith("Fork_") || l.StartsWith("Join_") || l.StartsWith("Par_") || l.StartsWith("Foreach_"))
                            {
                                int f = l.IndexOf("_");
                                l = l.Substring(f + 1);
                                f = l.IndexOf("_");
                                if (f >= 0)
                                {
                                    l = l.Substring(0, f);
                                }
                                int k = int.Parse(l);
                                if (k > max)
                                {
                                    max = k;
                                }
                            }
                        }
                    }
                }
            }
            APLStmt.ResetCounter(max);
        }

        private void InitLogic()
        {
            Logic.True = new IdentifierExpr(Token.NoToken, Qoogie.GetConstant(program, "True"));
            Logic.False = new IdentifierExpr(Token.NoToken, Qoogie.GetConstant(program, "False"));
        }
        // TODO: put all these to Prelud.Init(program)
        private void InitLocks()
        {
            this.mutexType = Qoogie.GetType(program, Prelude.MutexTypeName);
            this.mutexOwnerVar = Qoogie.GetGlobalVar(program, Prelude.MutexOwnerFieldName);

            this.lockProc = Qoogie.GetProcedure(program, Prelude.LockProcName);
            this.unlockProc = Qoogie.GetProcedure(program, Prelude.UnlockProcName);
        }

        private void InitExceptions()
        {
            this.exceptionType = Qoogie.GetType(program, Prelude.ExceptionTypeName);

            this.exSkipExpr = new IdentifierExpr(Token.NoToken, Qoogie.GetConstant(program, Prelude.ExSkipName));
            this.exReturnExpr = new IdentifierExpr(Token.NoToken, Qoogie.GetConstant(program, Prelude.ExReturnName));
            this.exBreakExpr = new IdentifierExpr(Token.NoToken, Qoogie.GetConstant(program, Prelude.ExBreakName));
            this.exContinueExpr = new IdentifierExpr(Token.NoToken, Qoogie.GetConstant(program, Prelude.ExContinueName));

            // get subtyping relationship
            subtypeFunction = Qoogie.GetFunction(program, "subtype");
            subtypeMap = new Dictionary<string, string>();
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Axiom axiom = decl as Axiom;
                if (axiom != null)
                {
                    Expr expr = axiom.Expr;
                    if (expr is NAryExpr)
                    {
                        NAryExpr nexpr = expr as NAryExpr;
                        if (nexpr.Fun.FunctionName == "subtype")
                        {
                            subtypeMap.Add(nexpr.Args[0].ToString(), nexpr.Args[1].ToString());
                        }
                    }
                }
            }
        }

        private void InitAlloc()
        {
            this.allocType = Qoogie.GetType(program, Prelude.AllocTypeName);

            this.allocExpr = new IdentifierExpr(Token.NoToken, Qoogie.GetConstant(program, Prelude.AllocName));
            this.deallocExpr = new IdentifierExpr(Token.NoToken, Qoogie.GetConstant(program, Prelude.DeallocName));
            this.nullExpr = new IdentifierExpr(Token.NoToken, Qoogie.GetConstant(program, Prelude.NullName));
        }

        public bool IsSubType(string sub, string sup)
        {
            // reflexive
            if (sub == sup) return true;

            // transitive
            string key = sub;
            while (subtypeMap.ContainsKey(key))
            {
                string val = subtypeMap[key];
                if (val == sup)
                {
                    return true;
                }
                key = val;
            }
            return false;
        }

        public void UpdateCallGraph()
        {
            this.callGraph = new CallGraph(this);
        }

        private void InitGlobalVars()
        {
            globalVars = new Hashtable();
            
            auxVars = new Hashtable();
            hiddenVars = new Hashtable();

            primesMap = new Hashtable();
            primes = new VariableSeq();

            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                GlobalVariable gvar = decl as GlobalVariable;
                if (gvar != null)
                {
                    AddGlobalVar(gvar);

                    if (QKeyValue.FindBoolAttribute(gvar.Attributes, "isaux"))
                    {
                        MakeAuxVar(gvar);
                    }

                    if (QKeyValue.FindBoolAttribute(gvar.Attributes, "ishidden"))
                    {
                        HideVar(gvar);
                    }
                }
                else
                {
                    Record record = decl as Record;
                    if (record != null)
                    {
                        foreach (Field f in record.fields)
                        {
                            AddGlobalVar(f.mapVar as GlobalVariable);
                        }
                    }
                }
            }
        }

        private void InitInvariants()
        {
            string invFile = config.GetStr("Input", "InvariantFile");
            if (invFile == null)
            {
                this.invStore = InvariantStore.GetInstance();
                this.invStore.Clear();
            }
            else
            {
                this.invStore = InvariantStore.LoadFromFile(invFile);
            }


            List<Declaration> topLevelDecls = new List<Declaration>(program.TopLevelDeclarations);
            foreach (Declaration decl in topLevelDecls)
            {
                Invariant inv = decl as Invariant;
                if (inv != null)
                {
                    invStore.Add(new QInvariant(null, null, inv.Expr));
                }
            }

            // split invariants
            this.splitInvariants = new List<Expr>();
        }

        //private void InitOwnerMap()
        //{
        //    // init owner map
        //    GlobalVariable ownerVar = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "owner", new MapType(Token.NoToken, new TypeVariableSeq(), new TypeSeq(BasicType.Int), BasicType.Int)));
        //    ownerMapExpr = new IdentifierExpr(Token.NoToken, ownerVar);
        //    AddGlobalVar(ownerVar);
        //}


        //private void InitErrorState()
        //{
        //    GlobalVariable errorVar = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "error", BasicType.Bool));
        //    errorExpr = new IdentifierExpr(Token.NoToken, errorVar);
        //    AddGlobalVar(errorVar);

        //    // rely does not change error
        //    Debug.Assert(rely != null);
        //    rely.Add(Expr.Eq(errorExpr, GetPrimedExpr(errorExpr)));
        //}

        private void InitTid()
        {
            Constant tidVar = Qoogie.GetConstant(program, Prelude.tidName);
            Constant tidxVar = Qoogie.GetConstant(program, Prelude.tidxName);

            Debug.Assert(tidVar != null && tidxVar!= null);

            this.tidExpr = new IdentifierExpr(Token.NoToken, tidVar);
            this.tidxExpr = new IdentifierExpr(Token.NoToken, tidxVar);

            //Constant tidVar = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, "tid", BasicType.Int));
            //Constant tidxVar = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, "tidx", BasicType.Int));
            //tidExpr = new IdentifierExpr(Token.NoToken, tidVar);
            //tidxExpr = new IdentifierExpr(Token.NoToken, tidxVar);

            //invs.Add(Expr.Neq(tidExpr, LiteralExpr.Literal(0)));
            //invs.Add(Expr.Neq(tidxExpr, LiteralExpr.Literal(0)));
            //invs.Add(Expr.Neq(tidExpr, tidxExpr));

            //program.TopLevelDeclarations.Add(tidVar);
            //program.TopLevelDeclarations.Add(tidxVar);
        }

        public string CurrentStateInfo()
        {
            StringBuilder strb = new StringBuilder();

            strb.Append("Invariant: ").Append(Output.ToString(ProofState.GetInstance().Invariant)).AppendLine();
            strb.Append("Rely: ").Append(Output.ToString(ProofState.GetInstance().Rely)).AppendLine();
            strb.Append("Guarantee: ").Append(Output.ToString(ProofState.GetInstance().Guar)).AppendLine();

            strb.AppendLine().Append("Procedures: ").AppendLine();
            foreach (ProcedureState procState in ProofState.GetInstance().procedureStates.Values)
            {
                strb.AppendLine("---------------------------");
                strb.AppendLine(procState.CurrentStateInfo());
            }

            strb.AppendLine("---------------------------");
            strb.AppendLine("Configuration");
            strb.AppendLine(config.Print());

            return strb.ToString();
        }

        //// this assume that label is of the form blockname@procname
        //public AtomicBlock GetAtomicBlock(string label) {
        //    // parse the label
        //    int idx = label.LastIndexOf('@');
        //    string atomname = label.Substring(0, idx);
        //    string procname = label.Substring(idx + 1);
        //    ProcedureState procState = GetProcedureState(procname);
        //    if (procState == null) return null;
        //    return procState.GetAtomicBlock(atomname);
        //}

        //public AtomicStmt GetAtomicStmt(string label, out ProcedureState procState)
        //{
        //    // parse the label
        //    int idx = label.LastIndexOf('@');
        //    string atomname = label.Substring(0, idx);
        //    string procname = label.Substring(idx + 1);
        //    procState = GetProcedureState(procname);
        //    if (procState == null) return null;
        //    return procState.GetAtomicStmt(atomname);
        //}

        
        //public List<AtomicStmt> AtomicStmts
        //{
        //    get
        //    {
        //        List<AtomicStmt> atoms = new List<AtomicStmt>();
        //        foreach (ProcedureState procState in procedureStates.Values)
        //        {
        //            atoms.AddRange(procState.AtomicStmts);
        //        }
        //        return atoms;
        //    }
        //}

        public List<AtomicBlock> AtomicBlocks
        {
            get
            {
                List<AtomicBlock> atoms = new List<AtomicBlock>();
                foreach (ProcedureState procState in procedureStates.Values)
                {
                    procState.ComputeAtomicBlocks();
                    atoms.AddRange(procState.AtomicBlocks);
                }
                return atoms;
            }
        }

        public List<ProcedureState> ProcedureStates
        {
            get
            {
                List<ProcedureState> procStates = new List<ProcedureState>();
                foreach (ProcedureState procState in procedureStates.Values)
                {
                    procStates.Add(procState);
                }
                return procStates;
            }
        }

        public Variable GetPrimedVar(Variable var)
        {
            return GetPrimedExpr(var).Decl;
        }

        public IdentifierExpr GetPrimedExpr(Variable var)
        {
            return (IdentifierExpr)primesMap[var];
        }

        public IdentifierExpr GetPrimedExpr(IdentifierExpr expr)
        {
            return GetPrimedExpr(expr.Decl);
        }

        public Expr MakePrime(Expr expr)
        {
            return Logic.Substitute(primesMap, expr);
        }

        public Expr MakeUnprimed(Expr expr)
        {
            Hashtable reverseMap = new Hashtable();

            Hashtable allPrimesMap = this.primesMap;

            foreach (Variable var in allPrimesMap.Keys)
            {
                IdentifierExpr iexpr = allPrimesMap[var] as IdentifierExpr;
                Debug.Assert(iexpr != null);
                reverseMap.Add(iexpr.Decl, new IdentifierExpr(Token.NoToken, var));
            }
            return Logic.Substitute(reverseMap, expr);
        }

        public Expr MakePrime(Expr expr, VariableSeq dontTouch)
        {
            return Logic.Substitute(primesMap, expr, dontTouch);
        }

        public Expr Invariant
        {
            get
            {
                Expr inv = Expr.True;
                foreach (QInvariant qinv in this.invStore.GetInvariants())
                {
                    if (qinv.Introduced)
                    {
                        Debug.Assert(qinv.RTChecked);
                        inv = Expr.And(inv, qinv.Formula);
                    }
                }
                return inv;
            }
        }

        public Expr InvariantForProc(ProcedureState procState)
        {
            return Expr.And(this.Invariant, procState.LocalInvariant);
        }

        public Expr SplitInvariant
        {
            get
            {
                Expr inv = Expr.True;
                foreach (Expr expr in this.splitInvariants)
                {
                    inv = Expr.And(inv, expr);
                }
                return inv;
            }
        }

        public Expr Guar
        {
            get
            {
                Expr g = Expr.True;
                foreach (Expr f in guar)
                {
                    g = Expr.And(g, f);
                }
                return g;
            }
        }

        public Expr Rely
        {
            get
            {
                Expr r = Expr.True;
                foreach (Expr f in rely)
                {
                    r = Expr.And(r, f);
                }
                return r;
            }
        }

        public Expr RelyForGlobals
        {
            get
            {
                Expr rely = Expr.True;
                foreach (Variable gvar in globalVars.Values)
                {
                    IdentifierExpr iexpr = new IdentifierExpr(Token.NoToken, gvar);
                    Expr primeexp = this.GetPrimedExpr(gvar);
                    rely = Expr.And(rely, Expr.Eq(primeexp, iexpr));
                }
                return rely;
            }
        }

        public void AddGlobalVar(GlobalVariable var)
        {
            globalVars.Add(var.Name, var);
            IdentifierExpr primeExpr = Logic.MakePrimedExpr(var);

            primesMap[var] = primeExpr;

            primes.Add(primeExpr.Decl);
        }

        public GlobalVariable GetGlobalVar(string name)
        {
            if (!globalVars.ContainsKey(name)) return null;
            return (GlobalVariable)globalVars[name];
        }

        public void AddAuxVar(GlobalVariable var)
        {
            if(!program.TopLevelDeclarations.Contains(var))
            {
                program.TopLevelDeclarations.Add(var);
                // Prover.GetInstance().DeclareGlobalVar(var);
            }

            AddGlobalVar(var);
            MakeAuxVar(var);
        }

        public void MakeAuxVar(GlobalVariable var)
        {
            Debug.Assert(this.globalVars[var.Name] == var);
            auxVars.Add(var.Name, var);

            // add the QKeyValue
            Qoogie.AddQKeyValue(var, "isaux");
        }

        public void MakeNonAuxVar(GlobalVariable var)
        {
            Debug.Assert(this.auxVars[var.Name] == var);
            Debug.Assert(this.globalVars[var.Name] == var);
            auxVars.Remove(var.Name);

            // remove the QKeyValue
            Qoogie.RemoveQKeyValue(var, "isaux");
        }

        public void RemoveAuxVar(GlobalVariable var)
        {
            RemoveGlobalVar(var);
            auxVars.Remove(var.Name);
        }

        public bool IsHiddenVar(Variable var)
        {
            return hiddenVars.ContainsKey(var.Name);
        }

        public void HideVar(GlobalVariable var)
        {
            Debug.Assert(this.globalVars[var.Name] == var);
            hiddenVars.Add(var.Name, var);

            Qoogie.AddQKeyValue(var, "ishidden");
        }

        public void RemoveGlobalVar(GlobalVariable var)
        {
            Variable prime = GetPrimedVar(var);

            globalVars.Remove(var.Name);
            program.TopLevelDeclarations.Remove(var);

            primesMap.Remove(var);

            primes = Util.RemoveFromVarSeq(primes, prime);

            // TODO: remove also from the modifies list of the procedures
        }

        public bool IsAuxVar(Variable var)
        {
            return auxVars.Contains(var.Name);
        }

        public List<GlobalVariable> AuxVars
        {
            get
            {
                List<GlobalVariable> vars = new List<GlobalVariable>();
                foreach (GlobalVariable var in auxVars.Values)
                {
                    vars.Add(var);
                }
                return vars;
            }
        }

        public Set<Variable> ProgramVars
        {
            get
            {
                Set<Variable> vars = new Set<Variable>();
                foreach (Variable var in globalVars.Values)
                {
                    if (!IsAuxVar(var))
                    {
                        vars.Add(var);
                    }
                }
                return vars;
            }
        }

        public Set<Constant> Constants
        {
            get
            {
                Set<Constant> consts = new Set<Constant>();
                foreach (Declaration decl in program.TopLevelDeclarations)
                {
                    if (decl is Constant)
                    {
                        consts.Add(decl as Constant);
                    }
                }
                return consts;
            }
        }

        public Record GetRecord(string name)
        {
            if (program.Records.ContainsKey(name))
            {
                return program.Records[name];
            }
            return null;
        }

        public List<Record> Records
        {
            get
            {
                return new List<Record>(program.Records.Values);
            }
        }

        // this is for procedures with bodies
        public void CreateProcedureState(Implementation impl, bool isatomic, bool ispublic)
        {
            CreateProcedureState(impl, isatomic, false, ispublic);
        }
        public void CreateProcedureState(Implementation impl, bool isatomic, bool autolabel, bool ispublic)
        {
            ProcedureState procstate = new ProcedureState(impl, isatomic, autolabel, ispublic);

            Debug.Assert(!procedureStates.ContainsKey(impl.Name));
            procedureStates.Add(impl.Name, procstate);
            procstate.hasTransformed = true;
        }

        public void RemoveProcedureState(ProcedureState procState)
        {
            Debug.Assert(procedureStates.ContainsKey(procState.impl.Name));
            procedureStates.Remove(procState.impl.Name);

            // remove from the program
            program.TopLevelDeclarations.Remove(procState.impl.Proc);
            program.TopLevelDeclarations.Remove(procState.impl);

            //foreach(AtomicBlock atomicBlock in procState.atomicBlocks) {
            //    RemoveAtomicBlock(atomicBlock);
            //}
        }

        public bool HasProcedureState(string name)
        {
            return procedureStates.ContainsKey(name);
        }

        public ProcedureState GetProcedureState(string name)
        {
            if (!HasProcedureState(name)) return null;
            return (ProcedureState)procedureStates[name];
        }

        public ResolutionContext GetResolutionContext(bool twostate)
        {
            return GetResolutionContext(twostate, new Set<Variable>());
        }

        public ResolutionContext GetResolutionContext(bool twostate, Set<Variable> fv)
        {
            ResolutionContext rc = new ResolutionContext((IErrorSink)null);

            Debug.Assert(rc.StateMode == ResolutionContext.State.Single);
            if (twostate) rc.StateMode = ResolutionContext.State.Two;

            foreach (Declaration d in program.TopLevelDeclarations)
            {
                d.Register(rc);
            }

            // add primes as well
            foreach (Declaration d in primes)
            {
                d.Register(rc);
            }

            // register fv
            foreach (Variable var in fv)
            {
                var.Register(rc);
            }

            return rc;

        }

        public TypecheckingContext GetTypecheckingContext()
        {
            return GetTypecheckingContext(new Set<Variable>());
        }

        public TypecheckingContext GetTypecheckingContext(Set<Variable> fv)
        {
            TypecheckingContext tc = new TypecheckingContext((IErrorSink)null);
            
            foreach (Declaration d in program.TopLevelDeclarations)
            {
                d.Typecheck(tc);
            }

            foreach (Declaration d in globalVars.Values)
            {
                d.Typecheck(tc);
            }

            // type check primes as well
            foreach (Declaration d in primes)
            {
                d.Typecheck(tc);
            }

            // typecheck fv
            foreach (Variable var in fv)
            {
                var.Typecheck(tc);
            }

            return tc;
        }

        public bool ResolveTypeCheckExpr(Expr expr, bool twostate, Set<Variable> fv)
        {
            BoogiePL.Errors.count = 0;

            expr.Resolve(GetResolutionContext(twostate, fv));

            expr.Typecheck(GetTypecheckingContext());

            return BoogiePL.Errors.count == 0;
        }

        public bool ResolveTypeCheckExpr(Expr expr, bool twostate)
        {
            BoogiePL.Errors.count = 0;

            expr.Resolve(GetResolutionContext(twostate));

            expr.Typecheck(GetTypecheckingContext());

            return BoogiePL.Errors.count == 0;
        }

        public bool ResolveType(Microsoft.Boogie.Type type, out Microsoft.Boogie.Type result)
        {
            BoogiePL.Errors.count = 0;

            result = type.ResolveType(GetResolutionContext(false));

            return BoogiePL.Errors.count == 0;
        }


        public string TextView
        {
            get
            {
                StringWriter strw = new StringWriter();

                using (TokenTextWriter writer = new TokenTextWriter(strw))
                {
                    program.Emit(writer);
                }
                strw.Flush();

                return strw.ToString();
            }
        }

        public List<myGraph> GraphView
        {
            get
            {
                List<myGraph> glist = new List<myGraph>();
                foreach (ProcedureState procState in procedureStates.Values)
                {
                    myGraph procg = procState.GraphView;
                    glist.Add(procg);
                }
                return glist;
            }
        }


        public bool HasGlobalVar(string varname)
        {
            return globalVars.ContainsKey(varname);
        }

        public bool HasAuxVar(string varname)
        {
            return auxVars.ContainsKey(varname);
        }

        public APLBlock GetAPLBlockByLabel(string label)
        {
            int idx = label.LastIndexOf('@');
            if (idx < 0)
            {
                foreach (ProcedureState procState in ProcedureStates)
                {
                    procState.ComputeAtomicBlocks();
                    APLBlock atom = procState.aplBlockMap[label];

                    if (atom != null)
                    {
                        return atom;
                    }
                }

                Output.AddError("Invalid label: " + label);
                return null;
            }
            else
            {

                string atomname = label.Substring(0, idx);
                string procname = label.Substring(idx + 1);

                ProcedureState procState = GetProcedureState(procname);
                if (procState == null)
                {
                    Output.AddError("ProcedureState does not exist: " + procname);
                    return null;
                }

                procState.ComputeAtomicBlocks();
                APLBlock atom = procState.aplBlockMap[atomname];

                if (atom == null)
                {
                    Output.AddError("APLBlock does not exist: " + atomname);
                    return null;
                }

                return atom;
            }
        }

        public AtomicBlock GetAtomicBlockByLabel(string label)
        {
            int idx = label.LastIndexOf('@');
            if (idx < 0)
            {
                foreach (ProcedureState procState in ProcedureStates)
                {
                    procState.ComputeAtomicBlocks();
                    AtomicBlock atom = procState.GetAtomicBlock(label);

                    if (atom != null)
                    {
                        return atom;
                    }
                }

                Output.AddError("Invalid label: " + label);
                return null;
            }
            else
            {

                string atomname = label.Substring(0, idx);
                string procname = label.Substring(idx + 1);

                ProcedureState procState = GetProcedureState(procname);
                if (procState == null)
                {
                    Output.AddError("ProcedureState does not exist: " + procname);
                    return null;
                }

                procState.ComputeAtomicBlocks();
                AtomicBlock atom = procState.GetAtomicBlock(atomname);

                if (atom == null)
                {
                    Output.AddError("Atomic block does not exist: " + atomname);
                    return null;
                }

                return atom;
            }
        }


        internal void AddCheckedInvariant(QInvariant invariant)
        {
            invStore.Add(invariant);
            Debug.Assert(invariant.Introduced == false && invariant.RTChecked == true);
            invariant.Introduced = true;

            // ensure that expr is not currently in the program
            program.TopLevelDeclarations.Add(new Invariant(Token.NoToken, invariant.Formula));
        }

        internal void QuantifyInvariant(GlobalVariable var)
        {
            foreach (QInvariant qinv in this.invStore.GetInvariants())
            {
                if (qinv.Introduced)
                {
                    Debug.Assert(qinv.RTChecked);
                    qinv.Formula = new ExistsExpr(Token.NoToken, new VariableSeq(var), qinv.Formula);
                }
            }
        }

		/// <summary>
		/// Returns the hidden variables of this program
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


        public string GetCodeTextByLabel(string blocklabel)
        {
            AtomicBlock atomicBlock = GetAtomicBlockByLabel(blocklabel);

            if (atomicBlock == null)
            {
                Output.AddError("No such atomic block: " + blocklabel);
                return null;
            }

            return atomicBlock.StmtStr;
        }
    } // end class


} // end namespace QED