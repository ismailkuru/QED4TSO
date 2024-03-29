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
using Microsoft.Boogie.AbstractInterpretation;
using AI = Microsoft.AbstractInterpretationFramework;
using Microsoft.Contracts;
using Type = Microsoft.Boogie.Type;
using PureCollections;


    public class MyReadSubstituter : StmtDuplicator
    {
        protected Substitution subst;
        protected Hashtable map;
        protected bool found = false;
        protected bool stopAtWrite = true;

        public MyReadSubstituter(Hashtable m, bool saw)
        {
            this.map = m;
            this.subst = Substituter.SubstitutionFromHashtable(this.map);
            this.stopAtWrite = saw;
        }

        // does substitution in place
        public virtual void VisitAtomicBlock(AtomicBlock atomicBlock)
        {
            Debug.Assert(map.Count == 1); // TODO: can only handle 1 variable for now !

            Queue<Block> q = new Queue<Block>();
            q.Enqueue(atomicBlock.startBlock);

            while (q.Count > 0)
            {
                Block b = q.Dequeue();

                found = false;
                b.Cmds = VisitCmdSeq(b.Cmds);

                if (!found)
                {
                    // deal with goto
                    GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
                    if (gotoCmd != null)
                    {
                        foreach (Block succ in gotoCmd.labelTargets)
                        {
                            if (atomicBlock.Contains(succ))
                            {
                                q.Enqueue(succ);
                            }
                        }
                    }
                }
            }
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            Expr e;

            if (found)
            {
                e = base.VisitIdentifierExpr(node);
            }
            else
            {
                e = new MySubstituter(subst).VisitIdentifierExpr(node);
            }
            return e;
        }

        public override Cmd VisitAssignCmd(AssignCmd node)
        {

            for (int i = 0; i < node.Rhss.Count; ++i)
            {
                node.Rhss[i] = (Expr)this.Visit(node.Rhss[i]);
            }

            if (stopAtWrite)
            {
                for (int i = 0; i < node.Lhss.Count && !found; ++i)
                {
                    if (map.ContainsKey(node.Lhss[i].DeepAssignedVariable))
                    {
                        found = true;
                        break;
                    }
                }
            }

            for (int i = 0; i < node.Lhss.Count; ++i)
            {
                if (!found)
                {
                    if (node.Lhss[i] is FieldAssignLhs)
                    {
                        FieldAssignLhs fieldAssignLhs = node.Lhss[i] as FieldAssignLhs;
                        Variable fieldMap = fieldAssignLhs.DeepAssignedVariable;
                        Debug.Assert(fieldMap != null);
                        if (map.ContainsKey(fieldMap))
                        {
                            IdentifierExpr newMap = subst(fieldMap) as IdentifierExpr;
                            Debug.Assert(newMap != null);
                            AssignLhs assignLhs = new SimpleAssignLhs(Token.NoToken, newMap);
                            List<Expr> indexes = new List<Expr>();
                            indexes.Add(fieldAssignLhs.obj);
                            node.Lhss[i] = new MapAssignLhs(Token.NoToken, assignLhs, indexes);
                        }
                    }
                }

                node.Lhss[i] = (AssignLhs)this.Visit(node.Lhss[i]);
            }
            return node;
        }

        public override Cmd VisitHavocCmd(HavocCmd node)
        {
            if (stopAtWrite)
            {
                for (int i = 0; i < node.Vars.Length && !found; ++i)
                {
                    if (map.ContainsKey(node.Vars[i].Decl))
                    {
                        found = true;
                        break;
                    }
                }
            }

            node.Vars = this.VisitIdentifierExprSeq(node.Vars);
            return node;
        }

        public override Cmd VisitCallCmd(CallCmd node)
        {
            for (int i = 0; i < node.Ins.Count; ++i)
                if (node.Ins[i] != null)
                    node.Ins[i] = this.VisitExpr(node.Ins[i]);

            if (stopAtWrite)
            {
                for (int i = 0; i < node.Outs.Count && !found; ++i)
                {
                    if (map.ContainsKey(node.Outs[i].Decl))
                    {
                        found = true;
                        break;
                    }
                }

                for (int i = 0; i < node.Proc.Modifies.Length && !found; ++i)
                {
                    if (map.ContainsKey(node.Proc.Modifies[i].Decl))
                    {
                        found = true;
                        break;
                    }
                }
            }

            for (int i = 0; i < node.Outs.Count; ++i)
            {
                if (node.Outs[i] != null)
                {
                    node.Outs[i] = (IdentifierExpr)this.VisitIdentifierExpr(node.Outs[i]);
                }
            }
            node.Proc = this.VisitProcedure(node.Proc);
            return node;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (!found)
            {
                if (node.Fun is FieldSelect || node.Fun is FieldStore)
                {
                    Debug.Assert(node.Args[0] != node.Args[1]);
                    IdentifierExpr fieldMap = node.Args[0] as IdentifierExpr;
                    Debug.Assert(fieldMap != null);
                    if (map.ContainsKey(fieldMap.Decl))
                    {
                        IdentifierExpr newMap = subst(fieldMap.Decl) as IdentifierExpr;
                        Debug.Assert(newMap != null);
                        if (node.Fun is FieldSelect)
                        {
                            node.Fun = new MapSelect(Token.NoToken, 1);
                        }
                        else
                        {
                            node.Fun = new MapStore(Token.NoToken, 1);
                        }
                        node.Args[0] = newMap;
                    }
                }
            }

            return base.VisitNAryExpr(node);
        }

    } // end MyReadSubstituter

// TODO/BUG: Create new object for all the expressions visited
// Look at VisitQuantifierExpr


    public class MySubstituter : StmtDuplicator
    {
        protected Substitution subst;
        protected bool insideOldExpr = false;
        protected Substitution substold;
        protected VariableSeq dontTouch = null;

        public MySubstituter(Substitution subst)
            : this(subst, null, null)
        {
        }

        public MySubstituter(Substitution subst, VariableSeq donttouch)
            : this(subst, null, donttouch)
        {
        }

        public MySubstituter(Substitution subst, Substitution substold)
            : this(subst, substold, null)
        {
        }

        public MySubstituter(Substitution subst, Substitution substold, VariableSeq donttouch)
            : base()
        {
            this.subst = subst;
            this.substold = substold;
            this.insideOldExpr = false;
            this.dontTouch = donttouch;
        }

        private Expr Substitute(IdentifierExpr node, Substitution s)
        {
            Expr/*?*/ e = null;
            if (!boundedVars.Contains(node.Decl.Name) && (dontTouch == null || !dontTouch.Has(node.Decl)))
            {
                e = s(node.Decl);
            }
            return e == null ? base.VisitIdentifierExpr(node) : e;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (substold != null)
            {
                if (insideOldExpr)
                {
                    return Substitute(node, substold);
                }
                else
                {
                    return Substitute(node, subst);
                }
            }
            else
            {
                return Substitute(node, subst);
            }
        }

        public override Expr VisitOldExpr(OldExpr node)
        {
            if (substold != null)
            {
                bool previouslyInOld = insideOldExpr;
                insideOldExpr = true;
                Expr e = (Expr)this.Visit(node.Expr);
                insideOldExpr = previouslyInOld;
                return e;
            }
            else
            {
                return base.VisitOldExpr(node);
            }
        }
    }

/******************************************************************/
/******************************************************************/

public class MyHider : StmtDuplicator
{
    Hashtable map;

	public MyHider()
        : base()
    {
        map = new Hashtable();
	}

	public override Expr VisitIdentifierExpr(IdentifierExpr node)
	{
		Variable var = node.Decl;
		if(!boundedVars.Contains(var.Name)) {
			if(var is Constant) {
				if(var.Name == "tid") {
					return ProofState.GetInstance().tidxExpr;
				} else {
					return base.VisitIdentifierExpr(node);
				}
			} else
			if(!ProofState.GetInstance().primesMap.ContainsKey(var) && !ProofState.GetInstance().primes.Has(var)) {
                Debug.Assert(!(var is GlobalVariable));
                Debug.Assert(!var.Name.EndsWith("_hidden"), "Variable already hidden, expected only one hide!");
				return DoHide(var);
			} else {
				return base.VisitIdentifierExpr(node);
			}
		} else {
			return base.VisitIdentifierExpr(node);
		}		
	}

    private Expr DoHide(Variable var)
    {
        if (map.Contains(var))
        {
            return map[var] as Expr;
        }
        else
        {
            IdentifierExpr hexpr = Logic.MakeHiddenExpr(var);
            map.Add(var, hexpr);
            return hexpr;
        }
    }
}

/******************************************************************/
/******************************************************************/

public class MyOldMaker : StmtDuplicator
{
    public MyOldMaker()
        : base()
    {
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
        Variable var = node.Decl;
        if (!boundedVars.Contains(var.Name))
        {
            return Logic.MakeOld(var);
        }
        else
        {
            return base.VisitIdentifierExpr(node);
        }
    }

    public override Expr VisitOldExpr(OldExpr node)
    {
        Debug.Assert(false, "The given expression should not contain old expressions !");
        return base.VisitOldExpr(node);
    }

}

/******************************************************************/
/******************************************************************/


public class MyQuantExprVisitor : MySubstituter
{
	// public Dictionary<Type,Set<Variable>> typeToBoundedVars = new Dictionary<Type,Set<Variable>>();
    public Set<Variable> allBoundedVars;
    public Hashtable substMap;

    public enum Kind { Eliminate, Collect, Substitute }
    public Kind kind;
    public string quantClassName;

    private MyQuantExprVisitor(string cname)
        : base(Substituter.SubstitutionFromHashtable(new Hashtable()))
    {
        this.quantClassName = cname;
	}
	
    static public MyQuantExprVisitor ExistsVisitor()
    {
        return new MyQuantExprVisitor("ExistsExpr");
    }

    static public MyQuantExprVisitor ForallVisitor()
    {
        return new MyQuantExprVisitor("ForallExpr");
    }
    //public Expr DoEliminate(Expr expr, ProofState proofState, ProcedureState procState) {
		
    //    Expr exprWoutExists = (Expr) this.Visit(expr);
		
    //    Set guessVars = new Set();
    //    exprWoutExists.ComputeFreeVariables(guessVars);
		
    //    foreach(Variable var in proofState.globalVars.Values) {
    //        guessVars.Add(var);
    //    }
    //    foreach(Variable var in procState.localVars.Values) {
    //        guessVars.Add(var);
    //    }
    //    foreach(Variable var in proofState.primes) {
    //        guessVars.Add(var);
    //    }
    //    foreach(Variable var in procState.primes) {
    //        guessVars.Add(var);
    //    }
		
    //    foreach(Variable bvar in allBoundedVars) {
    //        IdentifierExpr bexpr = new IdentifierExpr(Token.NoToken, bvar);
    //        Expr guessExpr = Expr.False;
			
    //        foreach(Variable gvar in guessVars) {
    //            if(! bvar.Equals(gvar)) {
    //                IdentifierExpr gexpr = new IdentifierExpr(Token.NoToken, gvar);
    //                guessExpr = Expr.Or(guessExpr, Logic.EquivExpr(bvar.TypedIdent.Type, bexpr, gexpr));
    //            }
    //        }
    //        if(guessExpr != Expr.False) {
    //            exprWoutExists = Expr.And(exprWoutExists, guessExpr);
    //        }
    //    }
		
    //    return exprWoutExists;
    //}

    public override Absy Visit(Absy node)
    {
        string typeName = node.GetType().ToString();
        string className = typeName.Substring(typeName.LastIndexOf(".") + 1);
        if (className == this.quantClassName)
        {
            QuantifierExpr qexpr = node as QuantifierExpr;
            
            if (kind == Kind.Eliminate)
            {
                return qexpr.Body;
            }
            else if (kind == Kind.Collect)
            {
                foreach (Variable var in qexpr.Dummies)
                {
                    allBoundedVars.Add(var);
                }
            }
            else if (kind == Kind.Substitute)
            {
                VariableSeq newDummies = new VariableSeq();
                foreach (Variable var in qexpr.Dummies)
                {
                    if (!substMap.ContainsKey(var))
                    {
                        newDummies.Add(var);
                    }
                }
                qexpr.Dummies = newDummies;
            }

            //QuantifierExpr qnode = node as QuantifierExpr;
            //foreach (Variable var in qnode.Dummies)
            //{
            //    Type type = var.TypedIdent.Type;
            //    if (!typeToBoundedVars.ContainsKey(type))
            //    {
            //        typeToBoundedVars[type] = new Set<Variable>();
            //    }
            //    Debug.Assert(!allBoundedVars.Contains(var));
            //    typeToBoundedVars[type].Add(var);
            //    allBoundedVars.Add(var);
            //}
            //return Visit(qnode.Body);
        }

        return base.Visit(node);
    }


    internal Expr Eliminate(Expr expr)
    {
        this.kind = Kind.Eliminate;

        return Visit(expr) as Expr;
    }

    internal Set<Variable> Collect(Expr expr)
    {
        this.allBoundedVars = new Set<Variable>();

        this.kind = Kind.Collect;

        Visit(expr);

        return allBoundedVars;
    }

    internal Expr Substitute(Expr expr, Hashtable map)
    {
        this.kind = Kind.Substitute;

        this.substMap = map;
        this.subst = Substituter.SubstitutionFromHashtable(this.substMap);

        return Visit(expr) as Expr;
    }
}

/******************************************************************/
/******************************************************************/

public class MySkolemizer : StmtDuplicator
{
	Hashtable map = new Hashtable();
	Set freeVars = new Set();
	int nextFuncId = 0;
	
	public MySkolemizer()
        : base()
    {	
	}
	
	private Expr SkolemFunction(Variable var) {
		++nextFuncId;
		ExprSeq args = new ExprSeq();
		foreach(Variable arg in freeVars) {
			args.Add(new IdentifierExpr(Token.NoToken, arg));
		}
		return new NAryExpr(Token.NoToken, new FunctionCall(new IdentifierExpr(Token.NoToken, "skolem" + var.Name, var.TypedIdent.Type)), args); 
	}
	
	public Expr DoSkolemize(Expr expr) {
		expr.ComputeFreeVariables(freeVars);
		
		return (Expr) Visit(expr);
	}

	public override Absy Visit(Absy node)
	{
		Set oldFreeVars = (Set) freeVars.Clone();
		
		Expr expr;
		
		if(node is ExistsExpr) {
		  ExistsExpr qnode = node as ExistsExpr;
		  foreach(Variable var in qnode.Dummies) {
			Debug.Assert(!map.Contains(var));
			map.Add(var, SkolemFunction(var));
		  }
		  expr = (Expr) this.Visit(Logic.Substitute(map, qnode.Body));
		} else
		if(node is ForallExpr) { 
			ForallExpr fnode = node as ForallExpr;
			foreach(Variable fvar in fnode.Dummies) {
				freeVars.Add(fvar);
			}
			expr = (Expr) this.Visit(fnode.Body);
		} else
		{		
			expr = (Expr) base.Visit(node);
		}
		
		freeVars = oldFreeVars;
		
		return expr;
	}

}

/******************************************************************/
/******************************************************************/

public class MyExprTranslator : StmtDuplicator
{
	ProofState proofState;
	ProcedureState procState;
	
	public MyExprTranslator()
        : base()
    {
	}
	
	public Expr DoTranslate(ProofState pstate, ProcedureState procstate, Expr expr) {
		this.proofState = pstate;
		this.procState = procstate;
		return (Expr) Visit(expr);
	}

	public override Absy Visit(Absy node)
	{
		NAryExpr nary = node as NAryExpr;
		if(nary != null) {
			FunctionCall fcall = nary.Fun as FunctionCall;
			if(fcall != null) {
                AtomicBlock atomicBlock = proofState.GetAtomicBlockByLabel(fcall.FunctionName);
                if(atomicBlock != null) {
					Expr trp = atomicBlock.TransitionPredicate;
					return base.Visit(trp);
				} else if(fcall.FunctionName == "Inv") {
					Expr inv = proofState.Invariant;
					if(procState != null) {
						inv = Expr.And(inv, procState.LocalInvariant);
					}
					return base.Visit(inv);
				} else if(fcall.FunctionName == "InvPrime") {
					Expr invprime = proofState.MakePrime(proofState.Invariant);
					if(procState != null) {
						invprime = Expr.And(invprime, procState.MakePrime(procState.LocalInvariant));
					}
					return base.Visit(invprime);
				}
			}
		}
		
		return base.Visit(node);
	}
	
	public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      if(node.Decl == null) {
		return node; 
	  } else {
		return base.VisitIdentifierExpr(node);
	  }
    }

}

/******************************************************************/
/******************************************************************/

public class MyMapSearcher : StmtVisitor
{
	Variable map = null;

	public MyMapSearcher()
        : base()
    {	
		
	}
	
	public Variable DoSearch(Expr expr) {
		Visit(expr);
		return map;
	}

	public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
      Debug.Assert(node.Decl != null);
      if(map == null && node.Decl.TypedIdent.Type is MapType) {
		this.map = node.Decl;
      }
      return node;
    }

}
  
/******************************************************************/
/******************************************************************/

public class MyMapIndiceFinder : StmtVisitor
{
	Variable map;
	Set<Expr> indices;

	public MyMapIndiceFinder(Variable m)
        : base()
    {	
		this.map = m;
		this.indices = new Set<Expr>();
	}
	
	public Set<Expr> DoFindIndices(Absy node) {
		Visit(node);
		return indices;
	}
	
	private void AddIndex(Expr expr) {
		IdentifierExpr iexpr = expr as IdentifierExpr;
		if(iexpr != null && boundedVars.Contains(iexpr.Decl.Name)) {
			return;
		}
		
		string exprStr = Output.ToString(expr);
		bool found = false;
		foreach(Expr e in indices) {
			if(exprStr == Output.ToString(e)) {
				found = true;
				break;
			}
		}
		if(!found) {
			indices.Add(expr);
		}
	}

    public override Expr VisitNAryExpr(NAryExpr node)
    {
        if (node.Fun is MapSelect || node.Fun is MapStore)
        {
            if (node.Args[0] is IdentifierExpr)
            {
                IdentifierExpr mapExpr = node.Args[0] as IdentifierExpr;
                if (mapExpr.Decl.Equals(this.map))
                {
                    AddIndex(node.Args[1]);
                    if (node.Args[2] != null) AddIndex(node.Args[2]);
                }
            }

        }

        return base.VisitNAryExpr(node);
    }

}

/******************************************************************/
/******************************************************************/

public class MySearchForLocalVars : StandardVisitor
{
    Set<Variable> vars = new Set<Variable>();
    Hashtable boundedVars = new Hashtable();

    public MySearchForLocalVars()
        : base()
    {
    }

    public Set<Variable> DoSearch(Cmd cmd)
    {
        Visit(cmd);
        return this.vars;
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node)
    {
        Debug.Assert(node.Decl != null);
        Variable var = node.Decl;
        if (!boundedVars.ContainsKey(var) && !(var is GlobalVariable))
        {
            vars.Add(var);
        }
        return node;
    }

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
        foreach (Variable bvar in node.Dummies)
        {
            if (!boundedVars.Contains(bvar.Name))
            {
                boundedVars.Add(bvar.Name, 1);
            }
            else
            {
                int i = (int)boundedVars[bvar.Name];
                boundedVars[bvar.Name] = i + 1;
            }
        }

        this.VisitExpr(node.Body);

        foreach (Variable bvar in node.Dummies)
        {
            Debug.Assert(boundedVars.Contains(bvar.Name));
            int i = (int)boundedVars[bvar.Name];
            i = i - 1;
            if (i == 0)
            {
                boundedVars.Remove(bvar.Name);
            }
            else
            {
                boundedVars[bvar.Name] = i;
            }
        }

        return node;
    }

}

/******************************************************************/
/******************************************************************/

public class BigBlocksCollector : StmtVisitor
{
    Set<BigBlock> bigBlocks = new Set<BigBlock>();
    
    public BigBlocksCollector()
        : base()
    {
    }

    public Set<BigBlock> Collect(StmtList stmt)
    {
        VisitStmtList(stmt);
        return bigBlocks;
    }

    public override BigBlock VisitBigBlock(BigBlock bb)
    {
        bigBlocks.Add(bb);
        return base.VisitBigBlock(bb);
    }
}

/******************************************************************/
/******************************************************************/

public class FieldAccessCollector : StmtVisitor
{
    Set<FieldAccess> accesses = new Set<FieldAccess>();

    public FieldAccessCollector()
        : base()
    {
    }

    public Set<FieldAccess> Collect(Cmd cmd)
    {
        Visit(cmd);
        return accesses;
    }

    public override FieldAssignLhs VisitFieldAssignLhs(FieldAssignLhs node)
    {
        accesses.Add(new FieldAccess(node.record, node.obj, node.fieldName, false));

        return base.VisitFieldAssignLhs(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node)
    {
        if (node.Fun is FieldSelect)
        {
            FieldSelect sel = node.Fun as FieldSelect;
            accesses.Add(new FieldAccess(null, node.Args[1], sel.fieldName, true));
        }
        else if(node.Fun is FieldStore)
        {
            FieldStore str = node.Fun as FieldStore;
            accesses.Add(new FieldAccess(null, node.Args[1], str.fieldName, false));
        }

        return base.VisitNAryExpr(node);
    }
}

/******************************************************************/
/******************************************************************/

public class StmtListCollector : StmtVisitor
{
    List<StmtList> stmtLists = new List<StmtList>();

    public StmtListCollector()
        : base()
    {
    }

    public List<StmtList> Collect(StmtList stmt)
    {
        VisitStmtList(stmt);
        return stmtLists;
    }

    public override StmtList VisitStmtList(StmtList stmt)
    {
        stmtLists.Add(stmt);
        return base.VisitStmtList(stmt);
    }
}

/******************************************************************/
/******************************************************************/

public class AtomicStmtCollector : StmtVisitor
{
    List<AtomicStmt> atomicStmts = new List<AtomicStmt>();

    public AtomicStmtCollector()
        : base()
    {
    }

    public List<AtomicStmt> Collect(StmtList stmt)
    {
        VisitStmtList(stmt);
        return atomicStmts;
    }

    public List<AtomicStmt> Collect(BigBlock bb)
    {
        VisitBigBlock(bb);
        return atomicStmts;
    }

    public override AtomicStmt VisitAtomicStmt(AtomicStmt stmt)
    {
        atomicStmts.Add(stmt);
        return base.VisitAtomicStmt(stmt);
    }
}


/******************************************************************/
/******************************************************************/

public class NonGlobalVarsCollector : StmtVisitor
{
    Set<Variable> locals = new Set<Variable>();
    Set<Variable> formals = new Set<Variable>();

    public NonGlobalVarsCollector()
        : base()
    {
    }

    public Pair Collect(StmtList stmt)
    {
        VisitStmtList(stmt);
        return new Pair(locals, formals);
    }

    public override Variable VisitVariable(Variable var)
    {
        if (!(boundedVars.ContainsKey(var)))
        {
            if (var is LocalVariable)
            {
                locals.Add(var);
            }
            else if (var is Formal)
            {
                formals.Add(var);
            }
        }
        return base.VisitVariable(var);
    }
}

/******************************************************************/
/******************************************************************/

    // TODO: not implemented correctly, reimplement this
public class AssignedVarsInLoopCollector : StmtVisitor
{
    VariableSeq vars = new VariableSeq();
    
    public AssignedVarsInLoopCollector()
        : base()
    {
    }

    public VariableSeq Collect(StmtList stmt)
    {
        VisitStmtList(stmt);

        VariableSeq varSeq = new VariableSeq();
        foreach (Variable v in vars)
        {
            if (v != null)
            {
                varSeq.Add(v);
            }
        }

        return varSeq;
    }

    public override CmdSeq VisitCmdSeq(CmdSeq cmdSeq)
    {
        foreach (Cmd cmd in cmdSeq)
        {
            cmd.AddAssignedVariables(vars);
        }
        return base.VisitCmdSeq(cmdSeq);
    }
}

/******************************************************************/
/******************************************************************/

public class StmtVisitor : StandardVisitor
{
    protected Hashtable boundedVars = new Hashtable();

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
        foreach (Variable bvar in node.Dummies)
        {
            if (!boundedVars.Contains(bvar.Name))
            {
                boundedVars.Add(bvar.Name, 1);
            }
            else
            {
                int i = (int)boundedVars[bvar.Name];
                boundedVars[bvar.Name] = i + 1;
            }
        }

        //-----------------------------------
        if (node.Triggers != null)
        {
            node.Triggers = this.VisitTrigger(node.Triggers);
        }

        node.Body = this.VisitExpr(node.Body);

        node.Dummies = this.VisitVariableSeq(node.Dummies);
        //-----------------------------------
        
        foreach (Variable bvar in node.Dummies)
        {
            Debug.Assert(boundedVars.Contains(bvar.Name));
            int i = (int)boundedVars[bvar.Name];
            i = i - 1;
            if (i == 0)
            {
                boundedVars.Remove(bvar.Name);
            }
            else
            {
                boundedVars[bvar.Name] = i;
            }
        }

        return node;
    }

    public virtual StmtList VisitStmtList(StmtList list)
    {
        List<BigBlock> bbs = new List<BigBlock>(list.BigBlocks);
        bbs = VisitBigBlocks(bbs);

        list.BigBlocks.Clear();
        list.BigBlocks.AddRange(bbs);

        return list;
    }

    public virtual List<StmtList> VisitStmtLists(List<StmtList> list)
    {
        for (int i = 0; i < list.Count; ++i)
        {
            list[i] = VisitStmtList(list[i]);
        }

        return list;
    }

    public virtual List<BigBlock> VisitBigBlocks(List<BigBlock> bbs)
    {
        for (int i = 0; i < bbs.Count; ++i)
        {
            bbs[i] = VisitBigBlock(bbs[i]);
        }
        return bbs;
    }

    public virtual BigBlock VisitBigBlock(BigBlock bb)
    {
        bb.simpleCmds = VisitCmdSeq(bb.simpleCmds);
        if(bb.ec != null) bb.ec = VisitStructuredCmd(bb.ec);
        if(bb.tc != null) bb.tc = VisitTransferCmd(bb.tc);
        return bb;
    }

    public virtual StructuredCmd VisitStructuredCmd(StructuredCmd cmd)
    {
        if (cmd is IfCmd)
        {
            return VisitIfCmd(cmd as IfCmd);
        }
        else if (cmd is WhileCmd)
        {
            return VisitWhileCmd(cmd as WhileCmd);
        }
        else if (cmd is BreakCmd)
        {
            return VisitBreakCmd(cmd as BreakCmd);
        }
        else if (cmd is ContinueCmd)
        {
            return VisitContinueCmd(cmd as ContinueCmd);
        }
        else if (cmd is APLStmt)
        {
            return VisitAPLStmt(cmd as APLStmt);
        }
        
        
        Debug.Assert(false, "Unknown structured Cmd!");
        return null;
    }

    public virtual StructuredCmd VisitAPLStmt(APLStmt stmt)
    {
        if (stmt is AtomicStmt)
        {
            return VisitAtomicStmt(stmt as AtomicStmt);
        }
        else if (stmt is CallStmt)
        {
            return VisitCallStmt(stmt as CallStmt);
        }
        else if (stmt is ParallelStmt)
        {
            return VisitParallelStmt(stmt as ParallelStmt);
        }
        else if (stmt is ForkStmt)
        {
            return VisitForkStmt(stmt as ForkStmt);
        }
        else if (stmt is JoinStmt)
        {
            return VisitJoinStmt(stmt as JoinStmt);
        }
        else if (stmt is TryCatchStmt)
        {
            return VisitTryCatchStmt(stmt as TryCatchStmt);
        }
        //else if (stmt is ThrowStmt)
        //{
        //    return VisitThrowStmt(stmt as ThrowStmt);
        //}

        Debug.Assert(false, "Unknown structured Cmd!");
        return null;
    }

    public virtual ParallelStmt VisitParallelStmt(ParallelStmt parStmt)
    {
        for (int i = 0; i < parStmt.bodies.Count; ++i)
        {
            parStmt.bodies[i] = VisitStmtList(parStmt.bodies[i]);
        }

        return parStmt;
    }

    public virtual ForkStmt VisitForkStmt(ForkStmt forkStmt)
    {
        forkStmt.callCmd = VisitAsyncCallCmd(forkStmt.callCmd);
        
        return forkStmt;
    }

    public virtual JoinStmt VisitJoinStmt(JoinStmt joinStmt)
    {
        joinStmt.joinCmd = VisitJoinCmd(joinStmt.joinCmd);

        return joinStmt;
    }

    public virtual TryCatchStmt VisitTryCatchStmt(TryCatchStmt trycatch)
    {
        trycatch.body = VisitStmtList(trycatch.body);

        for (int i = 0; i < trycatch.catchList.Count; ++i)
        {
            trycatch.catchList[i] = VisitCatchStmt(trycatch.catchList[i]);
        }

        return trycatch;
    }

    public virtual CatchStmt VisitCatchStmt(CatchStmt catchStmt)
    {
        catchStmt.body = VisitStmtList(catchStmt.body);

        return catchStmt;
    }

    //public virtual ThrowStmt VisitThrowStmt(ThrowStmt thrw)
    //{
    //    thrw.throwCmd = VisitThrowCmd(thrw.throwCmd);
    //    return thrw;
    //}

    public virtual CallStmt VisitCallStmt(CallStmt callStmt)
    {
        callStmt.bodies = VisitStmtLists(callStmt.bodies);
        return callStmt;
    }

    public virtual AtomicStmt VisitAtomicStmt(AtomicStmt atomicStmt)
    {
        atomicStmt.bodies = VisitStmtLists(atomicStmt.bodies);
        if (atomicStmt.trapPredicate != null) atomicStmt.trapPredicate = VisitExpr(atomicStmt.trapPredicate);
        // TODO: visit transitions
        return atomicStmt;
    }

    public virtual BreakCmd VisitBreakCmd(BreakCmd breakCmd)
    {
        return breakCmd;
    }

    public virtual ContinueCmd VisitContinueCmd(ContinueCmd continueCmd)
    {
        return continueCmd;
    }

    public virtual WhileCmd VisitWhileCmd(WhileCmd whileCmd)
    {
        if(whileCmd.Guard != null) whileCmd.Guard = VisitExpr(whileCmd.Guard);
        whileCmd.Body = VisitStmtList(whileCmd.Body);
        return whileCmd;
    }

    public virtual IfCmd VisitIfCmd(IfCmd ifCmd)
    {
        if (ifCmd.Guard != null) ifCmd.Guard = VisitExpr(ifCmd.Guard);
        ifCmd.thn = VisitStmtList(ifCmd.thn);
        if (ifCmd.elseBlock != null) ifCmd.elseBlock = VisitStmtList(ifCmd.elseBlock);
        if (ifCmd.elseIf != null) ifCmd.elseIf = VisitIfCmd(ifCmd.elseIf);
        return ifCmd;
    }
}

/******************************************************************/
/******************************************************************/

public class StmtDuplicator : Duplicator
{
    protected Hashtable boundedVars = new Hashtable();

    public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
    {
        return MyVisitQuantifierExpr((QuantifierExpr)node.Clone());
    }

    public QuantifierExpr MyVisitQuantifierExpr(QuantifierExpr node)
    {
        foreach (Variable bvar in node.Dummies)
        {
            if (!boundedVars.Contains(bvar.Name))
            {
                boundedVars.Add(bvar.Name, 1);
            }
            else
            {
                int i = (int)boundedVars[bvar.Name];
                boundedVars[bvar.Name] = i + 1;
            }
        }

        //-----------------------------------
        if (node.Triggers != null)
        {
            node.Triggers = this.VisitTrigger(node.Triggers);
        }

        node.Body = this.VisitExpr(node.Body);

        node.Dummies = this.VisitVariableSeq(node.Dummies);
        //-----------------------------------

        foreach (Variable bvar in node.Dummies)
        {
            Debug.Assert(boundedVars.Contains(bvar.Name));
            int i = (int)boundedVars[bvar.Name];
            i = i - 1;
            if (i == 0)
            {
                boundedVars.Remove(bvar.Name);
            }
            else
            {
                boundedVars[bvar.Name] = i;
            }
        }

        return node;
    }

    public virtual StmtList VisitStmtList(StmtList list)
    {
        StmtList stmtList = new StmtList(VisitBigBlocks(new List<BigBlock>(list.BigBlocks)), list.EndCurly);
        //stmtList.ParentBigBlock = list.ParentBigBlock;
        //stmtList.ParentContext = list.ParentContext;
        return stmtList;
    }

    public virtual List<StmtList> VisitStmtLists(List<StmtList> list)
    {
        List<StmtList> newList = new List<StmtList>(list);

        for (int i = 0; i < newList.Count; ++i)
        {
            newList[i] = VisitStmtList(newList[i]);
        }
        
        return newList;
    }

    public virtual List<BigBlock> VisitBigBlocks(List<BigBlock> bbs)
    {
        for (int i = 0; i < bbs.Count; ++i)
        {
            bbs[i] = VisitBigBlock(bbs[i]);
        }
        return bbs;
    }

    public virtual BigBlock VisitBigBlock(BigBlock bb)
    {
        return new BigBlock(bb.tok, (bb.Anonymous ? null : bb.LabelName), VisitCmdSeq(new CmdSeq(bb.simpleCmds)), (bb.ec == null ? null : VisitStructuredCmd(bb.ec)), (bb.tc == null ? null : VisitTransferCmd(bb.tc)));
    }

    public virtual StructuredCmd VisitStructuredCmd(StructuredCmd cmd)
    {
        if (cmd is IfCmd)
        {
            return VisitIfCmd(cmd as IfCmd);
        }
        else if (cmd is WhileCmd)
        {
            return VisitWhileCmd(cmd as WhileCmd);
        }
        else if (cmd is BreakCmd)
        {
            return VisitBreakCmd(cmd as BreakCmd);
        }
        else if (cmd is ContinueCmd)
        {
            return VisitContinueCmd(cmd as ContinueCmd);
        }
        else if (cmd is APLStmt)
        {
            return VisitAPLStmt(cmd as APLStmt);
        }
        
        Debug.Assert(false, "Unknown structured Cmd!");
        return null;
    }

    public virtual ParallelStmt VisitParallelStmt(ParallelStmt parStmt)
    {
        return new ParallelStmt(parStmt.tok, parStmt.label, VisitStmtLists(parStmt.bodies));
    }

    public virtual ForkStmt VisitForkStmt(ForkStmt forkStmt)
    {
        return new ForkStmt(forkStmt.tok, forkStmt.label, VisitAsyncCallCmd(forkStmt.callCmd));
    }

    public virtual JoinStmt VisitJoinStmt(JoinStmt joinStmt)
    {
        return new JoinStmt(joinStmt.tok, joinStmt.label, VisitJoinCmd(joinStmt.joinCmd));
    }

    //public virtual ThrowStmt VisitThrowStmt(ThrowStmt thrw)
    //{
    //    return new ThrowStmt(thrw.tok, thrw.label, VisitThrowCmd(thrw.throwCmd));
    //}

    public virtual StructuredCmd VisitAPLStmt(APLStmt stmt)
    {
        if (stmt is AtomicStmt)
        {
            return VisitAtomicStmt(stmt as AtomicStmt);
        }
        else if (stmt is CallStmt)
        {
            return VisitCallStmt(stmt as CallStmt);
        }
        else if (stmt is ParallelStmt)
        {
            return VisitParallelStmt(stmt as ParallelStmt);
        }
        else if (stmt is ForkStmt)
        {
            return VisitForkStmt(stmt as ForkStmt);
        }
        else if (stmt is JoinStmt)
        {
            return VisitJoinStmt(stmt as JoinStmt);
        }
        else if (stmt is TryCatchStmt)
        {
            return VisitTryCatchStmt(stmt as TryCatchStmt);
        }
        //else if (stmt is ThrowStmt)
        //{
        //    return VisitThrowStmt(stmt as ThrowStmt);
        //}

        Debug.Assert(false, "Unknown structured Cmd!");
        return null;
    }

    public virtual TryCatchStmt VisitTryCatchStmt(TryCatchStmt trycatch)
    {
        List<CatchStmt> catchList = new List<CatchStmt>(trycatch.catchList);
        for(int i = 0; i < catchList.Count; ++i)
        {
            catchList[i] = VisitCatchStmt(catchList[i]);
        }

        return new TryCatchStmt(trycatch.tok, trycatch.label, VisitStmtList(trycatch.body), catchList);
    }

    public virtual CatchStmt VisitCatchStmt(CatchStmt catchStmt)
    {
        return new CatchStmt(catchStmt.tok, catchStmt.labels, VisitStmtList(catchStmt.body));
    }

    public virtual CallStmt VisitCallStmt(CallStmt callStmt)
    {
        return new CallStmt(new Token(callStmt.tok.line, callStmt.tok.col), callStmt.label, VisitStmtList(callStmt.body), VisitCallCmd(callStmt.cmd) as CallCmd);
    }

    public virtual AtomicStmt VisitAtomicStmt(AtomicStmt atomicStmt)
    {
        AtomicStmt dup = new AtomicStmt(atomicStmt.tok, atomicStmt.label, VisitStmtList(atomicStmt.body));
        dup.mover = atomicStmt.mover;
        if (dup.trapPredicate != null)
        {
            dup.trapPredicate = VisitExpr(atomicStmt.trapPredicate);
        }
        else
        {
            dup.trapPredicate = null;
        }
        return dup;
    }

    public virtual BreakCmd VisitBreakCmd(BreakCmd breakCmd)
    {
        return new BreakCmd(new Token(breakCmd.tok.line, breakCmd.tok.col), breakCmd.Label);
    }

    public virtual ContinueCmd VisitContinueCmd(ContinueCmd continueCmd)
    {
        return new ContinueCmd(new Token(continueCmd.tok.line, continueCmd.tok.col), continueCmd.Label);
    }

    public virtual WhileCmd VisitWhileCmd(WhileCmd whileCmd)
    {
        List<PredicateCmd> cmds = new List<PredicateCmd>();
        for (int i = 0; i < whileCmd.Invariants.Count; ++i)
        {
            cmds[i] = Visit(whileCmd.Invariants[i]) as PredicateCmd;
        }

        return new WhileCmd(new Token(whileCmd.tok.line, whileCmd.tok.col), (whileCmd.Guard == null ? null : VisitExpr(whileCmd.Guard)), cmds, VisitStmtList(whileCmd.Body));
    }

    public virtual IfCmd VisitIfCmd(IfCmd ifCmd)
    {
        return new IfCmd(new Token(ifCmd.tok.line, ifCmd.tok.col), (ifCmd.Guard == null ? null : VisitExpr(ifCmd.Guard)), VisitStmtList(ifCmd.thn), (ifCmd.elseIf == null ? null : VisitIfCmd(ifCmd.elseIf)), (ifCmd.elseBlock == null ? null : VisitStmtList(ifCmd.elseBlock)));
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
    {
        MapAssignLhs lhs = node.Clone() as MapAssignLhs;
        lhs.Indexes = new List<Expr>(lhs.Indexes);
        return base.VisitMapAssignLhs(lhs);
    }

}


} // end namespace QED