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
using System.Threading;
using Microsoft.Boogie.VCExprAST;
using VC;


    // this supports LabeledExpr
    //internal class MyBoogieExprTranslator : Boogie2VCExprTranslator
    //{

    //    public MyBoogieExprTranslator(VCExpressionGenerator gen,
    //                       VCGenerationOptions genOptions)
    //        : base (gen, genOptions)
    //    {

    //    }

    //    public override Absy Visit(Absy node)
    //    {
    //        string typeName = node.GetType().ToString();
    //        string className = typeName.Substring(typeName.LastIndexOf(".") + 1);
    //        switch (className)
    //        {
    //            case "LabeledExpr":
    //                return this.VisitLabeledExpr((LabeledExpr)node);
    //            default:
    //                return base.Visit(node);
    //        }
    //    }
        
    //    public virtual LabeledExpr VisitLabeledExpr(LabeledExpr node)
    //    {
    //        Push(TranslateLabeledExpr(node));
    //        return node;
    //    }

    //    private VCExpr TranslateLabeledExpr(LabeledExpr node)
    //    {
    //        VCExpr vcexpr = Translate(node.expr);
    //        if (node.pos)
    //        {
    //            return Gen.LabelPos(node.label, vcexpr);
    //        }
    //        else
    //        {
    //            return Gen.LabelNeg(node.label, vcexpr);
    //        }
    //    }
    //}

    public class Prover
    {

        static private Prover instance;

        static internal bool isOn = true;

        static internal bool genModel = false;
        static public bool EnableModel { set { genModel = value; } }

        internal ConditionGeneration vcgen;

        static public Prover Init(Program prog)
        {
            if (instance != null)
            {
                instance.Close();
            }
            instance = new Prover(prog);
            return instance;
        }

        static public Prover GetInstance()
        {
            Debug.Assert(instance != null);
            return instance;
        }

        private Program program;
        private int timeout;
        private readonly Stack<Checker> checkers;
        private Checker checkerForModel;
        private Mutex mutex;
        private Semaphore semaphore;

        public Checker AcquireChecker()
        {
            if (genModel)
            {
                return GetCheckerForModel();
            }

            semaphore.WaitOne();

            mutex.WaitOne();

            Checker ch = null;

            if (checkers.Count == 0)
            {
                ch = CreateChecker();
            }
            else
            {
                ch = checkers.Pop();
            }
            
            mutex.ReleaseMutex();

            return ch;
        }

        public void ReleaseChecker(Checker checker)
        {
            if (genModel)
            {
                return;
            }

            mutex.WaitOne();

            checkers.Push(checker);

            mutex.ReleaseMutex();

            semaphore.Release(1);
        }

        private Checker CreateChecker()
        {
            // TODO: get rid of this trick later, we do not need an implementation
            Implementation impl = new Implementation(Token.NoToken, "dummy", new TypeVariableSeq(), new VariableSeq(), new VariableSeq(), new VariableSeq(), new List<Block>());
            impl.Proc = new Procedure(Token.NoToken, "dummy", new TypeVariableSeq(), new VariableSeq(), new VariableSeq(), new RequiresSeq(), new IdentifierExprSeq(), new EnsuresSeq());

            // CommandLineOptions.Clo.PrintErrorModel = 4; // this also enables model generation by Z3
            CommandLineOptions.Clo.Z3Options = GetZ3Options();
		    CommandLineOptions.Clo.Bitvectors = CommandLineOptions.BvHandling.None;
            return new Checker(this.vcgen, program, null, false, impl, timeout);
        }

        private Checker GetCheckerForModel()
        {
            if (checkerForModel == null)
            {
                CommandLineOptions.Clo.PrintErrorModel = 4; // (/m) this enables model generation by Z3
                checkerForModel = CreateChecker();
            }
            return checkerForModel;
        }


        internal static List<string> GetZ3Options()
        {
            return Util.ReadLinesFromFile(Util.GetExecutingPath() + "\\z3.ini");
        }

        public void Close()
        {
            if (checkerForModel != null) checkerForModel.Close();
            checkerForModel = null;
            foreach (Checker ch in checkers) ch.Close();
            checkers.Clear();
        }

        private Prover(Program prog)
        {
            this.program = prog;
            this.timeout = CommandLineOptions.Clo.VcsFinalAssertTimeout; // TODO: check out other possibilities later
            this.checkers = new Stack<Checker>();
            this.mutex = new Mutex(false);

            this.vcgen = new VCGen(this.program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend);

            int numCheckers = ProofState.GetInstance().config.GetInt("Prover", "NumCheckers", 10);
            this.semaphore = new Semaphore(0, numCheckers);
            semaphore.Release(numCheckers);
        }

        internal Set<string> failedLabels = new Set<string>();
        internal ErrorModel errorModel;

        public Set<string> GetErrorLabels()
        {
            return new Set<string>(failedLabels);
        }

        public ErrorModel GetErrorModel()
        {
            return errorModel;
        }

        internal class ErrorReporter : ProverInterface.ErrorHandler
        {
            public Prover prover;

            public ErrorReporter(Prover p)
            { this.prover = p; }

            override public void OnModel(IList<string> labels, ErrorModel errModel)
            {
                foreach (string str in labels)
                {
                    prover.failedLabels.Add(str);
                }
                prover.errorModel = errModel; // may be null
            }
        }

        public bool CheckUnSat(Expr expr)
        {
            return CheckValid(Expr.Not(expr));
        }

        public bool CheckUnSat(Expr expr, Checker ch)
        {
            return CheckValid(Expr.Not(expr), ch);
        }

        public bool CheckValid(Expr expr)
        {
            Checker ch = AcquireChecker();

            bool result = CheckValid(expr, ch);

            ReleaseChecker(ch);

            return result;
        }

        // this uses a special checker configured to produce error models upon failure to prove
        public bool CheckValid(Expr expr, out ErrorModel errModel)
        {
            bool oldGenModel = genModel;
            genModel = true;

            bool result = CheckValid(expr); // this will use the checker with model generation

            if (result == false)
            {
                Debug.Assert(this.errorModel != null);
                errModel = this.errorModel;
            }
            else
            {
                errModel = null;
            }
            genModel = oldGenModel;
            return result;
        }

        public bool CheckValid(Expr expr, Checker ch)
        {
            if (!Prover.isOn) return true; // we do not really check, just return true

            // typecheck expression
            ProofState.GetInstance().ResolveTypeCheckExpr(expr, false);

            Debug.Assert(expr.Type != null, "Typecheck the expression before feeding to the theorem prover!");

            failedLabels.Clear();

            Statistics.Count("numProverCalls");

            ErrorReporter reporter = new ErrorReporter(this);

            return DoCheck(ch, expr, reporter);
        }

        public bool DoCheck(Checker ch, Expr expr, ProverInterface.ErrorHandler handler)
        {
            ProverContext ctx = ch.TheoremProver.Context;

            VCExpr vc = ctx.BoogieExprTranslator.Translate(expr);

            ch.BeginCheck("", vc, handler);
            ch.ProverDone.WaitOne();

            ProverInterface.Outcome outcome;

            try
            {
                outcome = ch.ReadOutcome();
            }
            catch // (UnexpectedProverOutputException)
            {
                outcome = ProverInterface.Outcome.Undetermined;
            }

            if (outcome == ProverInterface.Outcome.Valid)
            {
                return true;
            }
            return false;
        }


        internal void Relaunch()
        {
            Close();
        }
    } // end class Prover

public class ProverCommand : ProofCommand
{
    bool on;

    public ProverCommand(bool o)
        : base("prover")
    {
        this.on = o;
        desc = "prover " + (on ? "on" : "off");
    }

    public static string Usage()
    {
        return "prover on|off";
    }

    public static ProofCommand Parse(CmdParser parser)
    {
        if (parser.NextAsString().Equals("prover"))
        {
            string onoff = parser.NextAsString();
            return new ProverCommand(onoff == "on");
        }
        return null;
    }


    override public bool Run(ProofState proofState)
    {
        Prover.isOn = this.on;
        return false;
    }

} // end class ProverCommand

//***************************************************************************************************
/*
  public class Checker 
  {
    private readonly VCExpressionGenerator gen;
    private readonly MyBoogieExprTranslator translator;

    private ProverInterface thmProver;
    private CommandLineOptions.BvHandling bitvectors;
    private int timeout;

    // state for the async interface
    private volatile ProverInterface.Outcome outcome;
    private volatile bool busy;
    private volatile bool hasOutput;
    private volatile UnexpectedProverOutputException outputExn;
    private DateTime proverStart;
    private TimeSpan proverRunTime;
    private volatile ProverInterface.ErrorHandler handler;

    public readonly AutoResetEvent ProverDone = new AutoResetEvent(false);

    public bool WillingToHandle(int timeout)
    {
        return timeout == this.timeout && bitvectors == CommandLineOptions.BvHandling.None; // TODO: handle this later
    }

    public VCExpressionGenerator VCExprGen
    {
      get { return this.gen; }
    }

    /// <summary>
    /// Constructor.  Initialize a the checker with the program and log file.
    /// </summary>
    public Checker(Program prog, int timeout)
    {
      this.bitvectors = CommandLineOptions.BvHandling.None; // handle this later
      this.timeout = timeout;

      Dictionary<string,object> options = new Dictionary<string,object>();

      if (timeout > 0) {
        options["TIMELIMIT"] = timeout * 1000;
      }

      options["BITVECTORS"] = this.bitvectors;

      ProverInterface prover = (ProverInterface)CommandLineOptions.Clo.TheProverFactory.SpawnProver(options);
      this.thmProver = prover;
      this.gen = prover.VCExprGen;
      ProverContext ctx = prover.Context;

      // change the VCTranslator
      translator = new MyBoogieExprTranslator(ctx.ExprGen, ctx.VCGenOptions);

      // set up the context
      foreach (Declaration decl in prog.TopLevelDeclarations) {
          TypeCtorDecl t = decl as TypeCtorDecl;
        if (t != null) {
          ctx.DeclareType(t, null);
        }
      }
      foreach (Declaration decl in prog.TopLevelDeclarations) {
        Constant c = decl as Constant;
        if (c != null) {
          ctx.DeclareConstant(c, c.Unique, null);
        } else {
          Function f = decl as Function;
          if (f != null) {
            ctx.DeclareFunction(f, null);
          }
        }
      }
      foreach (Declaration decl in prog.TopLevelDeclarations) {
        bool expand = false;
        Axiom ax = decl as Axiom;
        decl.CheckBooleanAttribute("expand", ref expand);
        if (!expand && ax != null) {
          ctx.AddAxiom(ax, null);
        }
      }
      foreach (Declaration decl in prog.TopLevelDeclarations) {
        GlobalVariable v = decl as GlobalVariable;
        if (v != null) {
          ctx.DeclareGlobalVariable(v, null);
        }
      }
        
      // base();
    }

    /// <summary>
    /// Clean-up.
    /// </summary>
    public void Close()
    {
      thmProver.Close();
    }

    public bool IsBusy
    {
      get { return busy; }
    }

    public bool HasOutput
    {
      get { return hasOutput; }
    }

    public TimeSpan ProverRunTime
    {
      get { return proverRunTime; }
    }

    private void WaitForOutput(object dummy)
    {
        try
        {
            outcome = thmProver.CheckOutcome(handler);
        }
        catch (UnexpectedProverOutputException e)
        {
            outputExn = e;
        }
        catch (AssumeException)
        {
            outcome = ProverInterface.Outcome.Undetermined;
        }

      switch (outcome) {
        case ProverInterface.Outcome.Valid:
          thmProver.LogComment("Valid");
          break;
        case ProverInterface.Outcome.Invalid:
          thmProver.LogComment("Invalid");
          break;
        case ProverInterface.Outcome.TimeOut:
          thmProver.LogComment("Timed out");
          break;
        case ProverInterface.Outcome.Undetermined:
          thmProver.LogComment("Undetermined");
          break;
      }

      Debug.Assert(busy);
      hasOutput = true;
      proverRunTime = DateTime.Now - proverStart;

      ProverDone.Set();
    }

    public bool DoCheck(Expr expr, ProverInterface.ErrorHandler handler)
    {

        VCExpr vc = translator.Translate(expr);
        
        BeginCheck("", vc, handler);
        ProverDone.WaitOne();
        ProverInterface.Outcome outcome = ReadOutcome();
        if (outcome == ProverInterface.Outcome.Valid)
        {
            return true;
        }
        return false;
    }
    
    public void BeginCheck(string descriptiveName, VCExpr vc, ProverInterface.ErrorHandler handler) 
    {
      Debug.Assert(!IsBusy);
      busy = true;
      hasOutput = false;
      outputExn = null;
      this.handler = handler;

      thmProver.LogComment(descriptiveName);
      proverStart = DateTime.Now;
      thmProver.BeginCheck(descriptiveName, vc, handler);
      // gen.ClearSharedFormulas();

      ThreadPool.QueueUserWorkItem(WaitForOutput);
    }

    public ProverInterface.Outcome ReadOutcome()
    {
        Debug.Assert(IsBusy);
        Debug.Assert(HasOutput);

        hasOutput = false;
        busy = false;

        if (outputExn != null)
        {
            throw outputExn;
        }

        return outcome;
    }
  }
 */
  
} // end namespace QED