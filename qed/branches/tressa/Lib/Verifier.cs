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

/// <summary>
/// The main interface of QETLib to the outside
/// loads the program and the script and runs the commands
/// </summary>  
public class Verifier
{
	
  public ProofState proofState;
  
  public Configuration config;

  public History history;
  
  public Verifier(Configuration conf) {
	  
	  this.config = conf;

      this.history = new History();
  }
  
  public ProofState ProofState {
	get {
		return ProofState.GetInstance();
	}
  }

  public bool LoadProgram()
  {
      try
      {
          Program program = new Program();

          foreach (string filename in CommandLineOptions.Clo.Files)
          {
              string extension = Path.GetExtension(filename);
              if (extension != null) { extension = extension.ToLower(); }
              if (extension != ".bpl")
              {
                  Output.LogLine("*** Error: " + filename + ": Filename extension '{1}' is not supported. Input files must be either BoogiePL programs (.bpl) or assemblies (.exe or .dll)." +
                      extension == null ? "" : extension);
                  return false;
              }

              Output.LogLine("Processing the file: " + filename);

              Program prog = Qoogie.ParseFile(filename);
              if (prog == null)
              {
                  Output.Log("Error parsing the program.");
                  return false;
              }

              // success
              program.TopLevelDeclarations.AddRange(prog.TopLevelDeclarations);
          }

          // load the prelude
          bool load_prelude = (Qoogie.GetConstant(program, Prelude.tidName) == null);
          if (config.GetBool("Input", "LoadPrelude", load_prelude))
          {
              Program prelude = Prelude.GetPrelude();
              if (prelude == null)
              {
                  Output.Log("Error parsing the prelude.");
                  return false;
              }
              program.TopLevelDeclarations.AddRange(prelude.TopLevelDeclarations);
          }

          if (!ResolveTypeCheck(program))
          {
              Output.LogLine("Failed in resolving/tyechecking the program");
              return false;
          }

          if (!PreprocessProgram(program))
          {
              Output.LogLine("Failed in processing the program");
              return false;
          }

          // init the prover
          Output.LogLine("Initializing the theorem prover");
          Prover.Init(program);
          Output.LogLine("Initialized the theorem prover");

          // check the invariants
          if (!CheckInvariants(program))
          {
              Output.LogLine("Given invariants are not preserved");
              return false;
          }

          return true;

      }
      catch (Exception e)
      {
          Output.AddLine("Error while loading the program!");
          Output.Add(e);
          //throw e; // TODO: remove later
          return false;
      }
  }

  private bool CheckInvariants(Program program)
  {
      return InvariantCommand.DoRun(proofState, null);
  }
  
  private bool PreprocessProgram(Program program) {
  
		// initialize the proof state
        this.proofState = ProofState.CreateInstance(program, config);

        List<Declaration> topLevelDecls = new List<Declaration> (program.TopLevelDeclarations);
		foreach(Declaration decl in topLevelDecls) {
			Implementation impl = decl as Implementation;
			if(impl != null) {
                bool isskip = QKeyValue.FindBoolAttribute(impl.Proc.Attributes, "skip");
                bool isatomic = QKeyValue.FindBoolAttribute(impl.Proc.Attributes, "isatomic");
				bool ispublic = QKeyValue.FindBoolAttribute(impl.Proc.Attributes, "ispublic");
				
				if(!isskip) {
					Output.LogLine("Creating procedure state: " + impl.Name);
					proofState.CreateProcedureState(impl, isatomic, ispublic);
				} else {
					Output.LogLine("Skipping " + impl.Name);
				}
			}
		}
		
        // handle procedure that has no corresponding implementation.
        // these procedures are atomic.
		foreach(Declaration decl in topLevelDecls) {
			Procedure proc = decl as Procedure;
			if(proc != null) {
				if(! proofState.HasProcedureState(proc.Name)) {
                    bool isskip = QKeyValue.FindBoolAttribute(proc.Attributes, "skip");
                    bool ispublic = QKeyValue.FindBoolAttribute(proc.Attributes, "ispublic");
					
					if(!isskip) {
						Output.LogLine("Creating procedure state: " + proc.Name);
						
                        // First create the implementation
                        Implementation impl = CodeTransformations.CreateImplFromSpec(proc);
                        program.TopLevelDeclarations.Add(impl);
                        
                        proofState.CreateProcedureState(impl, true, ispublic);
					} else {
						Output.LogLine("Skipping " + proc.Name);
					}
				}
			}
		}
		
		if(!ResolveTypeCheck(program)) {
			return false;
		}
		
		// decompose the program to atomic blocks 
		
		foreach(ProcedureState procState in proofState.procedureStates.Values) {
			procState.Init(proofState);
		}
		
		if(!ResolveTypeCheck(program)) {
			return false;
		}

        //--------------------------
        proofState.UpdateCallGraph();

        // reduce atomic procedures
        //--------------------------
        if (config.GetBool("Reduction", "ReduceAtomicProcs", false))
        {
            // process atomic procedures
            List<ProcedureState> procs = new List<ProcedureState>(proofState.ProcedureStates);
            foreach (ProcedureState procState in procs)
            {
                if (!procState.IsReduced)
                {
                    procState.Reduce(proofState);
                }
            }
        }
        //--------------------------

		if(!ResolveTypeCheck(program)) {
			return false;
		}
		
        //foreach(ProcedureState procState in proofState.procedureStates.Values) {
        //    procState.PostProcess(program);
        //}	
		
        //if(!ResolveTypeCheck(program)) {
        //    return false;
        //}
		
		Output.LogLine("Done with preprocessing the program.");
		
		// save the first version of the command to the history
		this.history.Add(proofState.TextView, proofState.GraphView, "Original program", null, Statistics.Print());
		
		return true;
  }
  
  public bool RunProofScript(ProofScript proofScript) {
	bool done = false;
	
	DateTime start_time = Statistics.StartTimer();
	
	foreach(ProofCommand command in proofScript)
	{
		done = RunProofCommand(command);
		
		// Output.LogLine("Program after running the command: ");
		// Output.PrintBplFile("-", ProofState.GetInstance().program);
		
		if(done) break;
	}
	
	Statistics.StopTimer("Script Run", start_time);
	
	return true;
  }
  
  public bool RunProofCommand(ProofCommand command) {		
	bool result = false;
    bool success = false;

	if(command != null) {
		
		Output.AddLine("Running the command: " + command.ToString());

        try
        {
            result = command.Run(proofState);
            success = true;
        }
        catch (Exception e)
        {
            Output.AddError("Verifier: Error while running the command " + command.ToString());
            Output.Add(e);            
            success = false;
        }

        if (success)
        {
            if (!ResolveTypeCheck(proofState.program))
            {
                Output.AddError("Error in resolution and typecheck after the command " + command.ToString());
                BoogiePL.Errors.count = 0;
            }

            Output.AddLine("Finished with the command: " + command.ToString());

            // save the current version to the history
            this.history.Add(proofState.TextView, proofState.GraphView, "After the command: " + command.ToString(), command, Statistics.Print());

            if (config.GetBool("Output", "SaveDotFiles", false))
            {
                foreach (ProcedureState procState in proofState.procedureStates.Values)
                {
                    string dotstr = procState.DotView;
                    new Dot().SaveDotOutput(procState.impl.Name + ".txt", dotstr);
                }
            }
        }
	}
	
	return result;
  }
  
  static public bool ResolveTypeCheck(Program program) {

      BoogiePL.Errors.count = 0;

	 // force re-resolve and re-typecheck
	 foreach(Declaration decl in program.TopLevelDeclarations) {
		Implementation impl = decl as Implementation;
		if(impl != null) {
			impl.Proc = null;
		}
	 }
  
	// ---------- Resolve ------------------------------------------------------------
      
      if (CommandLineOptions.Clo.NoResolve) { return true; }

      int errorCount = program.Resolve();
      
      if (errorCount > 0) 
      {
        Output.LogLine(errorCount + " name resolution errors detected");
        return false;
      }
		
	  // Output.LogLine("Resolved the program");

      // ---------- Type check ------------------------------------------------------------
      
      if (CommandLineOptions.Clo.NoTypecheck)  { return true; }
      
      errorCount = program.Typecheck();
      
      if (errorCount > 0) 
      {
        Output.LogLine(errorCount + " typechecking errors detected");
        return false;
      }
      
      // Output.LogLine("TypeChecked the program");
      
      return true;
  }
  
  public bool CheckValid(string procname, string strExpr) {
	Expr formula = Logic.ParseFormula(proofState, procname, strExpr, false);
	return Prover.GetInstance().CheckValid(formula);
  }

} // end class MechanizedProver

} // end namespace QED

