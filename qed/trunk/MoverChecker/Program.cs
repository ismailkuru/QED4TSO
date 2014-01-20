namespace QED
{

    using System;
    using System.Collections.Generic;
    using System.Linq;
    using System.Text;
    using Microsoft.Boogie;

    public class Program
    {
        static void Main(string[] args)
        {
            string filename = null;
            bool online = true;
            //if (args != null && args.Length > 0)
            //{
            //    filename = args[0];
            //    online = false;
            //}

            // init qed with default configuration
            Verifier verifier = Verifier.CreateDefault();
            Output.DebugEnabled = false;

            // assume all procedures atomic
            verifier.config.Set("Input", "IsAllProcsAtomic", true);

            while (true)
            {
                // load the file
                if (online)
                {
                    // get the program from the input
                    StringBuilder strb = new StringBuilder("");
                    string line = Console.ReadLine();
                    while (line != null)
                    {
                        if (line.StartsWith("//EndProgram"))
                        {
                            break;
                        }

                        strb.AppendLine(line);
                        line = Console.ReadLine();
                    }

                    Microsoft.Boogie.Program program = Qoogie.ParseProgram("Program", strb.ToString());
                    Microsoft.Boogie.Program prelude = Prelude.GetPrelude();
                    // add the prelude
                    program.TopLevelDeclarations.AddRange(prelude.TopLevelDeclarations);
                    foreach (Record record in prelude.Records.Values)
                    {
                        program.Records.Add(record.Name, record);
                    }

                    if (!verifier.LoadProgram(program))
                    {
                        Console.WriteLine("ERROR: Failed loading the program!");
                        return;
                    }
                }
                else
                {
                    if (!verifier.LoadProgram(filename))
                    {
                        Console.WriteLine("ERROR: Failed loading the program!");
                        return;
                    }
                }

                // do the mover check
                MoverCommand moverCommand = new MoverCommand("all", false, false);
                moverCommand.Run(verifier.ProofState);
                List<MoverCheck> mcs = moverCommand.mcs;


                // print the results
                Console.WriteLine("BEGINRESULTS");
                foreach (ProcedureState procState in verifier.ProofState.ProcedureStates)
                {
                    // get the body block
                    AtomicBlock bodyBlock = procState.AtomicBlocks[0];
                    Console.WriteLine(procState.Name + ":" + bodyBlock.Mover.ToString());
                }
                Console.WriteLine("ENDRESULTS");
                Console.Out.Flush();

                // print the failures
                //Output.AddLine(); Output.AddLine("Failed checks:");
                //foreach (MoverCheck mc in mcs)
                //{
                //    Output.AddLine(mc.ToString());
                //}

                if (!online)
                {
                    break;
                }
            }
        }
    }
}
