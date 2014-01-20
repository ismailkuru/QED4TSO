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
            string filename = args[0];

            // Load the defalt configuration
            Configuration config = Configuration.CreateDefault();
            Output.ApplyConfiguration(config);
            Statistics.ApplyConfiguration(config);

            Output.DebugEnabled = false;

            Microsoft.Boogie.Program program = Qoogie.ParseFile(filename);
            if (program == null)
            {
                Output.Log("Error parsing the program.");
                return;
            }

            // load the prelude
            if (config.GetBool("Input", "LoadPrelude", true))
            {
                Microsoft.Boogie.Program prelude = Prelude.GetPrelude();
                if (prelude == null)
                {
                    Output.Log("Error parsing the prelude.");
                    return;
                }
                program.TopLevelDeclarations.AddRange(prelude.TopLevelDeclarations);
            }

            if (!Verifier.ResolveTypeCheck(program))
            {
                Output.LogLine("Failed in resolving/tyechecking the program");
                return;
            }

            Output.Add("YES"); 
        }
    }
}
