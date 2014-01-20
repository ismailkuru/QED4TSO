using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;

namespace QED
{
    class Program
    {
        static void Main(string[] args)
        {
            string filename = args[0];

            StreamReader from_checker;
            StreamWriter to_checker;
            Process checker = ExternalProcess.Start("MoverChecker.exe", "", out from_checker, out to_checker);

            string[] lines = File.ReadAllLines(filename);

            for (int i = 0; i < 5; ++i)
            {
                to_checker.WriteLine("//BeginProgram");
                for (int j= 0; j < lines.Length; ++j)
                {
                    to_checker.WriteLine(lines[j]);
                }
                to_checker.WriteLine("//EndProgram");
                to_checker.Flush();


                string line = from_checker.ReadLine();
                while (line != null)
                {
                    if (line.StartsWith("BEGINRESULTS"))
                    {
                        Console.WriteLine("Results:");
                    }
                    else

                        if (line.StartsWith("ENDRESULTS"))
                        {
                            break;
                        }
                        else

                            if (line.StartsWith("ERROR"))
                            {
                                break;
                            }
                            else
                            {
                                Console.WriteLine(line);
                            }

                    line = from_checker.ReadLine();
                }
            }

            checker.Kill();
        }
    }
}
