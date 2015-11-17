using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

//- Add custom mutual summaries to symdiff-generated bpl file (by changing mutual summary function bodies)
//- Add custom mutual preconditions to symdiff-generated bpl files (by adding requires clauses to Check procedures)

class SymdiffMerge
{
    public static int Main(string[] args)
    {
        try
        {
            switch(args[0])
            {
                case "-config":
                    new SymdiffMerge().Config(args[1], args[2]);
                    return 0;
                case "-merge":
                {
                    string axiomWhitelist = (args.Length > 4 && args[3] == "-axiomWhitelist") ? args[4] : null;
                    new SymdiffMerge().Merge(args[1], args[2], axiomWhitelist);
                    return 0;
                }
                default:
                    throw new Exception("unexpected argument " + args[0]);
            }
        }
        catch (Exception e)
        {
            Console.Error.WriteLine(e);
            return -1;
        }
    }

    Dictionary<string,List<string>> preconditions = new Dictionary<string,List<string>>();
    Dictionary<string,List<string>> postconditions = new Dictionary<string,List<string>>();
    Dictionary<string,List<string>> postconditionVars = new Dictionary<string,List<string>>();
    const string funPrefix = "function {:inline true} ";

    public List<string> FunVars(string line)
    {
        string parms = line.Substring(line.IndexOf('(') + 1);
        parms = parms.Substring(0, parms.IndexOf(')'));
        return new List<string>(parms.Split(new char[] { ',' }))
            .ConvertAll(s => s.Substring(0, s.IndexOf(':')).Trim());
    }

    public void ReadMutualSummaries(string msfile)
    {
        bool inFun = false;
        List<string> data = null;
        foreach (string line in File.ReadAllLines(msfile))
        {
            bool isPre = line.StartsWith(funPrefix + "MP$");
            bool isPost = line.StartsWith(funPrefix + "MS$");
            if (isPre || isPost)
            {
                inFun = true;
                data = new List<string>();
                string f = line.Substring(0, line.IndexOf('(')).Substring(funPrefix.Length);
                (isPre ? preconditions : postconditions).Add(f, data);
                if (!isPre) { postconditionVars.Add(f, FunVars(line)); }
            }
            if (inFun)
            {
                data.Add(line);
            }
            if (line.StartsWith("}"))
            {
                inFun = false;
            }
        }
    }

    public void Config(string msfile, string configfile)
    {
        ReadMutualSummaries(msfile);
        foreach (string line in File.ReadAllLines(configfile))
        {
            if (line.StartsWith("procedure:"))
            {
                string name = line.Substring(line.IndexOf('(') + 1);
                name = name.Substring(0, name.IndexOf(')'));
                name = "MS$" + name.Replace(", ", "$");
                if (postconditions.ContainsKey(name))
                {
                    Console.WriteLine(line);
                }
            }
            else
            {
                Console.WriteLine(line);
            }
        }
    }

    public void Merge(string msfile, string mergefile, string axiomWhitelistFile)
    {
        Dictionary<string,string> axiomWhitelist = (axiomWhitelistFile == null) ? null :
            new List<string>(File.ReadAllLines(axiomWhitelistFile)).ToDictionary(x => x);
        Dictionary<string,string> alreadyPrintedAxiom = new Dictionary<string,string>();

        ReadMutualSummaries(msfile);
        bool inFun = false;
        foreach (string _line in File.ReadAllLines(mergefile))
        {
            string line = _line;
            string lineTrim = line.Trim();
            if (line.StartsWith(funPrefix + "MS$"))
            {
                //- Write mutual summary (mutual postcondition):
                inFun = true;
                string funPost = line.Substring(0, line.IndexOf('(')).Substring(funPrefix.Length);
                if (postconditions.ContainsKey(funPost))
                {
                    
                    
                    
                    
                    List<string> symdiffVars = FunVars(line);
                    List<string> ourVars = postconditionVars[funPost];
                    string lambdasBegin = "";
                    string lambdasEnd = "";
                    foreach (string ourVar in ourVars)
                    {
                        if (ourVar.StartsWith("v1_u.out_") && !symdiffVars.Contains(ourVar))
                        {
                            string x = ourVar.Substring("v1_u.out_".Length);
                            if (line.Contains("v1_u.in_" + x + ":"))
                            {
                                if (line.Contains("v1_u.in_old_" + x + ":"))
                                {
                                    line = line.Replace("v1_u.in_" + x + ":", "v1_u.out_" + x + ":");
                                    line = line.Replace("v2_u.in_" + x + ":", "v2_u.out_" + x + ":");
                                    line = line.Replace("v1_u.in_old_" + x + ":", "v1_u.in_" + x + ":");
                                    line = line.Replace("v2_u.in_old_" + x + ":", "v2_u.in_" + x + ":");
                                }
                                else
                                {
                                    string decl = line.Substring(line.IndexOf("v1_u.in_" + x + ":"));
                                    decl = decl.Substring(0, decl.IndexOf(','));
                                    string lb1 = "(lambda " + decl.Replace("v1_u.in_", "v1_u.out_") + "::(";
                                    string le1 = "))[" + "v1_u.in_" + x + "]";
                                    string lb2 = lb1.Replace("v1_u.", "v2_u.");
                                    string le2 = le1.Replace("v1_u.", "v2_u.");
                                    lambdasBegin = lb1 + lb2 + lambdasBegin;
                                    lambdasEnd = lambdasEnd + le2 + le1;
                                    line = line.Replace("{:inline true}", ""); 
                                }
                            }
                        }
                    }

                    //- Write mutual summary body
                    Console.WriteLine(line);
                    List<string> linesPost = postconditions[funPost];
                    for (int i = 1; i < linesPost.Count; i++)
                    {
                        if (linesPost[i] == "}" && lambdasEnd != "")
                        {
                            Console.WriteLine(lambdasEnd);
                        }
                        Console.WriteLine(linesPost[i]);
                        if (linesPost[i] == "{" && lambdasBegin != "")
                        {
                            Console.WriteLine(lambdasBegin);
                        }
                    }
                }
            }

            // Avoid duplicate linear collectors until Boogie collector problem is fixed
            if (line.Contains("v1_u.OurCollector"))
            {
                line = line.Replace("{:linear \"our\"}", "");
            }

            //- Try to improve performance by suppressing axioms that aren't needed
            bool suppressAxiom = axiomWhitelist != null
                && line.StartsWith("axiom ")
                && !axiomWhitelist.ContainsKey(line);
            suppressAxiom = suppressAxiom || alreadyPrintedAxiom.ContainsKey(line);

            if (!inFun && !suppressAxiom)
            {
                Console.WriteLine(line);
                if (line.StartsWith("axiom "))
                {
                    alreadyPrintedAxiom.Add(line, line);
                }
            }

            string constPrefix = "const v1_u.";
            if (lineTrim.StartsWith(constPrefix))
            {
                string x = lineTrim.Substring(constPrefix.Length);
                x = x.Substring(0, x.IndexOf(':'));
                Console.WriteLine("axiom v1_u." + x + " == v2_u." + x + ";");
            }

            string mpPrefix = "procedure MP_Check_";
            string msPrefix = "procedure MS_Check_";
            if (lineTrim.StartsWith(mpPrefix) || lineTrim.StartsWith(msPrefix))
            {
                //- Write mutual precondition:
                bool isMp = lineTrim.StartsWith(mpPrefix);
                string funPost = lineTrim.Substring(0, lineTrim.IndexOf('('));
                string s = lineTrim.Substring((isMp ? mpPrefix : msPrefix).Length);
                int v2i = s.IndexOf("v2_u.");
                int lparen = s.IndexOf('(');
                string v1 = s.Substring(0, v2i - 2);
                string v2 = s.Substring(v2i, lparen - v2i);
                string funPre = "MP$" + v1 + "$" + v2;
                if (preconditions.ContainsKey(funPre))
                {
                    Console.WriteLine(isMp ? "  requires" : "  free requires");
                    List<string> linesPre = preconditions[funPre];
                    for (int i = 2; i < linesPre.Count - 1; i++) Console.WriteLine("    " + linesPre[i]);
                    Console.WriteLine("  ;");
                }
            }
            if (line.StartsWith("}"))
            {
                inFun = false;
            }
        }
    }
}
