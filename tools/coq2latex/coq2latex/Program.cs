using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace coq2latex
{
    class Program
    {
        static void Main(string[] args)
        {
            Debug.Listeners.Add(new ConsoleTraceListener());

            string coqFileName = "GradVer.v";
            string coqFile;
            DirectoryInfo dir = new DirectoryInfo(Directory.GetCurrentDirectory());
            while (dir != null && !dir.EnumerateFiles(coqFileName).Any())
                dir = dir.Parent;
            if (dir == null)
                throw new FileNotFoundException(coqFileName);
            coqFile = File.ReadAllText(dir.FullName + "\\" + coqFileName);
            var parsing = new CoqParsing(coqFile);
            var le = parsing.latexifyExpression;

            // coq aliases
            string staticExpression = "sfrme";
            string staticFormula = "sfrmphi'";
            string staticSemantics = "hoareSingle";

            Action<string, string> commandify2 = (s, t) => le[s] = new Tuple<int, Func<string[], string>>(0, _ => @"\" + t);
            Action<string> commandify = s => commandify2(s, s);
            Action<string> swallowCtor = s => le[s] = new Tuple<int, Func<string[], string>>(1, x => x[0]);
            Action<string, string> functionify2 = (s, t) => le[s] = new Tuple<int, Func<string[], string>>(1, x => @"\" + t + "(" + x[0] + ")");
            Action<string> functionify = s => functionify2(s, s);

            le[staticExpression] = new Tuple<int, Func<string[], string>>(
                2,
                x => x[0] + @" \sfrme " + x[1]
            );
            le[staticFormula] = new Tuple<int, Func<string[], string>>(
                2,
                x => x[0] + @" \sfrmphi " + x[1]
            );
            le["sfrmphi"] = new Tuple<int, Func<string[], string>>(
                2,
                x => x[0] + @" \sfrmphi " + x[1]
            );
            le[staticSemantics] = new Tuple<int, Func<string[], string>>(
                4,
                x => @"\hoare {" + x[0] + "} {" + x[1] + "} {" + x[2] + "} {" + x[3] + "}"
            );
            le["In"] = new Tuple<int, Func<string[], string>>(
                2,
                x => x[0] + @" \in " + x[1]
            );
            swallowCtor("ev");
            swallowCtor("ex");
            le["edot"] = new Tuple<int, Func<string[], string>>(
                2,
                x => x[0] + "." + x[1]
            );
            le["appEnd"] = new Tuple<int, Func<string[], string>>(
                2,
                x => x[0] + @"{\:*\:}" + x[1]
            );
            commandify2("phiTrue", "true");
            le["phiEq"] = new Tuple<int, Func<string[], string>>(
                2,
                x => x[0] + @"{\:=\:}" + x[1]
            );
            le["phiImplies"] = new Tuple<int, Func<string[], string>>(
                2,
                x => x[0] + @"{\:\implies\:}" + x[1]
            );
            le["phiNeq"] = new Tuple<int, Func<string[], string>>(
                2,
                x => x[0] + @"{\:\neq\:}" + x[1]
            );
            le["phiAcc"] = new Tuple<int, Func<string[], string>>(
                2,
                x => @"\acc(" + x[0] + "," + x[1] + ")"
            );
            le["phiSubst"] = new Tuple<int, Func<string[], string>>(
                3,
                x => x[2] + "[" + x[0] + "/" + x[1] + "]"
            );
            le["sAlloc"] = new Tuple<int, Func<string[], string>>(
                2,
                x => x[0] + @"{\::=\:\new\:}" + x[1]
            );
            le["sMemberSet"] = new Tuple<int, Func<string[], string>>(
                3,
                x => x[0] + @"{\::=\:}" + x[1] + "." + x[2]
            );
            le["sAssign"] = new Tuple<int, Func<string[], string>>(
                3,
                x => x[0] + @"{\::=\:}" + x[1]
            );
            le["sReturn"] = new Tuple<int, Func<string[], string>>(
                1,
                x => @"{\return}" + x[0]
            );
            le["sAssert"] = new Tuple<int, Func<string[], string>>(
                1,
                x => @"{\assert}" + x[0]
            );
            le["sRelease"] = new Tuple<int, Func<string[], string>>(
                1,
                x => @"{\release}" + x[0]
            );
            functionify("Gamma");
            functionify("rho");
            functionify2("fieldsNames", "fields");

            swallowCtor("Some");
            swallowCtor("TClass");
            commandify2("TPrimitiveInt", "Tint");
            commandify("vnull");
            commandify("xresult");
            commandify("xthis");

            le["fold_left"] = new Tuple<int, Func<string[], string>>(
                3,
                x =>
                {
                    var funMatch = Regex.Match(x[0], @"^\(\s*fun\s+(?<a1>.*?)\s+(?<a2>.*?)\s*=>(?<body>.*)\)$", RegexOptions.Singleline);
                    var funBody = funMatch.Groups["body"].Value;
                    funBody = funBody.Replace(funMatch.Groups["a2"].Value, x[1]);
                    funBody = funBody.Replace(funMatch.Groups["a1"].Value, x[2]);
                    return @"\overline{" + funBody + "}";
                }
            );

            File.WriteAllLines(dir.FullName + "\\latex\\staticExpression.tex",
                parsing.ParseInductive(staticExpression));
            File.WriteAllLines(dir.FullName + "\\latex\\staticFormula.tex",
                parsing.ParseInductive(staticFormula));
            File.WriteAllLines(dir.FullName + "\\latex\\staticSemantics.tex",
                parsing.ParseInductive(staticSemantics));

            Console.WriteLine("DONE");
            //Console.ReadKey();
        }
    }
}
