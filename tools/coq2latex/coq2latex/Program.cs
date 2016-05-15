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
            Action<string, int, Func<string[], string>> le = parsing.AddHandler;

            // coq aliases
            string staticExpression = "sfrme";
            string staticFormula = "sfrmphi'";
            string staticSemantics = "hoareSingle";
            string dynamicExpression = "evale";
            string dynamicFormula = "evalphi'";
            string dynamicSemantics = "dynSem";

            Action<string, string> commandify2 = (s, t) => le(s, 0, _ => @"\" + t);
            Action<string> commandify = s => commandify2(s, s);
            Action<string> swallowCtor = s => le(s, 1, x => x[0]);
            Action<string, string> functionify2 = (s, t) => le(s, 1, x => @"\" + t + "(" + x[0] + ")");
            Action<string> functionify = s => functionify2(s, s);

            le(staticExpression,
                2,
                x => x[0] + @" \sfrme " + x[1]);
            le(staticFormula,
                2,
                x => x[0] + @" \sfrmphi " + x[1]
            );
            le("sfrmphi",
                2,
                x => x[0] + @" \sfrmphi " + x[1]
            );
            le(staticSemantics,
                4,
                x => @"\hoare {" + x[0] + "} {" + x[1] + "} {" + x[2] + "} {" + x[3] + "}"
            );

            le(dynamicExpression,
                4,
                x => @"\evalex {" + x[0] + "} {" + x[1] + "} {" + x[2] + "} {" + x[3] + "}");
            le(dynamicFormula,
                4,
                x => @"\evalphix {" + x[0] + "} {" + x[1] + "} {" + x[2] + "} {" + x[3] + "}");
            le("evalphi",
                4,
                x => @"\evalphix {" + x[0] + "} {" + x[1] + "} {" + x[2] + "} {" + x[3] + "}");
            le(dynamicSemantics,
                2,
                x => @"{" + x[0] + @"} \rightarrow {" + x[1] + @"}"
            );

            le("In",
                2,
                x => x[0] + @" \in " + x[1]
            );
            swallowCtor("vo");
            swallowCtor("ev");
            swallowCtor("ex");
            le("edot",
                2,
                x => x[0] + "." + x[1]
            );
            le("appEnd",
                2,
                x => x[0] + @"{\:*\:}" + x[1]
            );
            commandify2("phiTrue", "true");
            le("phiEq",
                2,
                x => x[0] + @"{\:=\:}" + x[1]
            );
            le("phiImplies",
                2,
                x => x[0] + @"{\:\implies\:}" + x[1]
            );
            le("phiNeq",
                2,
                x => x[0] + @"{\:\neq\:}" + x[1]
            );
            le("phiAcc",
                2,
                x => @"\acc(" + x[0] + "," + x[1] + ")"
            );
            le("rhoFrom2",
                4,
                x => "[" + x[0] + @"{\:\mapsto\:}" + x[1] + "," + x[2] + @"{\:\mapsto\:}" + x[3] + "]"
            );
            le("rhoSubst",
                3,
                x => x[2] + "[" + x[0] + @"{\:\mapsto\:}" + x[1] + "]"
            );
            le("HSubst",
                4,
                x => x[3] + "[" + x[0] + @"{\:\mapsto\:}[" + x[1] + @"{\:\mapsto\:}" + x[2] + "]]");
            le("HSubsts",
                3,
                x => x[2] + "[" + x[0] + @"{\:\mapsto\:}[" + x[1] + "]]");
            le("phiSubst",
                3,
                x => x[2] + "[" + x[1] + "/" + x[0] + "]"
            );
            le("phiSubsts2",
                5,
                x => x[4] + "[" + x[1] + "," + x[3] + "/" + x[0] + "," + x[2] + "]"
            );
            le("phiSubsts3",
                7,
                x => x[6] + "[" + x[1] + "," + x[3] + "," + x[5] + "/" + x[0] + "," + x[2] + "," + x[4] + "]"
            );
            le("phiSubsts",
                2,
                x => x[1] + "[" + x[0] + "]"
            );
            le("sAlloc",
                2,
                x => x[0] + @"{\::=\:\new\:}" + x[1]
            );
            le("sMemberSet",
                3,
                x => x[0] + "." + x[1] + @"{\::=\:}" + x[2]
            );
            le("sCall",
                4,
                x => x[0] + @"{\::=\:}" + x[1] + "." + x[2] + "(" + x[3] + ")"
            );
            le("sAssign",
                2,
                x => x[0] + @"{\::=\:}" + x[1]
            );
            le("sReturn",
                1,
                x => @"{\return}" + x[0]
            );
            le("sAssert",
                1,
                x => @"{\assert}" + x[0]
            );
            le("sRelease",
                1,
                x => @"{\release}" + x[0]
            );
            le("Aexcept",
                2,
                x => x[0] + @"{\:\backslash\:}" + x[1]
            );
            functionify("Gamma");
            functionify("rho");
            functionify("rho'");
            functionify("Heap");
            functionify("Heap'");
            commandify("Gamma");
            commandify("rho");
            commandify("rho'");
            commandify("Heap");
            commandify("Heap'");
            commandify2("s_bar", "overline{s}");
            commandify2("r_bar", "overline{r}");

            functionify2("fieldsNames", "fields");
            functionify2("fields", "fields");
            functionify2("staticFootprint", "staticFP");
            le("footprint", 3, x => @"\texttt{footprint}_{" + x[0] + "," + x[1] + "}(" + x[2] + ")");
            le("footprint'", 3, x => @"\texttt{footprint}_{" + x[0] + "," + x[1] + "}(" + x[2] + ")");

            swallowCtor("Some");
            swallowCtor("TClass");
            le("option_map", 2, x => {
                if (x[0].Contains("fun") || !x[0].StartsWith("(") || !x[0].EndsWith(")"))
                    throw new Exception("asd");
                return x[0].Substring(1, x[0].Length - 2) + " " + x[1];
            });
            commandify2("TPrimitiveInt", "Tint");
            commandify2("None", "bot");
            commandify("vnull");
            commandify("xresult");
            commandify("xthis");
            commandify("phi");
            commandify("phi_1");
            commandify("phi_2");
            commandify("phi_r");
            commandify("phi_p");
            commandify("phi_q");
            commandify2("phi_pre", "phi_{pre}");
            commandify2("phi_post", "phi_{post}");
            le("mpre", 2, x => @"\mpre" + "(" + x[0] + "," + x[1] + ")");
            le("mpost", 2, x => @"\mpost" + "(" + x[0] + "," + x[1] + ")");
            le("mbody", 2, x => @"\mbody" + "(" + x[0] + "," + x[1] + ")");
            le("mparam", 2, x => @"\mparam" + "(" + x[0] + "," + x[1] + ")");

            le("fold_left",
                3,
                x =>
                {
                    var funMatch = Regex.Match(x[0], @"^\(\s*fun\s+(?<a1>.*?)\s+(?<a2>.*?)\s*=>(?<body>.*)\)$", RegexOptions.Singleline);
                    var funBody = funMatch.Groups["body"].Value;
                    funBody = funBody.Replace(funMatch.Groups["a2"].Value, @"\overline{" + x[1] + "_i}");
                    funBody = funBody.Replace(funMatch.Groups["a1"].Value, x[2]);
                    return funBody;
                }
            );
            le("map",
                2,
                x =>
                {
                    var funMatch = Regex.Match(x[0], @"^\(\s*fun\s+(?<a1>.*?)\s*=>(?<body>.*)\)$", RegexOptions.Singleline);
                    var funBody = funMatch.Groups["body"].Value;
                    funBody = funBody.Replace(funMatch.Groups["a1"].Value, x[1] + "_i");
                    return @"\overline{" + funBody + "}";
                }
            );

            File.WriteAllLines(dir.FullName + "\\latex\\staticExpression.tex",
                parsing.ParseInductive(staticExpression));
            File.WriteAllLines(dir.FullName + "\\latex\\staticFormula.tex",
                parsing.ParseInductive(staticFormula));
            File.WriteAllLines(dir.FullName + "\\latex\\staticSemantics.tex",
                parsing.ParseInductive(staticSemantics));
            //File.WriteAllLines(dir.FullName + "\\latex\\dynamicExpression.tex",
            //    parsing.ParseInductive(dynamicExpression));
            File.WriteAllLines(dir.FullName + "\\latex\\dynamicFormula.tex",
                parsing.ParseInductive(dynamicFormula));
            File.WriteAllLines(dir.FullName + "\\latex\\dynamicSemantics.tex",
                parsing.ParseInductiveSpecial(dynamicSemantics));

            Console.WriteLine("DONE");
            //Console.ReadKey();
        }
    }
}
