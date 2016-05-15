using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace coq2latex
{
    class CoqParsing
    {
        public static readonly string regexCoqExpression =
            @"\s*?" +
            @"(\(((?<BR>\()|(?<-BR>\))|[^()]*)+\)(?(BR)(?!))" +
            @"|(\w|\'|\\)+)" +
            @"\s*?";

        private string coqFile;
        private Dictionary<string, Func<string[], string>> latexifyExpression;

        public void AddHandler(string name, int arity, Func<string[], string> handler)
        {
            latexifyExpression[name + "@" + arity] = handler;
        }

        public CoqParsing(string coqFile)
        {
            this.coqFile = coqFile;
            this.latexifyExpression = new Dictionary<string, Func<string[], string>>();
        }

        private string RemoveExpressions(string s)
        {
            var sparseMatches = Regex.Matches(s, regexCoqExpression).OfType<Match>().Reverse();
            // erase expressions
            foreach (var match in sparseMatches)
                s = s.Remove(match.Index, match.Length).Insert(match.Index, new string(' ', match.Length));
            return s;
        }

        private string PreFormat(string coq)
        {
            coq = coq.Replace("[]", @"\emptyset");
            coq = coq.Replace(" :: ", @"*");
            coq = coq.Replace(":: ", @"*");
            coq = coq.Replace(" ::", @"*");
            coq = coq.Replace("::", @"*");
            coq = coq.Replace(" ++ ", @"*");
            coq = coq.Replace("++ ", @"*");
            coq = coq.Replace(" ++", @"*");
            coq = coq.Replace("++", @"*");
            return coq;
        }
        private string PostFormat(string coq)
        {
            coq = coq.Replace(@" * S", @" \cdot S");
            coq = coq.Replace(@" * \overline{s", @"; \overline{s");
            coq = coq.Replace(@"<>", @" \neq ");
            return coq;
        }

        public string LatexifyExpression(string coq)
        {
            coq = PreFormat(coq);
            coq = coq.Trim();
            if (coq == "")
                return coq;
            var coqX = RemoveExpressions(coq);
            if (coqX.Trim() != "")
            {
                // get delimiters
                var delims = new List<Tuple<int, int>>();
                while (coqX.Trim() != "")
                {
                    coqX = coqX.TrimEnd();
                    var index2 = coqX.Length;
                    var index1 = coqX.LastIndexOf(' ') + 1;
                    delims.Add(new Tuple<int, int>(index1, index2));
                    coqX = coqX.Substring(0, index1);
                }
                delims.Add(new Tuple<int, int>(0, 0));
                // replace
                var lastDelimStart = coq.Length;
                foreach (var delim in delims)
                {
                    var part = coq.Substring(delim.Item2, lastDelimStart - delim.Item2);
                    part = " " + LatexifyExpression(part) + " ";
                    coq = coq.Remove(delim.Item2, lastDelimStart - delim.Item2).Insert(delim.Item2, part);
                    lastDelimStart = delim.Item1;
                }

                return coq;
            }
            var matches = Regex.Matches(coq, regexCoqExpression);
            if (matches.Count == 1)
                if (coq.StartsWith("("))
                {
                    var inner = LatexifyExpression(coq.Substring(1, coq.Length - 2));
                    if (inner.Contains(" "))
                        return "(" + inner + ")";
                    else
                        return inner;
                }
                else
                {
                    if (latexifyExpression.ContainsKey(coq + "@0"))
                        return latexifyExpression[coq + "@0"](new string[0]);
                    return coq;
                }
            var xs = matches.OfType<Match>().Select(x => x.Value);
            if (latexifyExpression.ContainsKey(xs.First() + "@" + (matches.Count - 1)))
                return latexifyExpression[xs.First() + "@" + (matches.Count - 1)](xs.Skip(1).Select(LatexifyExpression).ToArray());
            return string.Join(" ", xs);
        }

        public IEnumerable<string> ParseInductive(string name)
        {
            Debug.WriteLine("Inductive: " + name);
            Regex regex = new Regex("Inductive " + name + ".*?:=(?<def>.*?)\\.",
                RegexOptions.ExplicitCapture |
                RegexOptions.Singleline);
            var match = regex.Match(coqFile);
            var s = match.Groups["def"].Value;

            Regex regexCtor = new Regex(@"\|(?<name>.*?):(" + regexCoqExpression + @")*?,(?<pre>([^|]*?->)*)(?<con>.*?)(?=$|\|)",
                RegexOptions.ExplicitCapture |
                RegexOptions.Singleline);
            foreach (Match ctor in regexCtor.Matches(s))
            {
                var cname = ctor.Groups["name"].Value.Trim();
                var ccon = ctor.Groups["con"].Value.Trim();
                var cprems = ctor.Groups["pre"].Value.Split(new string[] { "->" }, StringSplitOptions.RemoveEmptyEntries).Select(x => x.Trim()).ToArray();

                Debug.WriteLine("\tCtor: " + cname);

                StringBuilder res = new StringBuilder();
                res.AppendLine(@"\begin{mathpar}");
                res.AppendLine(@"\inferrule* [Right=" + cname + "]");
                if (cprems.Length == 0)
                    res.AppendLine("{~}");
                else
                    res.AppendLine("{" + string.Join(@"\\", cprems.Select(LatexifyExpression)) + "}");
                res.AppendLine("{" + LatexifyExpression(ccon) + "}");
                res.AppendLine(@"\end{mathpar}");
                yield return PostFormat(res.ToString());
            }
        }
        private string LatexGray(string inner)
        {
            return @"\textcolor{gray}{" + inner + "}";
        }
        public IEnumerable<string> ParseInductiveSpecial(string name)
        {
            Debug.WriteLine("Inductive: " + name);
            Regex regex = new Regex("Inductive " + name + ".*?:=(?<def>.*?)\\.",
                RegexOptions.ExplicitCapture |
                RegexOptions.Singleline);
            var match = regex.Match(coqFile);
            var s = match.Groups["def"].Value;

            Regex regexCtor = new Regex(@"\|(?<name>.*?):(" + regexCoqExpression + @")*?,(?<pre>([^|]*?->)*)(?<con>.*?)(?=$|\|)",
                RegexOptions.ExplicitCapture |
                RegexOptions.Singleline);
            foreach (Match ctor in regexCtor.Matches(s))
            {
                var cname = ctor.Groups["name"].Value.Trim();
                var ccon = ctor.Groups["con"].Value.Trim();
                var cprems = ctor.Groups["pre"].Value.Split(new string[] { "->" }, StringSplitOptions.RemoveEmptyEntries).Select(x => x.Trim()).ToArray();

                Debug.WriteLine("\tCtor: " + cname);

                StringBuilder res = new StringBuilder();
                res.AppendLine(@"\begin{mathpar}");
                res.AppendLine(@"\inferrule* [Right=" + cname + "]");
                if (cprems.Length == 0)
                    res.AppendLine("{~}");
                else
                    res.AppendLine("{" + string.Join(@"\\", cprems.Select(LatexifyExpression)
                        .Select(x => x.Contains("A") || x.Contains("phi") ? LatexGray(x) : x)) + "}");

                var latexCon = LatexifyExpression(ccon);
                var miniExpression = @"[^,]*?";
                var regexPattern = @"\((?<a>" + miniExpression + @"),(?<b>" + miniExpression + @"),(?<c>" + miniExpression + @")\)";
                latexCon = Regex.Replace(latexCon,
                    regexPattern,
                    m => "(" + m.Groups["a"].Value + "," + LatexGray(m.Groups["b"].Value) + "," + m.Groups["c"].Value + ")");

                res.AppendLine("{" + latexCon + "}");
                res.AppendLine(@"\end{mathpar}");
                yield return PostFormat(res.ToString());
            }
        }
    }
}
