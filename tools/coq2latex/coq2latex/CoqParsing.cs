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
        public Dictionary<string, Tuple<int, Func<string[], string>>> latexifyExpression;

        public CoqParsing(string coqFile)
        {
            this.coqFile = coqFile;
            this.latexifyExpression = new Dictionary<string, Tuple<int, Func<string[], string>>>();
        }

        public string LatexifyExpression(string coq)
        {
            coq.Replace("[]", @"\emptyset");
            coq.Replace("::", @"*");
            coq = coq.Trim();
            if (coq == "")
                return coq;
            if (!Regex.IsMatch(coq, "^(" + regexCoqExpression + ")+$"))
            {
                var sparseMatches = Regex.Matches(coq, regexCoqExpression).OfType<Match>().Reverse();
                var coqX = coq;
                // erase expressions
                foreach (var match in sparseMatches)
                    coqX = coqX.Remove(match.Index, match.Length).Insert(match.Index, new string(' ', match.Length));
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
                // special handlers:
                // - A = B
                if (coqX.Count(c => c == '=') == 1)
                {
                    int index = coqX.IndexOf('=');
                    return
                        LatexifyExpression(coq.Substring(0, index)) +
                        " = " +
                        LatexifyExpression(coq.Substring(index + 1));
                }
                // - anything else
                var indices = coqX.Select((x, i) => new { X = x, I = i }).Where(x => x.X == ',').Select(x => x.I).ToList();
                indices.Reverse();
                indices.Add(-1);
                var lastIndex = coq.Length;
                foreach (var index in indices)
                {
                    string part = coq.Substring(index + 1, lastIndex - index - 1);
                    coq = coq.Remove(index + 1, lastIndex - index - 1).Insert(index + 1, " " + LatexifyExpression(part));
                    lastIndex = index;
                }
                return coq.Trim();

                return @"\verb€" + coq + "€";
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
                    if (latexifyExpression.ContainsKey(coq))
                    {
                        var handler = latexifyExpression[coq];
                        if (handler.Item1 == 0)
                            return handler.Item2(new string[0]);
                    }
                    return coq;
                }
            var xs = matches.OfType<Match>().Select(x => x.Value).Select(LatexifyExpression);
            if (latexifyExpression.ContainsKey(xs.First()))
            {
                var handler = latexifyExpression[xs.First()];
                if (handler.Item1 == matches.Count - 1)
                    return handler.Item2(xs.Skip(1).ToArray());
            }
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

            Regex regexCtor = new Regex(@"\|(?<name>.*?):.*?,(?<pre>([^|]*?->)*)(?<con>.*?)(?=$|\|)",
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
                res.AppendLine(@"\inferrule* [right=" + cname + "]");
                if (cprems.Length == 0)
                    res.AppendLine("{~}");
                else
                    res.AppendLine("{" + string.Join(@" \\ ", cprems.Select(LatexifyExpression)) + "}");
                res.AppendLine("{" + LatexifyExpression(ccon) + "}");
                res.AppendLine(@"\end{mathpar}\hfill");
                yield return res.ToString();
            }
        }
    }
}
