import { VerificationFormula, FormulaPartAcc, FormulaPartNeq, FormulaPart } from "./VerificationFormula";
import { FootprintStatic } from "./Footprint";
import { Expression } from "./Expression";

export class VerificationFormulaGradual
{
    private html: JQuery;

    public gradual: boolean;
    public staticFormula: VerificationFormula;

    public static create(gradual: boolean, staticFormula: VerificationFormula): VerificationFormulaGradual
    {
        var res = new VerificationFormulaGradual();
        res.gradual = gradual;
        res.staticFormula = staticFormula;
        res.updateHTML();
        return res;
    }

    public constructor(
        source: string = "?"
    )
    {
        this.html = $("<span>");

        source = source.trim();
        this.gradual = false;
        if (source.charAt(0) == "?")
        {
            this.gradual = true;
            source = source.substr(1).trim().substr(1);
        }
        this.staticFormula = new VerificationFormula(source);
        this.updateHTML();
    }

    private updateHTML()
    {
        this.html.text("");
        var grad = $("<span>").text("?");
        if (!this.staticFormula.isEmpty())
            grad.append($("<span>").addClass("sepConj").text(" * "));
        if (this.gradual)
            this.html.append(grad);
        if (!this.gradual || !this.staticFormula.isEmpty())
            this.html.append(this.staticFormula.createHTML());
    }

    public createHTML(): JQuery
    {
        return this.html;
    }
    public sfrm(fp: FootprintStatic = []): boolean
    {
        return this.gradual || this.staticFormula.sfrm(fp);
    }
    public substs(m: (x: string) => string): VerificationFormulaGradual
    {
        var frm = new VerificationFormulaGradual();
        frm.gradual = this.gradual;
        frm.staticFormula = this.staticFormula.substs(m);
        return frm;
    }

    public satisfiable(): boolean
    {
        return this.staticFormula.satisfiable();
    }
    public norm(): VerificationFormulaGradual
    {
        return VerificationFormulaGradual.create(this.gradual, this.staticFormula.norm());
    }
    public woVar(x: string): VerificationFormulaGradual
    {
        return VerificationFormulaGradual.create(this.gradual, this.staticFormula.woVar(x));
    }
    public woAcc(e: Expression, f: string): VerificationFormulaGradual
    {
        return VerificationFormulaGradual.create(this.gradual, this.staticFormula.woAcc(e, f));
    }

    public impliesRuntime(phi: VerificationFormula): VerificationFormula
    {
        if (this.gradual)
        {
            // impossible by itself?
            if (!phi.satisfiable())
                return VerificationFormula.getFalse();
            
            var linearPart = <FormulaPartAcc[]>
                phi.parts.filter(p => p instanceof FormulaPartAcc);
            var classicalPart =
                phi.parts.filter(p => !(p instanceof FormulaPartAcc));
            // augment classical parts
            for (var i = 0; i < linearPart.length; ++i)
                for (var j = i + 1; j < linearPart.length; ++j)
                    if (linearPart[i].f == linearPart[j].f)
                        classicalPart.push(new FormulaPartNeq(linearPart[i].e, linearPart[j].e));
            
            // impossible to imply?
            if (!new VerificationFormula(null, this.staticFormula.parts.concat(classicalPart)).satisfiable())
                return VerificationFormula.getFalse();

            // simplify
            classicalPart = classicalPart.filter(x => 
                            !this.staticFormula.implies(new VerificationFormula(null, [x])));
            linearPart = linearPart.filter(x => 
                            !this.staticFormula.implies(new VerificationFormula(null, [x])));

            // not required if more sophisticated:
            // - create meet of A and B (structured disjunction)
            // - eliminate unsatisfiable
            // - simplify remaining
            // BUT: that makes runtime checks more expensive!
            return new VerificationFormula(null, classicalPart.concat(linearPart)).norm();
        }
        else
            return this.staticFormula.impliesRuntime(phi);
    }

    // may produce false negatives
    public impliesApprox(phi: VerificationFormula): boolean
    {
        if (this.gradual)
            return VerificationFormula.intersect(this.staticFormula, phi).satisfiable();
        else
            return this.staticFormula.implies(phi);
    }
}