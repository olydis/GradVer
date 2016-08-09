import { VerificationFormula, FormulaPartAcc, FormulaPartNeq, FormulaPartEq, FormulaPart } from "./VerificationFormula";
import { FootprintStatic } from "./Footprint";
import { Expression, ExpressionDot } from "./Expression";

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

    public static supremum(a: VerificationFormulaGradual, b: VerificationFormulaGradual): VerificationFormulaGradual
    {
        if (!a.gradual || !b.gradual)
            return null;

        var sA = a.norm().staticFormula;
        var sB = b.norm().staticFormula;

        var parts: FormulaPart[] = [];
        for (var eq of sA.impliedEqualities().concat(sB.impliedEqualities()))
        {
            var part = new VerificationFormula(null, [eq]);
            if (sB.implies(part) && sA.implies(part))
                parts.push(eq);
        }
        for (var neq of sA.impliedInequalities().concat(sB.impliedInequalities()))
        {
            var part = new VerificationFormula(null, [neq]);
            if (sB.implies(part) && sA.implies(part))
                parts.push(neq);
        }
        var res = VerificationFormulaGradual.create(true, new VerificationFormula(null, parts));
        return res.norm();
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
        var res = VerificationFormulaGradual.create(this.gradual, this.staticFormula.norm());
        // gradual post-normalization
        if (this.gradual)
            res = VerificationFormulaGradual.create(true, this.staticFormula.snorm());
        return res;
    }
    public woVar(x: string): VerificationFormulaGradual
    {
        return VerificationFormulaGradual.create(this.gradual, this.staticFormula.woVar(x));
    }
    public woAcc(e: Expression, f: string): VerificationFormulaGradual
    {
        return VerificationFormulaGradual.create(this.gradual, this.staticFormula.woAcc(e, f));
    }
    public append(part: FormulaPart): VerificationFormulaGradual
    { // TODO: doesn't fail in double acc case... but with hoare rules that cannot occur...
        return VerificationFormulaGradual.create(this.gradual, this.staticFormula.append(part));
    }

    public implies(phi: VerificationFormula): VerificationFormulaGradual
    {
        if (this.gradual)
        {
            var staticIntersection: FormulaPart[] = this.staticFormula.snorm().parts
                                            .concat(phi.snorm().parts);
                        
            // implication fails statically?
            var res = new VerificationFormula(null, staticIntersection).norm();
            if (!res.satisfiable())
                return null;

            // simplify
            return VerificationFormulaGradual.create(true, res);
        }
        else
        {
            var sf = this.staticFormula.implies(phi);
            if (sf == null)
                return null;
            return VerificationFormulaGradual.create(false, sf);
        }
    }

    // MUST return false if implication impossible (for hoare rules to be gradual lifting!)
    // on the otherhand, witnesses don't need to be optimal
    public impliesRuntime(phi: VerificationFormula): VerificationFormula
    {
        var res = this.implies(phi);
        return res == null
            ? VerificationFormula.getFalse()
            : res.staticFormula.simplifyAssuming(this.staticFormula);
    }
}