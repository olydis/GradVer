import { VerificationFormula } from "./VerificationFormula";
import { FootprintStatic } from "./FootprintStatic";

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

    // may produce false negatives
    public impliesApprox(phi: VerificationFormula): boolean
    {
        if (this.gradual)
            return VerificationFormula.intersect(this.staticFormula, phi).satisfiableApprox();
        else
            return this.staticFormula.impliesApprox(phi);
    }
    public impliesApproxMissing(phi: VerificationFormula): VerificationFormula
    {
        return this.staticFormula.impliesApproxMissing(phi);
    }
    public containsApprox(phi: VerificationFormula): boolean
    {
        if (!this.gradual)
            return VerificationFormula.eq(this.staticFormula, phi);
        // gradual
        if (!phi.satisfiableApprox())
            return false;
        if (!phi.sfrm([]))
            return false;
        return phi.impliesApprox(this.staticFormula);
    }
}