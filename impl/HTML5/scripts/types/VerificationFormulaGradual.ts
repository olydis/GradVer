import { VerificationFormula, FormulaPartAcc, FormulaPartNeq, FormulaPartEq, FormulaPart } from "./VerificationFormula";
import { FootprintStatic } from "./Footprint";
import { Expression, ExpressionDot } from "./Expression";
import { EvalEnv } from "../runtime/EvalEnv";

export class VerificationFormulaGradual
{
    public gradual: boolean;
    public staticFormula: VerificationFormula;

    public static create(gradual: boolean, staticFormula: VerificationFormula): VerificationFormulaGradual
    {
        var res = new VerificationFormulaGradual();
        res.gradual = gradual;
        res.staticFormula = staticFormula;
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
        source = source.trim();
        this.gradual = false;
        if (source.charAt(0) == "?")
        {
            this.gradual = true;
            source = source.substr(1).trim().substr(1);
        }
        this.staticFormula = new VerificationFormula(source);
    }

    public toString(): string
    {
        if (this.staticFormula.isEmpty() && this.gradual)
            return "?";
        return (this.gradual ? "? * " : "") + this.staticFormula.toString();
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

    public eval(env: EvalEnv): boolean
    {
        var frm = this.staticFormula.autoFraming();
        if (!this.staticFormula.eval(env))
            return false;
        return frm.every(acc => acc.eval(env));
    }
}