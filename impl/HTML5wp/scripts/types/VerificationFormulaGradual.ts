import { VerificationFormula, FormulaPartAcc, FormulaPartNeq, FormulaPartEq, FormulaPart } from "./VerificationFormula";
import { FootprintStatic } from "./Footprint";
import { Expression, ExpressionDot } from "./Expression";
import { EvalEnv, NormalizedEnv } from "../runtime/EvalEnv";

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

    public static supremum(a: VerificationFormulaGradual, b: VerificationFormulaGradual): VerificationFormulaGradual | null
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

    public static infimum(a: VerificationFormulaGradual, b: VerificationFormulaGradual): VerificationFormulaGradual | null
    {
        if (!a.gradual && !b.gradual)
            if (a.staticFormula.implies(b.staticFormula) && b.staticFormula.implies(a.staticFormula))
                return a;
            else
                return null;
        if (!a.gradual)
            if (a.staticFormula.implies(b.staticFormula))
                return a;
            else
                return null;
        if (!b.gradual)
            if (b.staticFormula.implies(a.staticFormula))
                return b;
            else
                return null;

        return VerificationFormulaGradual.create(true, new VerificationFormula(null, a.staticFormula.snorm().parts.concat(b.staticFormula.snorm().parts)).snorm());
    }

    public static nonSepAnd(a: VerificationFormulaGradual, b: VerificationFormulaGradual): VerificationFormulaGradual | null
    {
        if (!a.gradual && !b.gradual)
        {
            var nsa = VerificationFormula.nonSepAnd(a.staticFormula, b.staticFormula);
            return nsa == null ? null : VerificationFormulaGradual.create(false, nsa);
        }
        return VerificationFormulaGradual.create(true, new VerificationFormula(null, a.staticFormula.snorm().parts.concat(b.staticFormula.snorm().parts)).snorm());
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
    public subste(a: Expression, b: Expression): VerificationFormulaGradual
    {
        var frm = new VerificationFormulaGradual();
        frm.gradual = this.gradual;
        frm.staticFormula = this.staticFormula.subste(a, b);
        return frm;
    }

    public createNormalizedEnv(): NormalizedEnv
    {
        var env = this.staticFormula.createNormalizedEnv() as NormalizedEnv;
        for (var acc of this.staticFormula.autoFraming())
            env = acc.envAdd(env) || env;
        return env;
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

    public implies(phi: VerificationFormula): VerificationFormulaGradual | null
    {
        if (this.gradual)
        {
            var staticIntersection: FormulaPart[] = this.staticFormula.snorm().parts
                                            .concat(phi.snorm().parts);
                        
            // implication fails statically?
            var res = new VerificationFormula(null, staticIntersection);
            if (!res.satisfiable())
                return null;

            // simplify
            return VerificationFormulaGradual.create(true, res.norm());
        }
        else
        {
            var sf = this.staticFormula.implies(phi);
            if (sf == null)
                return null;
            return VerificationFormulaGradual.create(false, sf);
        }
    }

    public impliesRemaindors(phi: VerificationFormula): VerificationFormula[]
    {
        var condClassic = this.staticFormula.snorm();
        var condx = this.staticFormula
            .autoFraming()
            .map(x => new VerificationFormula(null, (<FormulaPart[]>[x]).concat(condClassic.parts)));
        condx.push(this.staticFormula);
        return phi.autoFramedChecks(condx);
    }

    public impliesFully(phi: VerificationFormula): boolean
    {
        var rem = this.impliesRemaindors(phi);
        return rem.length == 0;
    }

    public eval(env: EvalEnv): boolean
    {
        var frm = this.staticFormula.autoFraming();
        if (!this.staticFormula.eval(env))
            return false;
        return frm.every(acc => acc.eval(env));
    }

    public static eq(a: VerificationFormulaGradual, b: VerificationFormulaGradual): boolean
    {
        return JSON.stringify(a) == JSON.stringify(b);
    }
    public static qm(): VerificationFormulaGradual
    {
        return VerificationFormulaGradual.create(true, VerificationFormula.empty());
    }
}