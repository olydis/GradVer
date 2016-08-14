import { Expression, ExpressionDot } from "./Expression";
import { ValueObject } from "./ValueExpression";
import { Type } from "./Type";
import { FootprintStatic, FootprintDynamic } from "./Footprint";

import { NormalizedEnv, EvalEnv } from "../runtime/EvalEnv";

export abstract class FormulaPart
{
    public abstract toString(): string;
    public abstract substs(m: (x: string) => string): FormulaPart;
    public footprintStatic(): FootprintStatic
    {
        return [];
    }
    public footprintDynamic(env: EvalEnv): FootprintDynamic
    {
        return [];
    }
    public abstract sfrm(fp: FootprintStatic): boolean;
    public abstract sfrmInv(): FootprintStatic;
    public abstract FV(): string[];
    public abstract envAdd(env: NormalizedEnv): NormalizedEnv;
    public envImpiledBy(env: NormalizedEnv): boolean { return this.eval(env.getEnv()); }
    public abstract eval(env: EvalEnv): boolean;

    static get subs(): any[]
    {
        return [
            FormulaPartAcc,
            FormulaPartTrue,
            FormulaPartNeq,
            FormulaPartEq,
        ];
    }
    public static parse(source: string): FormulaPart
    {
        source = source.replace(/\s/g, "");
        source = source.replace(/\(/g, "");
        source = source.replace(/\)/g, "");
        try
        {
            var result: FormulaPart = null;
            for (var sub of FormulaPart.subs)
            {
                if (result) break;
                result = sub.parse(source);
            }
            return result;
        }
        catch(e)
        {
            console.error("parse error");
            return new FormulaPartTrue();
        }
    }
    public static eq(p1: FormulaPart, p2: FormulaPart): boolean
    {
        for (var sub of FormulaPart.subs)
            if (p1 instanceof sub && p2 instanceof sub)
                return JSON.stringify(p1) == JSON.stringify(p2);
        return false;
    }

    public asFormula(): VerificationFormula
    {
        return new VerificationFormula(null, [this]);
    }
}

export class FormulaPartTrue extends FormulaPart
{
    public static parse(source: string): FormulaPart
    {
        return source.toLowerCase() == "true"
            ? new FormulaPartTrue()
            : null;
    }

    public toString(): string
    {
        return "true";
    }
    public substs(m: (x: string) => string): FormulaPart
    {
        return this;
    }
    public sfrm(fp: FootprintStatic): boolean
    {
        return true;
    }
    public sfrmInv(): FootprintStatic
    {
        return [];
    }
    public FV(): string[] { return []; }
    public envAdd(env: NormalizedEnv): NormalizedEnv { return env; }
    public eval(env: EvalEnv): boolean { return true; }
}

export class FormulaPartEq extends FormulaPart
{
    public constructor(
        private e1: Expression,
        private e2: Expression)
    {
        super();
        if (e1 == null) throw "null arg";
        if (e2 == null) throw "null arg";
    }

    public static parse(source: string): FormulaPart
    {
        var eqIndex = source.indexOf("=");
        if (eqIndex == -1) return null;

        var a = source.substr(0, eqIndex);
        var b = source.substr(eqIndex + 1).replace(/=/g, "");
        var ea = Expression.parse(a);
        var eb = Expression.parse(b);
        return ea != null && eb != null
            ? new FormulaPartEq(ea, eb)
            : null;
    }

    public toString(): string
    {
        return "(" + this.e1.toString() + " = " + this.e2.toString() + ")";
    }
    public substs(m: (x: string) => string): FormulaPart
    {
        return new FormulaPartEq(this.e1.substs(m), this.e2.substs(m));
    }
    public sfrm(fp: FootprintStatic): boolean
    {
        return this.e1.sfrm(fp)
            && this.e2.sfrm(fp);
    }
    public sfrmInv(): FootprintStatic
    {
        return this.e1.necessaryFraming().concat(this.e2.necessaryFraming());
    }
    public FV(): string[] { return this.e1.FV().concat(this.e2.FV()); }
    public envAdd(env: NormalizedEnv): NormalizedEnv { return env.addEq(this.e1, this.e2); }
    public eval(env: EvalEnv): boolean { 
        var v1 = this.e1.eval(env); 
        var v2 = this.e2.eval(env);
        return v1 != null && v2 != null && v1.equalTo(v2); 
    }
}

export class FormulaPartNeq extends FormulaPart
{
    public constructor(
        private e1: Expression,
        private e2: Expression)
    {
        super();
        if (e1 == null) throw "null arg";
        if (e2 == null) throw "null arg";
    }

    public static parse(source: string): FormulaPart
    {
        if (source == "false")
            return new FormulaPartNeq(Expression.getNull(), Expression.getNull());

        var eqIndex = source.indexOf("!=");
        if (eqIndex == -1) eqIndex = source.indexOf("<>");
        if (eqIndex == -1) eqIndex = source.indexOf("≠");
        if (eqIndex == -1) return null;

        var a = source.substr(0, eqIndex);
        var b = source.substr(eqIndex + 1).replace(/=/g, "").replace(/>/g, "");
        var ea = Expression.parse(a);
        var eb = Expression.parse(b);
        return ea != null && eb != null
            ? new FormulaPartNeq(ea, eb)
            : null;
    }

    public toString(): string
    {
        var e1 = this.e1.toString();
        var e2 = this.e2.toString();
        if (e1 == e2 && e1 == "null")
            return "false";
        return "(" + e1 + " ≠ " + e2 + ")";
    }
    public substs(m: (x: string) => string): FormulaPart
    {
        return new FormulaPartNeq(this.e1.substs(m), this.e2.substs(m));
    }
    public sfrm(fp: FootprintStatic): boolean
    {
        return this.e1.sfrm(fp)
            && this.e2.sfrm(fp);
    }
    public sfrmInv(): FootprintStatic
    {
        return this.e1.necessaryFraming().concat(this.e2.necessaryFraming());
    }
    public FV(): string[] { return this.e1.FV().concat(this.e2.FV()); }
    public envAdd(env: NormalizedEnv): NormalizedEnv { return env.addIneq(this.e1, this.e2); }
    public envImpiledBy(env: NormalizedEnv): boolean {

        if (!super.envImpiledBy(env))
            return false;
        return env.addEq(this.e1, this.e2) == null;
    }
    public eval(env: EvalEnv): boolean { 
        var v1 = this.e1.eval(env); 
        var v2 = this.e2.eval(env);
        return v1 != null && v2 != null && !v1.equalTo(v2); 
    }
}

export class FormulaPartAcc extends FormulaPart
{
    public constructor(
        public e: Expression,
        public f: string)
    {
        super();
        if (e == null) throw "null arg";
        if (!Expression.isValidX(f)) throw "null arg";
    }

    public static parse(source: string): FormulaPart
    {
        if (source.substr(0, 3) != "acc") return null;
        source = source.substr(3);

        var dotIndex = source.lastIndexOf(".");
        if (dotIndex == -1) dotIndex = source.lastIndexOf(",");
        if (dotIndex == -1)
            return null;
        var e = Expression.parse(source.substr(0, dotIndex));
        var f = source.substr(dotIndex + 1);
        return e != null
            ? new FormulaPartAcc(e, f)
            : null;
    }

    public toString(): string
    {
        return "acc(" + this.e.toString() + "." + this.f + ")";
    }
    public substs(m: (x: string) => string): FormulaPart
    {
        return new FormulaPartAcc(this.e.substs(m), this.f);
    }
    public footprintStatic(): FootprintStatic
    {
        return [{ e: this.e, f: this.f }];
    }
    public footprintDynamic(env: EvalEnv): FootprintDynamic
    {
        var v = this.e.eval(env);
        if (v instanceof ValueObject)
            return [{ o: v.UID, f: this.f }];
        return [];
    }
    public sfrm(fp: FootprintStatic): boolean
    {
        return this.e.sfrm(fp);
    }
    public sfrmInv(): FootprintStatic
    {
        return this.e.necessaryFraming();
    }
    public FV(): string[] { return this.e.FV(); }
    public envAdd(env: NormalizedEnv): NormalizedEnv { return env.addAcc(this.e, this.f); }
    public eval(env: EvalEnv): boolean { 
        var v = this.e.eval(env);
        if (v instanceof ValueObject)
            return env.A.some(a => a.o == v.UID && a.f == this.f);
        return false; 
    }
}

export class VerificationFormula
{
    public static getFalse(): VerificationFormula
    {
        return new VerificationFormula(null, [new FormulaPartNeq(Expression.getNull(), Expression.getNull())]);
    }
    public static empty(): VerificationFormula
    {
        return new VerificationFormula(null, []);
    }
    public static intersect(p1: VerificationFormula, p2: VerificationFormula): VerificationFormula
    {
        var parts = p1.parts.slice();
        parts.push(...p2.parts.filter(x => !parts.some(y => FormulaPart.eq(x, y))));
        parts = parts.filter(p => !(p instanceof FormulaPartTrue));
        return new VerificationFormula(null, parts);
    }
    public static eq(p1: VerificationFormula, p2: VerificationFormula): boolean
    {
        if (p1.parts.length != p2.parts.length)
            return false;
        return p1.parts.every((p, i) => FormulaPart.eq(p, p2.parts[i]));
    }

    public constructor(
        source: string = null,
        public parts: FormulaPart[] = []
    )
    {
        if (source)
        {
            this.parts = [];
            source = source.trim();
            if (source != "")
                this.parts = source.split("*").map(FormulaPart.parse).filter(part => part != null);
        }
    }

    public isEmpty(): boolean
    {
        return this.parts.length == 0;
    }

    public toString(): string
    {
        var parts = this.isEmpty() ? [new FormulaPartTrue()] : this.parts;
        return parts.join(" * ");
    }
    public substs(m: (x: string) => string): VerificationFormula
    {
        var frm = new VerificationFormula();
        frm.parts = this.parts.map(part => part.substs(m));
        return frm;
    }
    public sfrm(fp: FootprintStatic = []): boolean
    {
        for (var part of this.parts)
        {
            if (!part.sfrm(fp))
                return false;
            fp.push(...part.footprintStatic());
        }
        return true;
    }
    public footprintStatic(): FootprintStatic
    {
        var res: FootprintStatic = [];
        this.parts.forEach(p => res.push(...p.footprintStatic()));
        return res;
    }
    public footprintDynamic(env: EvalEnv): FootprintDynamic
    {
        var res: FootprintDynamic = [];
        this.parts.forEach(p => res.push(...p.footprintDynamic(env)));
        return res;
    }
    public eval(env: EvalEnv): boolean
    {
        if (!this.parts.every(p => p.eval(env)))
            return false;
        var fp = this.footprintDynamic(env);
        // nodup
        var a: FootprintDynamic = [];
        for (var x of fp)
        {
            if (a.some(y => y.f == x.f && y.o == x.o))
                return false;
            a.push(x);
        }
        return true;
    }

    public autoFraming(): FormulaPartAcc[]
    {
        var framing: FootprintStatic = [];
        for (var part of this.snorm().parts)
            framing.push(...part.sfrmInv());
        var framingFrm = framing.map(x => new FormulaPartAcc(x.e, x.f));
        var partsAcc : FormulaPartAcc[] = [];
        for (var acc of framingFrm)
            if (partsAcc.every(x => !FormulaPart.eq(acc, x)))
                partsAcc.push(acc);
        return partsAcc;
    }

    public autoFramedChecks(knowns: VerificationFormula[]): VerificationFormula[]
    {
        var parts = this.snorm().parts;

        // add framing
        var partsAcc = this.autoFraming();

        // simpl classical
        parts = parts.filter(x => partsAcc.every(y => 
                                        new VerificationFormula(null, [y]).implies(
                                        new VerificationFormula(null, [x])) == null));

        for (var known of knowns)
            parts = parts.filter(x => known.implies(new VerificationFormula(null, [x])) == null);

        // simpl framing
        for (var known of knowns)
            partsAcc = partsAcc.filter(x => new VerificationFormula(null, known.parts.concat(parts)).implies(
                                            new VerificationFormula(null, [x])) == null);

        return parts.concat(partsAcc).map(x => new VerificationFormula(null, [x]));
    }
    
    public envImpliedBy(env: NormalizedEnv): boolean
    {
        if (env == null)
            return true;
        if (!this.parts.every(p => p.envImpiledBy(env)))
            return false;
        return this.eval(env.getEnv());
    }
    public FV(): string[] 
    {
        return this.parts.reduce((a, b) => a.concat(b.FV()), []);
    }
    public createNormalizedEnv(): NormalizedEnv
    {
        var env = NormalizedEnv.create();
        for (var part of this.parts)
            env = env ? part.envAdd(env) : null;
        return env;
    }
    public satisfiable(): boolean
    {
        return this.createNormalizedEnv() != null;
    }
    // partial function "imp" of PDF!
    public implies(phi: VerificationFormula): VerificationFormula
    {
        return phi.envImpliedBy(this.createNormalizedEnv())
            ? this
            : null;
    }

    public impliedEqualities(): FormulaPartEq[]
    {
        var nenv = this.createNormalizedEnv();
        return nenv == null
            ? null
            : nenv.impliedEqualities().map(x => new FormulaPartEq(x.e1, x.e2));
    }

    public impliedInequalities(): FormulaPartNeq[]
    {
        var nenv = this.createNormalizedEnv();
        return nenv == null
            ? null
            : nenv.impliedInequalities().map(x => new FormulaPartNeq(x.e1, x.e2));
    }

    public norm(): VerificationFormula
    {
        var nenv = this.createNormalizedEnv();
        return nenv == null
            ? VerificationFormula.getFalse()
            : nenv.createFormula();
    }
    public snorm(): VerificationFormula
    {
        var linearPart = <FormulaPartAcc[]>
            this.parts.filter(p => p instanceof FormulaPartAcc);
        var classicalPart =
            this.parts.filter(p => !(p instanceof FormulaPartAcc));
        // augment classical parts
        for (var i = 0; i < linearPart.length; ++i)
        {
            for (var j = i + 1; j < linearPart.length; ++j)
                if (linearPart[i].f == linearPart[j].f)
                    classicalPart.push(new FormulaPartNeq(linearPart[i].e, linearPart[j].e));
            var pivot = new ExpressionDot(linearPart[i].e, linearPart[i].f);
            classicalPart.push(new FormulaPartEq(pivot, pivot));
        }
        return new VerificationFormula(null, classicalPart).norm();
    }
    public woVar(x: string): VerificationFormula
    {
        var nenv = this.createNormalizedEnv();
        return nenv == null
            ? VerificationFormula.getFalse()
            : nenv.woVar(x).createFormula();
    }
    public woAcc(e: Expression, f: string): VerificationFormula
    {
        var nenv = this.createNormalizedEnv();
        return nenv == null
            ? VerificationFormula.getFalse()
            : nenv.woAcc(e, f).createFormula();
    }
    public append(part: FormulaPart): VerificationFormula
    {
        var env = this.createNormalizedEnv();
        if (env != null)
            env = part.envAdd(env);
        if (part instanceof FormulaPartAcc)
        {
            var f = part.f;
            for (var fx of this.autoFraming())
                if (fx.f == f && env != null)
                    env = new FormulaPartNeq(fx.e, part.e).envAdd(env);
        }
        return env == null
            ? VerificationFormula.getFalse()
            : env.createFormula();
    }
}