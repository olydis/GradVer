import { Expression } from "./Expression";
import { ValueObject } from "./ValueExpression";
import { Type } from "./Type";
import { FootprintStatic, FootprintDynamic } from "./Footprint";

import { NormalizedEnv, EvalEnv } from "../runtime/EvalEnv";

export abstract class FormulaPart
{
    public abstract createHTML(): JQuery;
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
        var result: FormulaPart = null;
        for (var sub of FormulaPart.subs)
        {
            if (result) break;
            result = sub.parse(source);
        }
        return result;
    }
    public static eq(p1: FormulaPart, p2: FormulaPart): boolean
    {
        for (var sub of FormulaPart.subs)
            if (p1 instanceof sub && p2 instanceof sub)
                return JSON.stringify(p1) == JSON.stringify(p2);
        return false;
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

    public createHTML(): JQuery
    {
        return $("<span>").text("true");
    }
    public substs(m: (x: string) => string): FormulaPart
    {
        return this;
    }
    public sfrm(fp: FootprintStatic): boolean
    {
        return true;
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

    public createHTML(): JQuery
    {
        return $("<span>")
            .append($("<span>").text("("))
            .append(this.e1.createHTML())
            .append($("<span>").text(" = "))
            .append(this.e2.createHTML())
            .append($("<span>").text(")"));
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

    public createHTML(): JQuery
    {
        return $("<span>")
            .append($("<span>").text("("))
            .append(this.e1.createHTML())
            .append($("<span>").text(" ≠ "))
            .append(this.e2.createHTML())
            .append($("<span>").text(")"));
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
        private e: Expression,
        private f: string)
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

    public createHTML(): JQuery
    {
        return $("<span>")
            .append($("<span>").text("acc("))
            .append(this.e.createHTML())
            .append($("<span>").text("." + this.f))
            .append($("<span>").text(")"));
    }
    public substs(m: (x: string) => string): FormulaPart
    {
        return new FormulaPartAcc(this.e.substs(m), this.f);
    }
    public footprintStatic(): FootprintStatic
    {
        return [{ e: this.e, f: this.f }];
    }
    public FootprintDynamic(env: EvalEnv): FootprintDynamic
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

    private html: JQuery;

    public constructor(
        source: string = null,
        public parts: FormulaPart[] = []
    )
    {
        this.html = $("<span>");

        if (source)
        {
            this.parts = [];
            source = source.trim();
            if (source != "")
                this.parts = source.split("*").map(FormulaPart.parse).filter(part => part != null);
        }
        this.updateHTML();
    }

    public isEmpty(): boolean
    {
        return this.parts.length == 0;
    }

    private updateHTML()
    {
        var parts = this.isEmpty() ? [new FormulaPartTrue()] : this.parts;
        this.html.text("");
        for (var i = 0; i < parts.length; ++i)
        {
            if (i > 0)
                this.html.append($("<span>").addClass("sepConj").text(" * "));
            this.html.append(parts[i].createHTML());
        }
    }

    public createHTML(): JQuery
    {
        return this.html;
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
    public implies(phi: VerificationFormula)
    {
        return phi.envImpliedBy(this.createNormalizedEnv());
    }
    public norm(): VerificationFormula
    {
        var nenv = this.createNormalizedEnv();
        return nenv == null
            ? VerificationFormula.getFalse()
            : nenv.createFormula();
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
}