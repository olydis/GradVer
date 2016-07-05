import { Expression } from "./Expression";
import { Type } from "./Type";
import { FootprintStatic } from "./FootprintStatic";
import { VerificationFormulaData } from "./VerificationFormulaData";
import { vfdTrue, vfdNormalize, vfdImpliesApprox } from "./VerificationFormulaDataServices";

export abstract class FormulaPart
{
    public abstract createHTML(): JQuery;
    public abstract substs(m: (x: string) => string): FormulaPart;
    public footprintStatic(): FootprintStatic
    {
        return [];
    }
    public abstract sfrm(fp: FootprintStatic): boolean;
    public abstract collectData(data: VerificationFormulaData): void;
    public abstract FV(): string[];

    static get subs(): any[]
    {
        return [
        	FormulaPartType,
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
    public collectData(data: VerificationFormulaData): void
    {
    }
    public FV(): string[] { return []; }
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
    public collectData(data: VerificationFormulaData): void
    {
        data.equalities.push({e1: this.e1, e2: this.e2});
    }
    public FV(): string[] { return this.e1.FV().concat(this.e2.FV()); }
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
    public collectData(data: VerificationFormulaData): void
    {
        data.inEqualities.push({e1: this.e1, e2: this.e2});
    }
    public FV(): string[] { return this.e1.FV().concat(this.e2.FV()); }
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
    public sfrm(fp: FootprintStatic): boolean
    {
        return this.e.sfrm(fp);
    }
    public collectData(data: VerificationFormulaData): void
    {
        data.access.push({e: this.e, f: this.f});
    }
    public FV(): string[] { return this.e.FV(); }
}

export class FormulaPartType extends FormulaPart
{
    public constructor(
        private x: string,
        private T: Type)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
    }

    public static parse(source: string): FormulaPart
    {
        var dotIndex = source.lastIndexOf(":");
        if (dotIndex == -1)
            return null;
        var x = source.substr(0, dotIndex);
        var T = source.substr(dotIndex + 1);
        var TT = Type.parse(T);
        if (TT == null)
            return null;
        return new FormulaPartType(x, TT);
    }

    public createHTML(): JQuery
    {
        return $("<span>")
            .append($("<span>").text("("))
            .append($("<span>").text(this.x))
            .append($("<span>").text(" : "))
            .append(this.T.createHTML())
            .append($("<span>").text(")"));
    }
    public substs(m: (x: string) => string): FormulaPart
    {
        return new FormulaPartType(m(this.x), this.T);
    }
    public sfrm(fp: FootprintStatic): boolean
    {
        return true;
    }
    public collectData(data: VerificationFormulaData): void
    {
        data.types.push({x: this.x, T: this.T});
    }
    public FV(): string[] { return [this.x]; }
}

export class VerificationFormula
{
    public static empty(): VerificationFormula
    {
        return new VerificationFormula(null, []);
    }
    public static intersect(p1: VerificationFormula, p2: VerificationFormula): VerificationFormula
    {
        var parts = p1.parts;
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
    public collectData(): VerificationFormulaData
    {
        var data: VerificationFormulaData = vfdTrue();
        for (var part of this.parts)
            part.collectData(data);
        return vfdNormalize(data);
    }
    public FV(): string[] 
    {
        return this.parts.reduce((a, b) => a.concat(b.FV()), []);
    }

    // conservative: might not find type, but WILL, if x:T exists
    public tryGetType(x : string): Type
    {
        var data = this.collectData();
        if (data.knownToBeFalse) return null;
        var type = data.types.filter(y => y.x == x);
        return type.length == 1 ? type[0].T : null;
    }

    // may produce false negatives
    public impliesApprox(phi: VerificationFormula)
    {
        return vfdImpliesApprox(this.collectData(), phi.collectData());
    }
}