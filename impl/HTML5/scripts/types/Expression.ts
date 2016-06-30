import { VerificationFormula } from "./VerificationFormula";
import { ValueExpression } from "./ValueExpression";
import { FootprintStatic } from "./FootprintStatic";

export abstract class Expression
{
    public createHTML(): JQuery
    {
        return $("<span>").text(this.toString());
    }
    public abstract substs(m: (x: string) => string): Expression;
    public subste(a: Expression, b: Expression): Expression
    {
        if (Expression.eq(a, this))
            return b;
        else
            return this;
    }
    public abstract sfrm(fp: FootprintStatic): boolean;
    public abstract toString(): string;
    public abstract depth(): number;

    public static eq(e1: Expression, e2: Expression): boolean
    {
        return e1.toString() == e2.toString();
    }

    public static parse(source: string): Expression
    {
        source = source.replace(/\s/g, "");
        var result: Expression = null;
        if (!result) result = ExpressionDot.parse(source);
        if (!result) result = ExpressionV.parse(source);
        if (!result) result = ExpressionX.parse(source);
        return result;
    }

    public static isValidX(source: string): boolean
    {
        if (source == null) return false;
        return source.search(/^[A-Za-z]+$/) == 0;
    }

    public static getNull(): Expression
    {
        return new ExpressionV(ValueExpression.getNull());
    }
}

export class ExpressionV extends Expression
{
    public constructor(private v: ValueExpression)
    {
        super();
        if (v == null) throw "null arg";
    }

    public static parse(source: string): Expression
    {
        var vex = ValueExpression.parse(source);
        return vex != null
            ? new ExpressionV(vex)
            : null;
    }

    public toString(): string
    {
        return this.v.createHTML().text();
    }

    public substs(m: (x: string) => string): Expression
    {
        return this;
    }
    public sfrm(fp: FootprintStatic): boolean
    {
        return true;
    }
    public depth(): number
    {
        return 0;
    }
}

export class ExpressionX extends Expression
{
    public constructor(private x: string)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
    }

    public static parse(source: string): Expression
    {
        return source != ""
            ? new ExpressionX(source)
            : null;
    }

    public toString(): string
    {
        return this.x;
    }

    public substs(m: (x: string) => string): Expression
    {
        return new ExpressionX(m(this.x));
    }
    public sfrm(fp: FootprintStatic): boolean
    {
        return true;
    }
    public depth(): number
    {
        return 1;
    }
}

export class ExpressionDot extends Expression
{
    public constructor(
        private e: Expression,
        private f: string)
    {
        super();
        if (e == null) throw "null arg";
        if (!Expression.isValidX(f)) throw "null arg";
    }

    public static parse(source: string): Expression
    {
        var dotIndex = source.lastIndexOf(".");
        if (dotIndex == -1)
            return null;
        var e = Expression.parse(source.substr(0, dotIndex));
        var f = source.substr(dotIndex + 1);
        return e != null
            ? new ExpressionDot(e, f)
            : null;
    }

    public toString(): string
    {
        return this.e.toString() + "." + this.f;
    }

    public substs(m: (x: string) => string): Expression
    {
        return new ExpressionDot(this.e.substs(m), this.f);
    }
    public sfrm(fp: FootprintStatic): boolean
    {
        return this.e.sfrm(fp)
            && fp.some(fpx => Expression.eq(this.e, fpx.e) && this.f == fpx.f);
    }
    public depth(): number
    {
        return 1 + this.e.depth();
    }
    public subste(a: Expression, b: Expression): Expression
    {
        var ex = this.e.subste(a, b);
        var thisx = new ExpressionDot(ex, this.f);
        if (Expression.eq(a, thisx))
            return b;
        else
            return thisx;
    }
}