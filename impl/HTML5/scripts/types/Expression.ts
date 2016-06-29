import { VerificationFormula } from "./VerificationFormula";
import { ValueExpression } from "./ValueExpression";

export abstract class Expression
{
    abstract createHTML(): JQuery;

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

    public createHTML(): JQuery
    {
        return this.v.createHTML();
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

    public createHTML(): JQuery
    {
        return $("<span>").text(this.x);
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

    public createHTML(): JQuery
    {
        return $("<span>")
            .append(this.e.createHTML())
            .append($("<span>").text("." + this.f));
    }
}