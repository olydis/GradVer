import { VerificationFormula } from "./VerificationFormula";

export abstract class ValueExpression
{
    abstract createHTML(): JQuery;

    public static parse(source: string): ValueExpression
    {
        source = source.replace(/\s/g, "");
        var result: ValueExpression = null;
        if (!result) result = ValueExpressionNull.parse(source);
        if (!result) result = ValueExpressionN.parse(source);
        return result;
    }

    public static getNull(): ValueExpression
    {
        return new ValueExpressionNull();
    }
}

export class ValueExpressionN extends ValueExpression
{
    public constructor(private n: number) 
    { 
        super(); 
        if (n == null) throw "null arg";
        this.n = Math.max(0, Math.round(this.n)); 
    }

    public static parse(source: string): ValueExpression
    {
        var n = parseInt(source);
        return !isNaN(n)
            ? new ValueExpressionN(n)
            : null;
    }

    public createHTML(): JQuery
    {
        return $("<span>").text(this.n.toString());
    }
}

export class ValueExpressionNull extends ValueExpression
{
    public static parse(source: string): ValueExpression
    {
        return source.toLocaleLowerCase() == "null"
            ? new ValueExpressionNull()
            : null;
    }

    public createHTML(): JQuery
    {
        return $("<span>").text("null");
    }
}