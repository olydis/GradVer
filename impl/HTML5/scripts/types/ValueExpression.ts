import { VerificationFormula } from "./VerificationFormula";
import { Type } from "./Type";

export abstract class Value {
    public abstract equalTo(other: Value): boolean;

}

export class ValueObject extends Value {
    private static _uid: number = 0;
    public static reset(): void { ValueObject._uid = 0; }

    constructor(private uid: number = null) {
        super();
        if (uid === null)
            this.uid = ValueObject._uid++;
    }

    public equalTo(other: Value): boolean
    {
        return other instanceof ValueObject && this.uid == other.uid;
    }

    public get UID(): number { return this.uid; }

    public toString(): string {
        return "<" + this.uid + ">";
    }
}

export abstract class ValueExpression extends Value
{
    abstract toString(): string;
    abstract getType(): Type;

    public abstract equalTo(other: ValueExpression): boolean;

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
    public static getZero(): ValueExpression
    {
        return new ValueExpressionN(0);
    }
}

export class ValueExpressionN extends ValueExpression
{
    public constructor(private n: number) 
    { 
        super(); 
        if (n == null) throw "null arg";
        this.n = Math.round(this.n); 
    }

    public static parse(source: string): ValueExpression
    {
        var n = parseInt(source);
        return !isNaN(n)
            ? new ValueExpressionN(n)
            : null;
    }

    public equalTo(other: ValueExpression): boolean
    {
        return other instanceof ValueExpressionN && other.n == this.n;
    }

    public toString(): string
    {
        return this.n.toString();
    }
    public getType(): Type
    {
        return Type.getPrimitiveInt();
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

    public equalTo(other: ValueExpression): boolean
    {
        return other instanceof ValueExpressionNull;
    }

    public toString(): string
    {
        return "null";
    }
    public getType(): Type
    {
        return null;
    }
}