import { Expression, ExpressionV } from "./Expression";

export abstract class Type
{
    abstract createHTML(): JQuery;
    abstract defaultValue(): Expression;
    abstract compatibleWith(other: Type): boolean;
    public toString(): string
    {
        return this.createHTML().text();
    }

    public static parse(source: string): Type
    {
        source = source.replace(/\s/g, "");
        var result: Type = null;
        if (!result) result = TypePrimitiveInt.parse(source);
        if (!result) result = TypeClass.parse(source);
        return result;
    }

    public static getPrimitiveInt(): Type
    {
        return new TypePrimitiveInt();
    }
    public static intersect(t1: Type, t2: Type): { t: Type, impossible: boolean }
    {
        var resImpossible: { t: Type, impossible: boolean } = { t: null, impossible: true };

        var t1Primitive = !(t1 instanceof TypeClass) && t1 != null;
        var t2Primitive = !(t2 instanceof TypeClass) && t2 != null;
        // compatible primitiveness?
        if (t1Primitive != t2Primitive)
            return resImpossible;
        // class wildcard case (note that we then also KNOW that the other thing is a class)
        if (t1 == null)
            return { t: t2, impossible: false };
        if (t2 == null)
            return { t: t1, impossible: false };
        // types compatible? works for primitive and class
        return t1.toString() == t2.toString() ? { t: t1, impossible: false } : resImpossible;
    }
    public static implies(t1: Type, t2: Type): boolean
    {
        if (t1 == t2)
            return true; // also covers nulls!
        var t1Primitive = !(t1 instanceof TypeClass) && t1 != null;
        var t2Primitive = !(t2 instanceof TypeClass) && t2 != null;
        // compatible primitiveness?
        if (t1Primitive != t2Primitive)
            return false;
        // class wildcard case (note that we then also KNOW that the other thing is a class)
        if (t1 == null)
            return false;
        if (t2 == null)
            return true;
        // types compatible? works for primitive and class
        return t1.toString() == t2.toString();
    }
    public static eq(t1: Type, t2: Type): boolean
    {
        return Type.implies(t1, t2) && Type.implies(t2, t1);
    }
}

export class TypePrimitiveInt extends Type
{
    public static parse(source: string): Type
    {
        return source.toLocaleLowerCase() == "int"
            ? new TypePrimitiveInt()
            : null;
    }

    public createHTML(): JQuery
    {
        return $("<span>").text("int");
    }
    public defaultValue(): Expression
    {
        return Expression.getZero();
    }
    public compatibleWith(other: Type): boolean
    {
        return other instanceof TypePrimitiveInt;
    }
}

export class TypeClass extends Type
{
    public constructor(public C: string) 
    { 
        super();
        if (!Expression.isValidX(C)) throw "null arg";
    }

    public static parse(source: string): Type
    {
        if (source == "") return null;
        return new TypeClass(source);
    }

    public createHTML(): JQuery
    {
        return $("<span>").text(this.C);
    }
    public defaultValue(): Expression
    {
        return Expression.getNull();
    }
    public compatibleWith(other: Type): boolean
    {
        return other === null || (other instanceof TypeClass && other.C == this.C);
    }
}