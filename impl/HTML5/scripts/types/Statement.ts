import { VerificationFormula } from "./VerificationFormula";
import { Type } from "./Type";
import { Expression } from "./Expression";

export abstract class Statement
{
    abstract createHTML(): JQuery;

    public static parse(source: string): Statement
    {
        var result: Statement = null;
        source = source.replace(/;$/, "");
        var sourceWS = source;
        source = source.replace(/\s/g, "");
        try
        {
            if (!result) result = StatementCall.parse(source);
            if (!result) result = StatementAlloc.parse(source);
            if (!result) result = StatementAssert.parse(source);
            if (!result) result = StatementRelease.parse(source);
            if (!result) result = StatementMemberSet.parse(source);
            if (!result) result = StatementAssign.parse(source);
            if (!result) result = StatementDeclare.parse(sourceWS);
        }
        catch(e)
        {
            console.error("parse error");
            result = Statement.getNop();
        }
        return result;
    }

    public static getNop(): Statement
    {
        return new StatementAssert(new VerificationFormula());
    }
}

export class StatementMemberSet extends Statement
{
    public constructor(
        public x: string,
        public f: string,
        public y: string)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
        if (!Expression.isValidX(f)) throw "null arg";
        if (!Expression.isValidX(y)) throw "null arg";
    }

    public static parse(source: string): Statement
    {
        var eqIndex = source.indexOf(":=");
        if (eqIndex == -1) eqIndex = source.indexOf("=");
        if (eqIndex == -1) return null;

        var a = source.substr(0, eqIndex);
        var b = source.substr(eqIndex + 1).replace(/=/g, "");

        var dotIndex = a.lastIndexOf(".");
        if (dotIndex == -1)
            return null;
        var x = a.substr(0, dotIndex);
        var f = a.substr(dotIndex + 1);

        return new StatementMemberSet(x, f, b);
    }

    public createHTML(): JQuery
    {
        return $("<span>")
            .append(this.x + "." + this.f)
            .append($("<span>").text(" := "))
            .append(this.y)
            .append($("<span>").text(";"));
    }
}

export class StatementAssign extends Statement
{
    public constructor(
        public x: string,
        public e: Expression)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
        if (e == null) throw "null arg";
    }

    public static parse(source: string): Statement
    {
        var eqIndex = source.indexOf(":=");
        if (eqIndex == -1) eqIndex = source.indexOf("=");
        if (eqIndex == -1) return null;

        var a = source.substr(0, eqIndex);
        var b = source.substr(eqIndex + 1).replace(/=/g, "");

        var e = Expression.parse(b);

        return e != null
            ? new StatementAssign(a, e)
            : null;
    }

    public createHTML(): JQuery
    {
        return $("<span>")
            .append(this.x)
            .append($("<span>").text(" := "))
            .append(this.e.createHTML())
            .append($("<span>").text(";"));
    }
}

export class StatementAlloc extends Statement
{
    public constructor(
        public x: string,
        public C: string)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
        if (!Expression.isValidX(C)) throw "null arg";
    }

    public static parse(source: string): Statement
    {
        var eqIndex = source.indexOf(":=");
        if (eqIndex == -1) eqIndex = source.indexOf("=");
        if (eqIndex == -1) return null;

        var a = source.substr(0, eqIndex);
        var b = source.substr(eqIndex + 1).replace(/=/g, "");
        if (b.substr(0, 3) != "new")
            return null;
        b = b.substr(3);

        return new StatementAlloc(a, b);
    }

    public createHTML(): JQuery
    {
        return $("<span>")
            .append(this.x)
            .append($("<span>").text(" := new "))
            .append(this.C)
            .append($("<span>").text(";"));
    }
}

export class StatementCall extends Statement
{
    public constructor(
        public x: string,
        public y: string,
        public m: string,
        public z: string)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
        if (!Expression.isValidX(y)) throw "null arg";
        if (!Expression.isValidX(m)) throw "null arg";
        if (!Expression.isValidX(z)) throw "null arg";
    }

    public static parse(source: string): Statement
    {
        var eqIndex = source.indexOf(":=");
        if (eqIndex == -1) eqIndex = source.indexOf("=");
        if (eqIndex == -1) return null;

        var x = source.substr(0, eqIndex);
        var b = source.substr(eqIndex + 1).replace(/=/g, "");

        var dotIndex = b.lastIndexOf(".");
        if (dotIndex == -1)
            return null;
        var y = b.substr(0, dotIndex);
        var call = b.substr(dotIndex + 1);
        var braceIndex = call.indexOf("(");
        if (braceIndex == -1)
            return null;
        var m = call.substr(0, braceIndex);
        var z = call.substr(braceIndex + 1).replace(")", "");

        return new StatementCall(x, y, m, z);
    }

    public createHTML(): JQuery
    {
        return $("<span>")
            .append(this.x)
            .append($("<span>").text(" := "))
            .append(this.y + "." + this.m + "(" + this.z + ")")
            .append($("<span>").text(";"));
    }
}

export class StatementReturn extends Statement
{
    public constructor(public x: string) 
    { 
        super(); 
        if (!Expression.isValidX(x)) throw "null arg";
    }

    public static parse(source: string): Statement
    {
        if (source.substr(0, 6) != "return")
            return null;
        return new StatementReturn(source.substr(6));
    }

    public createHTML(): JQuery
    {
        return $("<span>")
            .append($("<span>").text("return "))
            .append(this.x)
            .append($("<span>").text(";"));
    }
}

export class StatementAssert extends Statement
{
    public constructor(public assertion: VerificationFormula) { super(); }

    public static parse(source: string): Statement
    {
        if (source.substr(0, 6) != "assert")
            return null;
        return new StatementAssert(new VerificationFormula(source.substr(6)));
    }

    public createHTML(): JQuery
    {
        return $("<span>")
            .append($("<span>").text("assert "))
            .append(this.assertion.createHTML())
            .append($("<span>").text(";"));
    }
}

export class StatementRelease extends Statement
{
    public constructor(public assertion: VerificationFormula) { super(); }

    public static parse(source: string): Statement
    {
        if (source.substr(0, 7) != "release")
            return null;
        return new StatementRelease(new VerificationFormula(source.substr(7)));
    }

    public createHTML(): JQuery
    {
        return $("<span>")
            .append($("<span>").text("release "))
            .append(this.assertion.createHTML())
            .append($("<span>").text(";"));
    }
}

export class StatementDeclare extends Statement
{
    public constructor(
        public T: Type,
        public x: string)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
    }

    public static parse(source: string): Statement
    {
        var srcParts = source.trim().split(" ");
        if (srcParts.length != 2) return null;
        var T = Type.parse(srcParts[0]);
        if (T == null) return null;
        return new StatementDeclare(T, srcParts[1]);
    }

    public createHTML(): JQuery
    {
        return $("<span>")
            .append(this.T.createHTML())
            .append($("<span>").text(" "))
            .append(this.x)
            .append($("<span>").text(";"));
    }
}