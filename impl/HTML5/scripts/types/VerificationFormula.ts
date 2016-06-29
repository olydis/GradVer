import { Expression } from "./Expression";

abstract class FormulaPart
{
    abstract createHTML(): JQuery;

    public static parse(source: string): FormulaPart
    {
        source = source.replace(/\s/g, "");
        source = source.replace(/\(/g, "");
        source = source.replace(/\)/g, "");
        var result: FormulaPart = null;
        if (!result) result = FormulaPartType.parse(source);
        if (!result) result = FormulaPartAcc.parse(source);
        if (!result) result = FormulaPartTrue.parse(source);
        if (!result) result = FormulaPartNeq.parse(source);
        if (!result) result = FormulaPartEq.parse(source);
        return result;
    }
}

class FormulaPartTrue extends FormulaPart
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
}

class FormulaPartEq extends FormulaPart
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
}

class FormulaPartNeq extends FormulaPart
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
}

class FormulaPartAcc extends FormulaPart
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
}

class FormulaPartType extends FormulaPart
{
    public constructor(
        private x: string,
        private T: string)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
        if (!Expression.isValidX(T)) throw "null arg";
    }

    public static parse(source: string): Expression
    {
        var dotIndex = source.lastIndexOf(":");
        if (dotIndex == -1)
            return null;
        var x = source.substr(0, dotIndex);
        var T = source.substr(dotIndex + 1);
        return new FormulaPartType(x, T);
    }

    public createHTML(): JQuery
    {
        return $("<span>")
            .append($("<span>").text("("))
            .append($("<span>").text(this.x))
            .append($("<span>").text(" : "))
            .append($("<span>").text(this.T))
            .append($("<span>").text(")"));
    }
}

export class VerificationFormula
{
    private html: JQuery;

    public parts: FormulaPart[];

    public constructor(
        source: string = ""
    )
    {
        this.html = $("<span>");

        this.parts = [];
        source = source.trim();
        if (source != "")
            this.parts = source.split("*").map(FormulaPart.parse).filter(part => part != null);
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
}