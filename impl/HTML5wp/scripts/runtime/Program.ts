import { Type } from "../types/Type";
import { Statement } from "../types/Statement";
import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual";

export interface Field
{
    type: Type;
    name: string;
}

export interface Method
{
    retType: Type;
    name: string;
    args: { type: Type, name: string }[];
    frmPre: VerificationFormulaGradual;
    frmPost: VerificationFormulaGradual;
    body: Statement[];
}

export interface Class
{
    name: string;
    fields: Field[];
    methods: Method[];
}

export interface Program
{
    classes: Class[];
    main: Statement[];
}

function indent(amount: number): (s: string) => string
{
    var prefix = "";
    for (var i = 0; i < amount; ++i)
        prefix += " ";

    return s => {
        var lines = s.split("\n");
        lines = lines.map(l => prefix + l);
        return lines.join("\n");
    };
}

function printField(f: Field): string
{
    return f.type + " " + f.name + ";";
}

function printMethod(m: Method): string
{
    var res = m.retType + " " + m.name + "(" + m.args.map(a => a.type + " " + a.name).join(", ") + ")";
    res += "\n    requires " + m.frmPre + ";"
    res += "\n    ensures  " + m.frmPost + ";"
    res += "\n{\n";
    res += m.body.map(x => x.toString()).map(indent(4)).join("\n");
    res += "\n}\n";
    return res;
}

function printClass(c: Class): string
{
    var res = "class " + c.name;
    res += "\n{\n";
    res += c.fields.map(printField).map(indent(4)).join("\n");
    if (c.fields.length > 0 && c.methods.length > 0)
        res += "\n\n";
    res += c.methods.map(printMethod).map(indent(4)).join("\n");
    res += "\n}\n";
    return res;
}

export function printProgram(p: Program): string
{
    return p.classes.map(printClass).join("\n");
}