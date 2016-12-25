import { Program, Class, Field, Method } from "./Program";
import { Type, TypeClass } from "../types/Type";
import { Statement } from "../types/Statement";
import { VerificationFormula } from "../types/VerificationFormula";

import { Expression, ExpressionDot, ExpressionV, ExpressionX } from "./../types/Expression";

export class ExecutionEnvironment
{
    public constructor(
        private program: Program
    )
    {
    }

    private getMain(): Statement[]
    {
        return this.program.main;
    }

    private getClasses(): Class[]
    {
        return this.program.classes;
    }

    private getClass(C: string): Class
    {
        var res = this.getClasses().filter(c => c.name == C);
        return res.length == 0 ? null : res[0];
    }

    public fields(C: string): Field[]
    {
        var cls = this.getClass(C);
        return cls == null
            ? null
            : cls.fields;
    }

    public fieldType(C: string, f: string): Type
    {
        var res = this.fields(C);
        if (res == null) return null;
        res = res.filter(c => c.name == f);
        return res.length == 0 ? null : res[0].type;
    }

    public mmethod(C: string, m: string): Method
    {
        var res = this.getClass(C);
        if (res == null) return null;
        var mm = res.methods.filter(c => c.name == m);
        return mm.length == 0 ? null : mm[0];
    }
}