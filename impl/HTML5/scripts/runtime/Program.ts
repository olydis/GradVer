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
    argType: Type;
    argName: string;
    frmPre: VerificationFormulaGradual;
    frpPost: VerificationFormulaGradual;
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