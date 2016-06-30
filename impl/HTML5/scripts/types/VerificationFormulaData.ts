import { Expression } from "./Expression";
import { Type } from "./Type";
import { FootprintStatic } from "./FootprintStatic";

export type ExpressionPair = { e1: Expression, e2: Expression };

export interface VerificationFormulaData
{
    equalities: ExpressionPair[];
    inEqualities: ExpressionPair[];
    types: { x: string, T: Type }[];
    access: FootprintStatic;
    knownToBeFalse: boolean;
}