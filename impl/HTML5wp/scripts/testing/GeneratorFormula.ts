import { generateExpression, generateExpressionDot } from "./GeneratorExpression";
import { VerificationFormula, FormulaPart, FormulaPartAcc, FormulaPartEq, FormulaPartNeq } from "../types/VerificationFormula";

function generateFormulaPartAcc(seed: number): { seed: number, p: FormulaPartAcc }
{
    var res = generateExpressionDot(seed);
    return {
        seed: res.seed,
        p: new FormulaPartAcc(res.e.e, res.e.f)
    };
}
function generateFormulaPartEq(seed: number): { seed: number, p: FormulaPartEq }
{
    var res1 = generateExpression(seed);
    var res2 = generateExpression(res1.seed);
    return {
        seed: res2.seed,
        p: new FormulaPartEq(res1.e, res2.e)
    };
}
function generateFormulaPartNeq(seed: number): { seed: number, p: FormulaPartNeq }
{
    var res1 = generateExpression(seed);
    var res2 = generateExpression(res1.seed);
    return {
        seed: res2.seed,
        p: new FormulaPartNeq(res1.e, res2.e)
    };
}
function generateFormulaPart(seed: number): { seed: number, p: FormulaPart }
{
    var lseed = seed % 3;
    seed = Math.floor(seed / 3);
    switch (lseed) {
        case 0: return generateFormulaPartAcc(seed);
        case 1: return generateFormulaPartEq(seed);
        case 2: return generateFormulaPartNeq(seed);
    }
    throw "unreachable";
}

export function generateVerificationFormula(seed: number): VerificationFormula
{
    var maxLen = seed % 4 + 1;
    seed = Math.floor(seed / 4);

    var parts: FormulaPart[] = [];
    while (seed != 0)
    {
        var res = generateFormulaPart(seed);
        seed = res.seed;
        parts.push(res.p);

        if (parts.length == maxLen)
            break;
    }
    return new VerificationFormula(null, parts);
}