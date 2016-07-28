import { Expression, ExpressionV, ExpressionDot, ExpressionX } from "../types/Expression";
import { ValueExpression, ValueExpressionN, ValueExpressionNull } from "../types/ValueExpression";

var fields: string[] = ["f", "g"];
var variables: string[] = ["a", "b", "c"];
var values: number[] = [0, 1, 2];

function generateExpressionV(seed: number): { seed: number, e: ExpressionV }
{
    var n = values.length + 1;
    var lseed = seed % n;
    return {
        seed: Math.floor(seed / n),
        e: new ExpressionV(lseed == n - 1
                ? new ValueExpressionNull()
                : new ValueExpressionN(values[lseed]))
    };
}
function generateExpressionX(seed: number): { seed: number, e: ExpressionX }
{
    var n = variables.length;
    return {
        seed: Math.floor(seed / n),
        e: new ExpressionX(variables[seed % n])
    };
}
export function generateExpressionDot(seed: number): { seed: number, e: ExpressionDot }
{
    var n = fields.length;
    var field = fields[seed % n];
    var res = generateExpression(Math.floor(seed / n));
    return {
        seed: res.seed,
        e: new ExpressionDot(res.e, field)
    };
}

export function generateExpression(seed: number): { seed: number, e: Expression }
{
    var lseed = seed % 3;
    seed = Math.floor(seed / 3);
    switch (lseed) {
        case 0: return generateExpressionV(seed);
        case 1: return generateExpressionX(seed);
        case 2: return generateExpressionDot(seed);
    }
    throw "unreachable";
}