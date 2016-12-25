define(["require", "exports", "../types/Expression", "../types/ValueExpression"], function (require, exports, Expression_1, ValueExpression_1) {
    "use strict";
    var fields = ["f", "g"];
    var variables = ["a", "b", "c"];
    var values = [0, 1, 2];
    function generateExpressionV(seed) {
        var n = values.length + 1;
        var lseed = seed % n;
        return {
            seed: Math.floor(seed / n),
            e: new Expression_1.ExpressionV(lseed == n - 1
                ? new ValueExpression_1.ValueExpressionNull()
                : new ValueExpression_1.ValueExpressionN(values[lseed]))
        };
    }
    function generateExpressionX(seed) {
        var n = variables.length;
        return {
            seed: Math.floor(seed / n),
            e: new Expression_1.ExpressionX(variables[seed % n])
        };
    }
    function generateExpressionDot(seed) {
        var n = fields.length;
        var field = fields[seed % n];
        var res = generateExpression(Math.floor(seed / n));
        return {
            seed: res.seed,
            e: new Expression_1.ExpressionDot(res.e, field)
        };
    }
    exports.generateExpressionDot = generateExpressionDot;
    function generateExpression(seed) {
        var lseed = seed % 3;
        seed = Math.floor(seed / 3);
        switch (lseed) {
            case 0: return generateExpressionV(seed);
            case 1: return generateExpressionX(seed);
            case 2: return generateExpressionDot(seed);
        }
        throw "unreachable";
    }
    exports.generateExpression = generateExpression;
});
