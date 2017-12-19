define(["require", "exports", "./GeneratorExpression", "../types/VerificationFormula"], function (require, exports, GeneratorExpression_1, VerificationFormula_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    function generateFormulaPartAcc(seed) {
        var res = GeneratorExpression_1.generateExpressionDot(seed);
        return {
            seed: res.seed,
            p: new VerificationFormula_1.FormulaPartAcc(res.e.e, res.e.f)
        };
    }
    function generateFormulaPartEq(seed) {
        var res1 = GeneratorExpression_1.generateExpression(seed);
        var res2 = GeneratorExpression_1.generateExpression(res1.seed);
        return {
            seed: res2.seed,
            p: new VerificationFormula_1.FormulaPartEq(res1.e, res2.e)
        };
    }
    function generateFormulaPartNeq(seed) {
        var res1 = GeneratorExpression_1.generateExpression(seed);
        var res2 = GeneratorExpression_1.generateExpression(res1.seed);
        return {
            seed: res2.seed,
            p: new VerificationFormula_1.FormulaPartNeq(res1.e, res2.e)
        };
    }
    function generateFormulaPart(seed) {
        var lseed = seed % 3;
        seed = Math.floor(seed / 3);
        switch (lseed) {
            case 0: return generateFormulaPartAcc(seed);
            case 1: return generateFormulaPartEq(seed);
            case 2: return generateFormulaPartNeq(seed);
        }
        throw "unreachable";
    }
    function generateVerificationFormula(seed) {
        var maxLen = seed % 4 + 1;
        seed = Math.floor(seed / 4);
        var parts = [];
        while (seed != 0) {
            var res = generateFormulaPart(seed);
            seed = res.seed;
            parts.push(res.p);
            if (parts.length == maxLen)
                break;
        }
        return new VerificationFormula_1.VerificationFormula(null, parts);
    }
    exports.generateVerificationFormula = generateVerificationFormula;
});
