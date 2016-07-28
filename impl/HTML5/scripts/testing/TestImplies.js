define(["require", "exports", "../types/VerificationFormula", "./Random", "./GeneratorFormula"], function (require, exports, VerificationFormula_1, Random_1, GeneratorFormula_1) {
    "use strict";
    function testImpliesTransitivity() {
        var p1 = VerificationFormula_1.VerificationFormula.getFalse();
        var p2 = VerificationFormula_1.VerificationFormula.getFalse();
        var p3 = VerificationFormula_1.VerificationFormula.getFalse();
        while (!p1.satisfiable())
            p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        while (!p1.implies(p2))
            p2 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        while (!p2.implies(p3))
            p3 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        var t1 = "{" + p1.createHTML().text() + "}";
        var t2 = "{" + p2.createHTML().text() + "}";
        var t3 = "{" + p3.createHTML().text() + "}";
        if (!p1.implies(p3))
            console.error("transitivity", t1, t2, t3);
    }
    exports.testImpliesTransitivity = testImpliesTransitivity;
});
