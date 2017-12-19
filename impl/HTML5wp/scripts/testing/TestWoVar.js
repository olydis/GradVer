define(["require", "exports", "../types/VerificationFormula", "./Random", "./GeneratorFormula"], function (require, exports, VerificationFormula_1, Random_1, GeneratorFormula_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    function testWoVarMonotonic() {
        var p1 = VerificationFormula_1.VerificationFormula.getFalse();
        var p2 = VerificationFormula_1.VerificationFormula.getFalse();
        while (!p1.satisfiable())
            p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        while (!p1.implies(p2))
            p2 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        var p1x = p1.woVar("a");
        var p2x = p2.woVar("a");
        var t1 = "{" + p1.toString() + "}";
        var t2 = "{" + p2.toString() + "}";
        var t1x = "{" + p1x.toString() + "}";
        var t2x = "{" + p2x.toString() + "}";
        if (!p1x.implies(p2x))
            console.error("TestWoVar monotonic", t1, t2, t1x, t2x);
    }
    exports.testWoVarMonotonic = testWoVarMonotonic;
    function testWoVarPreserveSat() {
        var p1 = VerificationFormula_1.VerificationFormula.getFalse();
        while (!p1.satisfiable())
            p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        var p1x = p1.woVar("a");
        var t1 = "{" + p1.toString() + "}";
        var t1x = "{" + p1x.toString() + "}";
        if (!p1.implies(p1x))
            console.error("TestWoVar preserve sat", t1, t1x);
    }
    exports.testWoVarPreserveSat = testWoVarPreserveSat;
    function testWoVarPreserveSfrm() {
        var p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        while (!p1.sfrm())
            p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        var p1x = p1.woVar("a");
        var t1 = "{" + p1.toString() + "}";
        var t1x = "{" + p1x.toString() + "}";
        if (!p1x.sfrm())
            console.error("TestWoVar preserve sfrm", t1, t1x);
    }
    exports.testWoVarPreserveSfrm = testWoVarPreserveSfrm;
});
