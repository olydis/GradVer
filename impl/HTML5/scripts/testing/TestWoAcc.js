define(["require", "exports", "../types/VerificationFormula", "../types/Expression", "./Random", "./GeneratorFormula"], function (require, exports, VerificationFormula_1, Expression_1, Random_1, GeneratorFormula_1) {
    "use strict";
    function testWoAccWorks() {
        var p1 = VerificationFormula_1.VerificationFormula.getFalse();
        var p2 = VerificationFormula_1.VerificationFormula.getFalse();
        while (!p1.satisfiable() || p1.footprintStatic().length == 0)
            p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        while (!p1.implies(p2) || p2.footprintStatic().length == 0)
            p2 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        var p1wo2 = p1;
        for (var _i = 0, _a = p2.footprintStatic(); _i < _a.length; _i++) {
            var a = _a[_i];
            p1wo2 = p1wo2.woAcc(a.e, a.f);
        }
        var p1x = new VerificationFormula_1.VerificationFormula(null, p2.parts.concat(p1wo2.parts));
        var t1 = "{" + p1.createHTML().text() + "}";
        var t2 = "{" + p2.createHTML().text() + "}";
        var t12 = "{" + p1wo2.createHTML().text() + "}";
        var t1x = "{" + p1x.createHTML().text() + "}";
        if (!p1.implies(p1x))
            console.error("TestWoAcc works", t1, t2, t12, t1x);
    }
    exports.testWoAccWorks = testWoAccWorks;
    function testWoAccMonotonic() {
        var p1 = VerificationFormula_1.VerificationFormula.getFalse();
        var p2 = VerificationFormula_1.VerificationFormula.getFalse();
        while (!p1.satisfiable())
            p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        while (!p1.implies(p2))
            p2 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        var p1x = p1.woAcc(new Expression_1.ExpressionX("a"), "f");
        var p2x = p2.woAcc(new Expression_1.ExpressionX("a"), "f");
        var t1 = "{" + p1.createHTML().text() + "}";
        var t2 = "{" + p2.createHTML().text() + "}";
        var t1x = "{" + p1x.createHTML().text() + "}";
        var t2x = "{" + p2x.createHTML().text() + "}";
        if (!p1x.implies(p2x))
            console.error("TestWoAcc monotonic", t1, t2, t1x, t2x);
    }
    exports.testWoAccMonotonic = testWoAccMonotonic;
    function testWoAccPreserveSat() {
        var p1 = VerificationFormula_1.VerificationFormula.getFalse();
        while (!p1.satisfiable())
            p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        var p1x = p1.woAcc(new Expression_1.ExpressionX("a"), "f");
        var t1 = "{" + p1.createHTML().text() + "}";
        var t1x = "{" + p1x.createHTML().text() + "}";
        if (!p1.implies(p1x))
            console.error("TestWoAcc preserve sat", t1, t1x);
    }
    exports.testWoAccPreserveSat = testWoAccPreserveSat;
    function testWoAccPreserveSfrm() {
        var p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        while (!p1.sfrm())
            p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        var p1x = p1.woAcc(new Expression_1.ExpressionX("a"), "f");
        var t1 = "{" + p1.createHTML().text() + "}";
        var t1x = "{" + p1x.createHTML().text() + "}";
        if (!p1x.sfrm())
            console.error("TestWoAcc preserve sfrm", t1, t1x);
    }
    exports.testWoAccPreserveSfrm = testWoAccPreserveSfrm;
});
