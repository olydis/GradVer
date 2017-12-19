define(["require", "exports", "../types/VerificationFormula", "../types/VerificationFormulaGradual", "./Random", "./GeneratorFormula"], function (require, exports, VerificationFormula_1, VerificationFormulaGradual_1, Random_1, GeneratorFormula_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    function testSupImplies() {
        var p1 = VerificationFormula_1.VerificationFormula.getFalse();
        var p2 = VerificationFormula_1.VerificationFormula.getFalse();
        while (!p1.satisfiable())
            p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        while (!p2.satisfiable())
            p2 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        var gp1 = VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, p1);
        var gp2 = VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, p2);
        var gps = VerificationFormulaGradual_1.VerificationFormulaGradual.supremum(gp1, gp2);
        var t1 = "{" + gp1.toString() + "}";
        var t2 = "{" + gp2.toString() + "}";
        var ts = "{" + gps.toString() + "}";
        if (!p1.implies(gps.staticFormula)
            || !p2.implies(gps.staticFormula))
            console.error("testSupImplies", t1, t2, ts);
    }
    exports.testSupImplies = testSupImplies;
    function testSupComm() {
        var p1 = VerificationFormula_1.VerificationFormula.getFalse();
        var p2 = VerificationFormula_1.VerificationFormula.getFalse();
        while (!p1.satisfiable())
            p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        while (!p2.satisfiable())
            p2 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        var gp1 = VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, p1);
        var gp2 = VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, p2);
        var gps1 = VerificationFormulaGradual_1.VerificationFormulaGradual.supremum(gp1, gp2);
        var gps2 = VerificationFormulaGradual_1.VerificationFormulaGradual.supremum(gp2, gp1);
        var t1 = "{" + gp1.toString() + "}";
        var t2 = "{" + gp2.toString() + "}";
        var ts1 = "{" + gps1.toString() + "}";
        var ts2 = "{" + gps2.toString() + "}";
        if (!gps1.staticFormula.implies(gps2.staticFormula)
            || !gps2.staticFormula.implies(gps1.staticFormula))
            console.error("testSupComm", t1, t2, ts1, ts2);
    }
    exports.testSupComm = testSupComm;
    function testSupAssoc() {
        var p1 = VerificationFormula_1.VerificationFormula.getFalse();
        var p2 = VerificationFormula_1.VerificationFormula.getFalse();
        var p3 = VerificationFormula_1.VerificationFormula.getFalse();
        while (!p1.satisfiable())
            p1 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        while (!p2.satisfiable())
            p2 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        while (!p3.satisfiable())
            p3 = GeneratorFormula_1.generateVerificationFormula(Random_1.rand());
        var gp1 = VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, p1);
        var gp2 = VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, p2);
        var gp3 = VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, p3);
        var gps1 = VerificationFormulaGradual_1.VerificationFormulaGradual.supremum(gp1, VerificationFormulaGradual_1.VerificationFormulaGradual.supremum(gp2, gp3));
        var gps2 = VerificationFormulaGradual_1.VerificationFormulaGradual.supremum(VerificationFormulaGradual_1.VerificationFormulaGradual.supremum(gp1, gp2), gp3);
        var t1 = "{" + gp1.toString() + "}";
        var t2 = "{" + gp2.toString() + "}";
        var t3 = "{" + gp3.toString() + "}";
        var ts1 = "{" + gps1.toString() + "}";
        var ts2 = "{" + gps2.toString() + "}";
        if (!gps1.staticFormula.implies(gps2.staticFormula)
            || !gps2.staticFormula.implies(gps1.staticFormula))
            console.error("testSupAssoc", t1, t2, t3, ts1, ts2);
    }
    exports.testSupAssoc = testSupAssoc;
});
