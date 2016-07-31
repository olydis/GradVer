import { VerificationFormula } from "../types/VerificationFormula";
import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual";
import { rand } from "./Random";
import { generateVerificationFormula } from "./GeneratorFormula";

export function testSupImplies(): void
{
    var p1 = VerificationFormula.getFalse();
    var p2 = VerificationFormula.getFalse();

    while (!p1.satisfiable())
        p1 = generateVerificationFormula(rand());
    while (!p2.satisfiable())
        p2 = generateVerificationFormula(rand());

    var gp1 = VerificationFormulaGradual.create(true, p1);
    var gp2 = VerificationFormulaGradual.create(true, p2);
    var gps = VerificationFormulaGradual.supremum(gp1, gp2);

    var t1 = "{" + gp1.createHTML().text() + "}";
    var t2 = "{" + gp2.createHTML().text() + "}";
    var ts = "{" + gps.createHTML().text() + "}";

    if (!p1.implies(gps.staticFormula)
     || !p2.implies(gps.staticFormula))// FAIL
        console.error("testSupImplies", t1, t2, ts);
}

export function testSupComm(): void
{
    var p1 = VerificationFormula.getFalse();
    var p2 = VerificationFormula.getFalse();

    while (!p1.satisfiable())
        p1 = generateVerificationFormula(rand());
    while (!p2.satisfiable())
        p2 = generateVerificationFormula(rand());

    var gp1 = VerificationFormulaGradual.create(true, p1);
    var gp2 = VerificationFormulaGradual.create(true, p2);
    var gps1 = VerificationFormulaGradual.supremum(gp1, gp2);
    var gps2 = VerificationFormulaGradual.supremum(gp2, gp1);

    var t1 = "{" + gp1.createHTML().text() + "}";
    var t2 = "{" + gp2.createHTML().text() + "}";
    var ts1 = "{" + gps1.createHTML().text() + "}";
    var ts2 = "{" + gps2.createHTML().text() + "}";

    if (!gps1.staticFormula.implies(gps2.staticFormula)
     || !gps2.staticFormula.implies(gps1.staticFormula))// FAIL
        console.error("testSupComm", t1, t2, ts1, ts2);
}

export function testSupAssoc(): void
{
    var p1 = VerificationFormula.getFalse();
    var p2 = VerificationFormula.getFalse();
    var p3 = VerificationFormula.getFalse();

    while (!p1.satisfiable())
        p1 = generateVerificationFormula(rand());
    while (!p2.satisfiable())
        p2 = generateVerificationFormula(rand());
    while (!p3.satisfiable())
        p3 = generateVerificationFormula(rand());

    var gp1 = VerificationFormulaGradual.create(true, p1);
    var gp2 = VerificationFormulaGradual.create(true, p2);
    var gp3 = VerificationFormulaGradual.create(true, p3);
    var gps1 = VerificationFormulaGradual.supremum(gp1, VerificationFormulaGradual.supremum(gp2, gp3));
    var gps2 = VerificationFormulaGradual.supremum(VerificationFormulaGradual.supremum(gp1, gp2), gp3);

    var t1 = "{" + gp1.createHTML().text() + "}";
    var t2 = "{" + gp2.createHTML().text() + "}";
    var t3 = "{" + gp3.createHTML().text() + "}";
    var ts1 = "{" + gps1.createHTML().text() + "}";
    var ts2 = "{" + gps2.createHTML().text() + "}";

    if (!gps1.staticFormula.implies(gps2.staticFormula)
     || !gps2.staticFormula.implies(gps1.staticFormula))// FAIL
        console.error("testSupAssoc", t1, t2, t3, ts1, ts2);
}