import { VerificationFormula } from "../types/VerificationFormula";
import { rand } from "./Random";
import { generateVerificationFormula } from "./GeneratorFormula";

export function testImpliesTransitivity(): void
{
    var p1 = VerificationFormula.getFalse();
    var p2 = VerificationFormula.getFalse();
    var p3 = VerificationFormula.getFalse();

    while (!p1.satisfiable())
        p1 = generateVerificationFormula(rand());
    while (!p1.implies(p2))
        p2 = generateVerificationFormula(rand());
    while (!p2.implies(p3))
        p3 = generateVerificationFormula(rand());

    var t1 = "{" + p1.toString() + "}";
    var t2 = "{" + p2.toString() + "}";
    var t3 = "{" + p3.toString() + "}";

    if (!p1.implies(p3))// FAIL
        console.error("TestImplies transitivity", t1, t2, t3);
}