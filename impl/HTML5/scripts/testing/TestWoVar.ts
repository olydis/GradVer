import { VerificationFormula } from "../types/VerificationFormula";
import { rand } from "./Random";
import { generateVerificationFormula } from "./GeneratorFormula";

export function testWoVarMonotonic(): void
{
    var p1 = VerificationFormula.getFalse();
    var p2 = VerificationFormula.getFalse();

    while (!p1.satisfiable())
        p1 = generateVerificationFormula(rand());
    while (!p1.implies(p2))
        p2 = generateVerificationFormula(rand());

    var p1x = p1.woVar("a");
    var p2x = p2.woVar("a");

    var t1 = "{" + p1.createHTML().text() + "}";
    var t2 = "{" + p2.createHTML().text() + "}";

    var t1x = "{" + p1x.createHTML().text() + "}";
    var t2x = "{" + p2x.createHTML().text() + "}";

    if (!p1x.implies(p2x))// FAIL
        console.error("TestWoVar monotonic", t1, t2, t1x, t2x);
}

export function testWoVarPreserveSat(): void
{
    var p1 = VerificationFormula.getFalse();

    while (!p1.satisfiable())
        p1 = generateVerificationFormula(rand());

    var p1x = p1.woVar("a");

    var t1 = "{" + p1.createHTML().text() + "}";

    var t1x = "{" + p1x.createHTML().text() + "}";

    if (!p1.implies(p1x))// FAIL
        console.error("TestWoVar preserve sat", t1, t1x);
}

export function testWoVarPreserveSfrm(): void
{
    var p1 = generateVerificationFormula(rand());

    while (!p1.sfrm())
        p1 = generateVerificationFormula(rand());

    var p1x = p1.woVar("a");

    var t1 = "{" + p1.createHTML().text() + "}";

    var t1x = "{" + p1x.createHTML().text() + "}";

    if (!p1x.sfrm())// FAIL
        console.error("TestWoVar preserve sfrm", t1, t1x);
}