import { VerificationFormula } from "../types/VerificationFormula";
import { ExpressionX } from "../types/Expression";
import { rand } from "./Random";
import { generateVerificationFormula } from "./GeneratorFormula";

export function testWoAccWorks(): void
{
    var p1 = VerificationFormula.getFalse();
    var p2 = VerificationFormula.getFalse();

    while (!p1.satisfiable() || p1.footprintStatic().length == 0)
        p1 = generateVerificationFormula(rand());
    while (!p1.implies(p2) || p2.footprintStatic().length == 0)
        p2 = generateVerificationFormula(rand());

    var p1wo2 = p1;
    for (var a of p2.footprintStatic())
        p1wo2 = p1wo2.woAcc(a.e, a.f);

    var p1x = new VerificationFormula(null, p2.parts.concat(p1wo2.parts));

    var t1 = "{" + p1.createHTML().text() + "}";
    var t2 = "{" + p2.createHTML().text() + "}";
    var t12 = "{" + p1wo2.createHTML().text() + "}";
    var t1x = "{" + p1x.createHTML().text() + "}";

    if (!p1.implies(p1x))// FAIL
        console.error("TestWoAcc works", t1, t2, t12, t1x);
}

export function testWoAccMonotonic(): void
{
    var p1 = VerificationFormula.getFalse();
    var p2 = VerificationFormula.getFalse();

    while (!p1.satisfiable())
        p1 = generateVerificationFormula(rand());
    while (!p1.implies(p2))
        p2 = generateVerificationFormula(rand());

    var p1x = p1.woAcc(new ExpressionX("a"), "f");
    var p2x = p2.woAcc(new ExpressionX("a"), "f");

    var t1 = "{" + p1.createHTML().text() + "}";
    var t2 = "{" + p2.createHTML().text() + "}";

    var t1x = "{" + p1x.createHTML().text() + "}";
    var t2x = "{" + p2x.createHTML().text() + "}";

    if (!p1x.implies(p2x))// FAIL
        console.error("TestWoAcc monotonic", t1, t2, t1x, t2x);
}

export function testWoAccPreserveSat(): void
{
    var p1 = VerificationFormula.getFalse();

    while (!p1.satisfiable())
        p1 = generateVerificationFormula(rand());

    var p1x = p1.woAcc(new ExpressionX("a"), "f");

    var t1 = "{" + p1.createHTML().text() + "}";

    var t1x = "{" + p1x.createHTML().text() + "}";

    if (!p1.implies(p1x))// FAIL
        console.error("TestWoAcc preserve sat", t1, t1x);
}

export function testWoAccPreserveSfrm(): void
{
    var p1 = generateVerificationFormula(rand());

    while (!p1.sfrm())
        p1 = generateVerificationFormula(rand());

    var p1x = p1.woAcc(new ExpressionX("a"), "f");

    var t1 = "{" + p1.createHTML().text() + "}";

    var t1x = "{" + p1x.createHTML().text() + "}";

    if (!p1x.sfrm())// FAIL
        console.error("TestWoAcc preserve sfrm", t1, t1x);
}