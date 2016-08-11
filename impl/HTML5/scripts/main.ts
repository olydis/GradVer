import { EditInstructions } from "./editors/EditInstructions";
import { EditVerificationFormula } from "./editors/EditVerificationFormula";
import { EditableElement } from "./editors/EditableElement";
import { ExecutionEnvironment } from "./runtime/ExecutionEnvironment";
import { Expression, ExpressionDot } from "./types/Expression";
import { Hoare } from "./runtime/Hoare";
import { Program } from "./runtime/Program";
import { testAll } from "./testing/MainTest";
import { VerificationFormulaGradual } from "./types/VerificationFormulaGradual";
import { Type, TypeClass } from "./types/Type";
import { VerificationFormula, FormulaPart, FormulaPartEq, FormulaPartNeq } from "./types/VerificationFormula";

$(() =>
{
    $(window).click(() => EditableElement.editEndAll());

    var program: Program = {
        classes: [
        {
            name: "Point",
            fields: [
            {
                name: "x",
                type: Type.getPrimitiveInt()
            },
            {
                name: "y",
                type: Type.getPrimitiveInt()
            }],
            methods: []
        },
        {
            name: "Points",
            fields: [
            {
                name: "h",
                type: new TypeClass("Point")
            },
            {
                name: "t",
                type: new TypeClass("Points")
            }],
            methods: []
        }],
        main: []
    };
    var env = new ExecutionEnvironment(program);
    var hoare = new Hoare(env);

    // containerHoare
    (() => {
        var code = new EditInstructions($("#containerHoareCode"), hoare);
        var update = () => {};
        var inputPre = new EditVerificationFormula("?", () => update());
        var inputPost = new EditVerificationFormula("?", () => update());
        update = () =>
        {
            var pPre = inputPre.getFormula();
            var pPost = inputPost.getFormula();
            code.updateConditions(pPre, pPost);
        };
        update();
        $("#containerHoarePre").append(inputPre.createHTML());
        $("#containerHoarePost").append(inputPost.createHTML());

        $("#btnEx1").click(() => code.loadEx1());
    })();

    // containerProps
    (() => {
        var input = new EditVerificationFormula("", phi => {
            $("#containerPropsOutSat").text(phi.satisfiable() ? "yes" : "no");
            $("#containerPropsOutSfrm").text(phi.sfrm() ? "yes" : "no");
            $("#containerPropsOutNorm").text(phi.norm().toString());
        });
        $("#containerPropsInput").append(input.createHTML());
    })();

    // containerWoVar
    (() => {
        var update = () => {};
        var input = new EditVerificationFormula("", () => update());
        var inputVar = $("#containerWoVarInputVar");
        inputVar.on("input", () => update());
        update = () =>
        {
            var phi = input.getFormula();
            var x = inputVar.val();
            $("#containerWoVarOutput").text(phi.woVar(x).toString());
        };
        update();
        $("#containerWoVarInput").append(input.createHTML());
    })();
    
    // containerWoAcc
    (() => {
        var update = () => {};
        var input = new EditVerificationFormula("", () => update());
        var inputAcc = $("#containerWoAccInputAcc");
        inputAcc.on("input", () => update());
        update = () =>
        {
            var phi = input.getFormula();
            var accText = inputAcc.val();
            var accE = Expression.parse(accText);
            if (accE instanceof ExpressionDot)
                $("#containerWoAccOutput").text(phi.woAcc(accE.e, accE.f).toString());
            else
                $("#containerWoAccOutput").text("format error");
        };
        update();
        $("#containerWoAccInput").append(input.createHTML());
    })();
    
    // containerImplies
    (() => {
        var update = () => {};
        var inputA = new EditVerificationFormula("", () => update());
        var inputB = new EditVerificationFormula("", () => update());
        update = () =>
        {
            var pA = inputA.getFormula();
            var pB = inputB.getFormula();
            $("#containerImpliesOutput").text(pA.implies(pB.staticFormula).toString());
        };
        update();
        $("#containerImpliesInputA").append(inputA.createHTML());
        $("#containerImpliesInputB").append(inputB.createHTML());
    })();
    
    // containerSup
    (() => {
        var update = () => {};
        var inputA = new EditVerificationFormula("", () => update());
        var inputB = new EditVerificationFormula("", () => update());
        update = () =>
        {
            var pA = inputA.getFormula();
            var pB = inputB.getFormula();
            if (!pA.gradual)
            {
                inputA.setFormula(VerificationFormulaGradual.create(true, pA.staticFormula));
                return;
            }
            if (!pB.gradual)
            {
                inputB.setFormula(VerificationFormulaGradual.create(true, pB.staticFormula));
                return;
            }

            $("#containerSupOutput").text(VerificationFormulaGradual.supremum(pA, pB).toString());
        };
        update();
        $("#containerSupInputA").append(inputA.createHTML());
        $("#containerSupInputB").append(inputB.createHTML());
    })();

    $("#btnTESTS").click(() => testAll());

    // var editor = new EditInstructions(
    //     $("#codeContainer")
    //     //, hoare
    // );
    // $("#btnVerify").click(() => editor.btnCheckAll());
    // $("#btnHammer").click(() => editor.btnPropDownAll());
    // $("#btnReset").click(() => editor.btnResetAssertionsAll(false));
    // $("#btnResetQ").click(() => editor.btnResetAssertionsAll(true));
    // editor.loadEx1();
});