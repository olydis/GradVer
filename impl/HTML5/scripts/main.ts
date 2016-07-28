import { EditInstructions } from "./editors/EditInstructions";
import { EditVerificationFormula } from "./editors/EditVerificationFormula";
import { EditableElement } from "./editors/EditableElement";
import { ExecutionEnvironment } from "./runtime/ExecutionEnvironment";
import { Expression, ExpressionDot } from "./types/Expression";
//import { Hoare } from "./runtime/Hoare";
import { Program } from "./runtime/Program";

$(() =>
{
    $(window).click(() => EditableElement.editEndAll());

    var program: Program = {
        classes: [],
        main: []
    };
    var env = new ExecutionEnvironment(program);
    //var hoare = new Hoare(env);

    // containerProps
    (() => {
        var input = new EditVerificationFormula("", phi => {
            $("#containerPropsOutSat").text(phi.satisfiable() ? "yes" : "no");
            $("#containerPropsOutSfrm").text(phi.sfrm() ? "yes" : "no");
            $("#containerPropsOutNorm").text(phi.norm().createHTML().text());
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
            $("#containerWoVarOutput").text(phi.woVar(x).createHTML().text());
        };
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
                $("#containerWoAccOutput").text(phi.woAcc(accE.e, accE.f).createHTML().text());
            else
                $("#containerWoAccOutput").text("format error");
        };
        $("#containerWoAccInput").append(input.createHTML());
        
    })();

    // var editor = new EditInstructions(
    //     $("#codeContainer")
    //     //, hoare
    // );
    // $("#btnVerify").click(() => editor.btnCheckAll());
    // $("#btnHammer").click(() => editor.btnPropDownAll());
    // $("#btnReset").click(() => editor.btnResetAssertionsAll(false));
    // $("#btnResetQ").click(() => editor.btnResetAssertionsAll(true));
    // $("#btnE1").click(() => editor.loadEx1());
    // editor.loadEx1();
});