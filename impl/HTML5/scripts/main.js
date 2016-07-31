define(["require", "exports", "./editors/EditVerificationFormula", "./editors/EditableElement", "./runtime/ExecutionEnvironment", "./types/Expression", "./testing/MainTest", "./types/VerificationFormulaGradual"], function (require, exports, EditVerificationFormula_1, EditableElement_1, ExecutionEnvironment_1, Expression_1, MainTest_1, VerificationFormulaGradual_1) {
    "use strict";
    $(function () {
        $(window).click(function () { return EditableElement_1.EditableElement.editEndAll(); });
        var program = {
            classes: [],
            main: []
        };
        var env = new ExecutionEnvironment_1.ExecutionEnvironment(program);
        //var hoare = new Hoare(env);
        // containerProps
        (function () {
            var input = new EditVerificationFormula_1.EditVerificationFormula("", function (phi) {
                $("#containerPropsOutSat").text(phi.satisfiable() ? "yes" : "no");
                $("#containerPropsOutSfrm").text(phi.sfrm() ? "yes" : "no");
                $("#containerPropsOutNorm").text(phi.norm().createHTML().text());
            });
            $("#containerPropsInput").append(input.createHTML());
        })();
        // containerWoVar
        (function () {
            var update = function () { };
            var input = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            var inputVar = $("#containerWoVarInputVar");
            inputVar.on("input", function () { return update(); });
            update = function () {
                var phi = input.getFormula();
                var x = inputVar.val();
                $("#containerWoVarOutput").text(phi.woVar(x).createHTML().text());
            };
            update();
            $("#containerWoVarInput").append(input.createHTML());
        })();
        // containerWoAcc
        (function () {
            var update = function () { };
            var input = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            var inputAcc = $("#containerWoAccInputAcc");
            inputAcc.on("input", function () { return update(); });
            update = function () {
                var phi = input.getFormula();
                var accText = inputAcc.val();
                var accE = Expression_1.Expression.parse(accText);
                if (accE instanceof Expression_1.ExpressionDot)
                    $("#containerWoAccOutput").text(phi.woAcc(accE.e, accE.f).createHTML().text());
                else
                    $("#containerWoAccOutput").text("format error");
            };
            update();
            $("#containerWoAccInput").append(input.createHTML());
        })();
        // containerImplies
        (function () {
            var update = function () { };
            var inputA = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            var inputB = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            update = function () {
                var pA = inputA.getFormula();
                var pB = inputB.getFormula();
                $("#containerImpliesOutput").text(pA.impliesRuntime(pB.staticFormula).createHTML().text());
            };
            update();
            $("#containerImpliesInputA").append(inputA.createHTML());
            $("#containerImpliesInputB").append(inputB.createHTML());
        })();
        // containerSup
        (function () {
            var update = function () { };
            var inputA = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            var inputB = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            update = function () {
                var pA = inputA.getFormula();
                var pB = inputB.getFormula();
                if (!pA.gradual) {
                    inputA.setFormula(VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, pA.staticFormula));
                    return;
                }
                if (!pB.gradual) {
                    inputB.setFormula(VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, pB.staticFormula));
                    return;
                }
                $("#containerSupOutput").text(VerificationFormulaGradual_1.VerificationFormulaGradual.supremum(pA, pB).createHTML().text());
            };
            update();
            $("#containerSupInputA").append(inputA.createHTML());
            $("#containerSupInputB").append(inputB.createHTML());
        })();
        $("#btnTESTS").click(function () { return MainTest_1.testAll(); });
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
});
