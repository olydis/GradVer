define(["require", "exports", "./editors/EditVerificationFormula", "./editors/EditableElement", "./runtime/ExecutionEnvironment", "./types/Expression"], function (require, exports, EditVerificationFormula_1, EditableElement_1, ExecutionEnvironment_1, Expression_1) {
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
});
