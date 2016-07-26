define(["require", "exports", "./editors/EditInstructions", "./editors/EditVerificationFormula", "./editors/EditableElement", "./runtime/ExecutionEnvironment"], function (require, exports, EditInstructions_1, EditVerificationFormula_1, EditableElement_1, ExecutionEnvironment_1) {
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
        {
            var input = new EditVerificationFormula_1.EditVerificationFormula("", function (phi) {
                $("#containerPropsOutSat").text(phi.satisfiable() ? "yes" : "no");
                $("#containerPropsOutSfrm").text(phi.sfrm() ? "yes" : "no");
                $("#containerPropsOutNorm").text(phi.norm().createHTML().text());
            });
            $("#containerPropsInput").append(input.createHTML());
        }
        // containerWoVar
        {
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
        }
        var editor = new EditInstructions_1.EditInstructions($("#codeContainer"));
        $("#btnVerify").click(function () { return editor.btnCheckAll(); });
        $("#btnHammer").click(function () { return editor.btnPropDownAll(); });
        $("#btnReset").click(function () { return editor.btnResetAssertionsAll(false); });
        $("#btnResetQ").click(function () { return editor.btnResetAssertionsAll(true); });
        $("#btnE1").click(function () { return editor.loadEx1(); });
        editor.loadEx1();
    });
});
