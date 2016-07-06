define(["require", "exports", "./editors/EditInstructions", "./editors/EditableElement", "./runtime/ExecutionEnvironment", "./runtime/Hoare"], function (require, exports, EditInstructions_1, EditableElement_1, ExecutionEnvironment_1, Hoare_1) {
    "use strict";
    $(function () {
        $(window).click(function () { return EditableElement_1.EditableElement.editEndAll(); });
        var program = {
            classes: [],
            main: []
        };
        var env = new ExecutionEnvironment_1.ExecutionEnvironment(program);
        var hoare = new Hoare_1.Hoare(env);
        var editor = new EditInstructions_1.EditInstructions($("#codeContainer"), hoare);
        $("#btnVerify").click(function () { return editor.btnCheckAll(); });
        $("#btnHammer").click(function () { return editor.btnPropDownAll(); });
        $("#btnReset").click(function () { return editor.btnResetAssertionsAll(false); });
        $("#btnResetQ").click(function () { return editor.btnResetAssertionsAll(true); });
        $("#btnE1").click(function () { return editor.loadEx1(); });
        editor.loadEx1();
    });
});
