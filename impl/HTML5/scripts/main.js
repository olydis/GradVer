define(["require", "exports", "./editors/EditInstructions", "./editors/EditableElement", "./runtime/ExecutionEnvironment", "./runtime/Hoare"], function (require, exports, EditInstructions_1, EditableElement_1, ExecutionEnvironment_1, Hoare_1) {
    "use strict";
    window.onerror = function (err) { return alert(JSON.stringify(err)); };
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
    });
});
