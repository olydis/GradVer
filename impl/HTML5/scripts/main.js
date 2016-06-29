define(["require", "exports", "./editors/EditInstructions", "./editors/EditableElement"], function (require, exports, EditInstructions_1, EditableElement_1) {
    "use strict";
    $(function () {
        $(window).click(function () { return EditableElement_1.EditableElement.editEndAll(); });
        var editor = new EditInstructions_1.EditInstructions($("#codeContainer"));
    });
});
