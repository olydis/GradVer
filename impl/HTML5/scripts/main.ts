import { EditInstructions } from "./editors/EditInstructions";
import { EditableElement } from "./editors/EditableElement";
import { ExecutionEnvironment } from "./runtime/ExecutionEnvironment";
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

    var editor = new EditInstructions(
        $("#codeContainer")
        //, hoare
    );
    $("#btnVerify").click(() => editor.btnCheckAll());
    $("#btnHammer").click(() => editor.btnPropDownAll());
    $("#btnReset").click(() => editor.btnResetAssertionsAll(false));
    $("#btnResetQ").click(() => editor.btnResetAssertionsAll(true));
    $("#btnE1").click(() => editor.loadEx1());
    editor.loadEx1();
});