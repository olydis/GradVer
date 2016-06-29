import { EditInstructions } from "./editors/EditInstructions";
import { EditableElement } from "./editors/EditableElement";

$(() =>
{
    $(window).click(() => EditableElement.editEndAll());
    var editor = new EditInstructions($("#codeContainer"));
});