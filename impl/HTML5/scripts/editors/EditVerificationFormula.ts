import { EditableElement } from "./EditableElement";
import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual";

export class EditVerificationFormula extends EditableElement
{
    private formulaContainer: JQuery;
    private verForm: VerificationFormulaGradual;

    public constructor(
        initialSource: string = ""
    ) 
    {
        var formulaContainer = $("<span>");

        super(
            formulaContainer,
            initialSource,
            (source: string) => {
                this.verForm = new VerificationFormulaGradual(source);
                var html = this.verForm.createHTML();
                return {
                    source: html.text(),
                    html: html
                };
            }
        );

        this.formulaContainer = formulaContainer;
    }

    public createHTML(): JQuery
    {
        return $("<p>")
            .addClass("clickable")
            .addClass("instructionVerForm")
            .append("{")
            .append(this.formulaContainer)
            .append("}")
            .click(eo => { 
                this.editBegin();
                eo.stopPropagation();
            });
    }
}