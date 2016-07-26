import { EditableElement } from "./EditableElement";
import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual";

export class EditVerificationFormula extends EditableElement
{
    private formulaContainer: JQuery;
    private verForm: VerificationFormulaGradual;

    public constructor(
        initialSource: string = "",
        onChange: (verForm: VerificationFormulaGradual) => void = () => {}
    ) 
    {
        var formulaContainer = $("<span>");

        super(
            formulaContainer,
            initialSource,
            (source: string) => {
                this.verForm = new VerificationFormulaGradual(source);
                onChange(this.verForm);
                var html = this.verForm.createHTML();
                // if (!this.verForm.sfrm())
                //     html.addClass("errSfrm");
                // // DEBUG: normalized data
                // var phi = this.verForm.staticFormula;
                // if (!phi.satisfiable())
                //     html.addClass("errFalse");
                // // DEBUG end
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
            .append(this.formulaContainer)
            .click(eo => { 
                this.editBegin();
                eo.stopPropagation();
            });
    }

    public getFormula(): VerificationFormulaGradual { return this.verForm; }
    public setFormula(frm: VerificationFormulaGradual): void
    {
        this.verForm = frm;
        this.source = frm.createHTML().text();
        this.rerender();
    }
}