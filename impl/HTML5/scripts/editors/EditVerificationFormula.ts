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
                var src = this.verForm.toString()
                var html = $("<span>").text(src);
                // if (!this.verForm.sfrm())
                //     html.addClass("errSfrm");
                // // DEBUG: normalized data
                // var phi = this.verForm.staticFormula;
                // if (!phi.satisfiable())
                //     html.addClass("errFalse");
                // // DEBUG end
                return {
                    source: src,
                    html: html
                };
            },
            () => onChange(this.verForm)
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
        this.source = frm.toString();
        this.rerender();
    }
}