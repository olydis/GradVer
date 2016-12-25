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
            (source: string, tthis: EditVerificationFormula) => {
                tthis.verForm = new VerificationFormulaGradual(source);
                var src = tthis.verForm.toString()
                var html = $("<span>").text(src);
                // if (!tthis.verForm.sfrm())
                //     html.addClass("errSfrm");
                // // DEBUG: normalized data
                // var phi = tthis.verForm.staticFormula;
                // if (!phi.satisfiable())
                //     html.addClass("errFalse");
                // // DEBUG end
                return {
                    source: src,
                    html: html
                };
            },
            (tthis: EditVerificationFormula) => onChange(tthis.verForm)
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