import { Editable } from "./Editable";
import { VerificationFormula } from "./VerificationFormula";
import { VerificationFormulaGradual } from "./VerificationFormulaGradual";

export class EditVerificationFormula implements Editable
{
    public constructor(
        private verForm: VerificationFormulaGradual = new VerificationFormulaGradual()
    ) 
    {
    }

    public createHTML(): JQuery
    {
        var container = $("<span>")
            .addClass("instructionVerForm");
        container.append("{");
        container.append(this.verForm.createHTML());
        container.append("}");
        return container;
    }
}