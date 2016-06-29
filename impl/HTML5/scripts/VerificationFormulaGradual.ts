import { Editable } from "./Editable";
import { VerificationFormula } from "./VerificationFormula";

export class VerificationFormulaGradual implements Editable
{
    private html: JQuery;

    public gradual: boolean;
    public staticFormula: VerificationFormula;

    public constructor()
    {
        this.html = $("<span>");

        this.gradual = true;
        this.staticFormula = new VerificationFormula();
        this.updateHTML();
    }

    private updateHTML()
    {
        this.html.text("");
        var grad = $("<span>").text("?");
        if (!this.staticFormula.isEmpty())
            grad.append($("<span>").addClass("sepConj"));
        grad.addClass(this.gradual ? "vfGradOn" : "vfGradOff");
        this.html.append(grad);
        if (!this.gradual || !this.staticFormula.isEmpty())
            this.html.append(this.staticFormula.createHTML());
    }

    public createHTML(): JQuery
    {
        return this.html;
    }
}