import { Editable } from "./Editable";

abstract class FormulaPart implements Editable
{
    abstract createHTML(): JQuery;
}

class FormulaPartTrue extends FormulaPart
{
    public createHTML(): JQuery
    {
        return $("<span>").text("true");
    }
}

export class VerificationFormula implements Editable
{
    private html: JQuery;

    public parts: FormulaPart[];

    public constructor()
    {
        this.html = $("<span>");

        this.parts = [];
        this.updateHTML();
    }

    public isEmpty(): boolean
    {
        return this.parts.length == 0;
    }

    private updateHTML()
    {
        var parts = this.isEmpty() ? [new FormulaPartTrue()] : this.parts;
        this.html.text("");
        for (var i = 0; i < parts.length; ++i)
        {
            if (i > 0)
                this.html.append($("<span>").addClass("sepConj"));
            this.html.append(parts[i].createHTML());
        }
    }

    public createHTML(): JQuery
    {
        return this.html;
    }
}