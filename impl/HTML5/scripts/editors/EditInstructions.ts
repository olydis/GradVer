import { EditStatement } from "./EditStatement";
import { EditVerificationFormula } from "./EditVerificationFormula";

import { Gamma, GammaNew } from "../runtime/Gamma";
import { Hoare } from "../runtime/Hoare";
import { GUIHelpers } from "../GUIHelpers";

import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual";
import { VerificationFormula } from "../types/VerificationFormula";

export class EditInstructions
{
    private statements: EditStatement[];
    private verificationFormulas: JQuery[];

    public loadEx1(): void
    {
        while (this.numInstructions > 5)
            this.removeInstruction(0);
        while (this.numInstructions < 5)
            this.insertInstruction(0);
        this.statements[0].setStatementX("int x;");
        this.statements[1].setStatementX("int y;");
        this.statements[2].setStatementX("y = 3;");
        this.statements[3].setStatementX("x = y;");
        this.statements[4].setStatementX("assert (x = 3);");
    }
    public loadEx2(): void
    {
        while (this.numInstructions > 5)
            this.removeInstruction(0);
        while (this.numInstructions < 5)
            this.insertInstruction(0);
        this.statements[0].setStatementX("int x;");
        this.statements[1].setStatementX("int y;");
        this.statements[2].setStatementX("y = 3;");
        this.statements[3].setStatementX("x = y;");
        this.statements[4].setStatementX("assert (x = 3);");
    }

    public get numInstructions(): number
    {
        return this.statements.length;
    }

    private createDynVerElement(): JQuery
    {
        return $("<span>").addClass("dynCheck");
    }

    private condPre: VerificationFormulaGradual;
    private condPost: VerificationFormulaGradual;

    public constructor(
        private container: JQuery,
        private hoare: Hoare
    )
    {
        this.condPre = VerificationFormulaGradual.create(true, VerificationFormula.empty());
        this.condPost = VerificationFormulaGradual.create(true, VerificationFormula.empty());

        this.statements = [];
        this.verificationFormulas = [];
        this.verificationFormulas.push(this.createDynVerElement());
        this.insertInstruction(0);

        this.updateGUI();
    }

    private displayDynCondition(i: number, dyn: VerificationFormula, cond: VerificationFormulaGradual): boolean
    {
        if (!dyn.satisfiable())
        {
            this.verificationFormulas[i].text("implication cannot hold").addClass("err");
            return false;
        }
        this.verificationFormulas[i].text("").append(cond.createHTML().text());
        if (dyn.createHTML().text() != "true")
            this.verificationFormulas[i].append($("<b style='font-weight: bold'>")
                .text("   +   " + dyn.createHTML().text()));
        
        return true;
    }

    private update(): void
    {
        // clear messages
        this.verificationFormulas.forEach(x => x.text(" ").removeClass("err").attr("title",null));

        var g = GammaNew;
        var cond = this.condPre;
        for (var i = 0; i < this.statements.length; ++i)
        {
            var s = this.statements[i].getStatement();
            var errs = this.hoare.check(s, cond, g);
            if (errs != null)
            {
                this.verificationFormulas[i].text(errs[0]).addClass("err");
                return;
            }

            var res = this.hoare.post(s, cond, g);
            if (!this.displayDynCondition(i, res.dyn, cond)) return;
            cond = res.post;
            g = res.postGamma;
        }

        var lastDyn = cond.impliesRuntime(this.condPost.staticFormula);
        if (!this.displayDynCondition(this.statements.length, lastDyn, cond)) return;
    }

    public updateConditions(pre: VerificationFormulaGradual, post: VerificationFormulaGradual): void
    {
        this.condPre = pre;
        this.condPost = post;
        this.update();
    }

    private removeInstruction(index: number): void
    {
        this.verificationFormulas.splice(index + 1, 1);
        this.statements.splice(index, 1);
        this.updateGUI();
    }

    private insertInstruction(index: number): void
    {
        this.verificationFormulas.splice(index + 1, 0, this.createDynVerElement());
        this.statements.splice(index, 0, new EditStatement(undefined, () => this.update()));
        this.updateGUI();
    }

    private updateGUI(): void
    {
        var createRightButton = (s: string) =>
            $("<span>")
                .addClass("rightFloat")
                .append($("<span>")
                    .addClass("button")
                    .addClass("buttonAutohide")
                    .text(s));

        this.container.text("");
        var n = this.numInstructions;
        for (var i = 0; i <= n; ++i)
            ((i: number) =>
            {
                this.container.append(createRightButton("+").click(() => this.insertInstruction(i)));
                this.container.append(this.verificationFormulas[i]);
                if (i != n)
                {
                    var ins = this.statements[i].createHTML();
                    this.container.append(createRightButton("-").click(() => this.removeInstruction(i)));
                    this.container.append(ins);
                }
            })(i);
        this.update();
    }
}