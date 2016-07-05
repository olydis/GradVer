import { EditStatement } from "./EditStatement";
import { EditVerificationFormula } from "./EditVerificationFormula";

import { Hoare } from "./runtime/Hoare";
import { GUIHelpers } from "../GUIHelpers";

import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual";

export class EditInstructions
{
    private statements: EditStatement[];
    private verificationFormulas: EditVerificationFormula[];

    public get numInstructions(): number
    {
        return this.statements.length;
    }

    public constructor(
        private container: JQuery,
        private hoare: Hoare
    )
    {
        this.statements = [];
        this.verificationFormulas = [];
        this.verificationFormulas.push(new EditVerificationFormula());
        this.insertInstruction(0);
    }

    private removeInstruction(index: number): void
    {
        this.verificationFormulas.splice(index + 1, 1);
        this.statements.splice(index, 1);
        this.updateGUI();
    }

    private insertInstruction(index: number): void
    {
        this.verificationFormulas.splice(index + 1, 0, new EditVerificationFormula());
        this.statements.splice(index, 0, new EditStatement());
        this.updateGUI();
    }

    private checkStatement(index: number): string[]
    {
        var s = this.statements[index].getStatement();
        var pre = this.verificationFormulas[index].getFormula().staticFormula;
        var post = this.verificationFormulas[index + 1].getFormula().staticFormula;

        return this.hoare.validate(s, pre, post);
    }

    public btnCheckAll(): void
    {
        for (var i = 0; i < this.numInstructions; ++i)
            this.btnCheck(i);
    }

    public btnCheck(index: number): void
    {
        var ins = this.statements[index].stmtContainer;
        var errs = this.checkStatement(index);
        if (errs == null)
            GUIHelpers.flashCorrect(ins);
        else
            GUIHelpers.flashError(ins, errs[0]);
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
                if (i != 0)
                    this.container.append(createRightButton("↲").click(() => {
                        var stmt = this.statements[i - 1].getStatement();
                        var pre = this.verificationFormulas[i - 1].getFormula().staticFormula;
                        var post = this.verificationFormulas[i].getFormula().staticFormula;
                        var npost = this.hoare.genPost(stmt, pre, post);
                        this.verificationFormulas[i].setFormula(VerificationFormulaGradual.create(false, npost));
                    }));
                if (i != n)
                    this.container.append(createRightButton("↰").click(() => {
                        var stmt = this.statements[i].getStatement();
                        var pre = this.verificationFormulas[i].getFormula().staticFormula;
                        var post = this.verificationFormulas[i + 1].getFormula().staticFormula;
                        var npre = this.hoare.genPre(stmt, pre, post);
                        this.verificationFormulas[i].setFormula(VerificationFormulaGradual.create(false, npre));
                    }));
                this.container.append(this.verificationFormulas[i].createHTML());
                if (i != n)
                {
                    var ins = this.statements[i].createHTML();
                    this.container.append(createRightButton("-").click(() => this.removeInstruction(i)));
                    this.container.append(createRightButton("✓").click(() => {
                        this.btnCheck(i);
                    }));
                    // this.container.append(createRightButton("⇳").click(() => {

                    // }));
                    this.container.append(ins);
                }
            })(i);
    }
}