import { EditStatement } from "./EditStatement";
import { EditVerificationFormula } from "./EditVerificationFormula";

import { Hoare } from "./runtime/Hoare";
import { GUIHelpers } from "../GUIHelpers";

import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual";
import { VerificationFormula } from "../types/VerificationFormula";

export class EditInstructions
{
    private statements: EditStatement[];
    private verificationFormulas: EditVerificationFormula[];

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

    private checkStatement(index: number): { errs: string[], runtimeCheck: VerificationFormula }
    {
        var s = this.statements[index].getStatement();
        var pre = this.verificationFormulas[index].getFormula();
        var post = this.verificationFormulas[index + 1].getFormula();

        return this.hoare.validate(s, pre, post);
    }

    public btnCheckAll(): void
    {
        for (var i = 0; i < this.numInstructions; ++i)
            this.btnCheck(i);
    }
    public btnCheck(index: number): boolean
    {
        var ins = this.statements[index].stmtContainer;
        var { errs, runtimeCheck } = this.checkStatement(index);
        if (errs == null)
            GUIHelpers.flashCorrect(ins/*, runtimeCheck.createHTML().text()*/);
        else
            GUIHelpers.flashError(ins, errs[0]);
        return errs == null;
    }

    public btnPropDownAll(): void
    {
        for (var i = 0; i < this.numInstructions; ++i)
            this.btnPropDown(i);
    }
    public btnPropDown(index: number): void
    {
        var stmt = this.statements[index].getStatement();
        var pre = this.verificationFormulas[index].getFormula();
        var post = this.verificationFormulas[index + 1].getFormula();
        var npost = this.hoare.genPost(stmt, pre, post);
        this.verificationFormulas[index + 1].setFormula(npost);
    }

    public btnResetAssertionsAll(grad: boolean): void
    {
        for (var i = 0; i <= this.numInstructions; ++i)
            this.btnResetAssertions(grad, i);
    }
    public btnResetAssertions(grad: boolean, index: number): void
    {
        this.verificationFormulas[index].setFormula(VerificationFormulaGradual.create(grad, new VerificationFormula()));
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
                    this.container.append(createRightButton("↲").click(() => this.btnPropDown(i - 1)));
                if (i != n)
                    this.container.append(createRightButton("↰").click(() => {
                        var stmt = this.statements[i].getStatement();
                        var pre = this.verificationFormulas[i].getFormula();
                        var post = this.verificationFormulas[i + 1].getFormula();
                        var npre = this.hoare.genPre(stmt, pre, post);
                        this.verificationFormulas[i].setFormula(npre);
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