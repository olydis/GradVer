import { EditStatement } from "./EditStatement";
import { EditVerificationFormula } from "./EditVerificationFormula";

import { Gamma, GammaNew } from "../runtime/Gamma";
import { Hoare } from "../runtime/Hoare";
import { GUIHelpers } from "../GUIHelpers";

import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual";
import { VerificationFormula, FormulaPart } from "../types/VerificationFormula";

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
        while (this.numInstructions > 14)
            this.removeInstruction(0);
        while (this.numInstructions < 14)
            this.insertInstruction(0);
        this.statements[0].setStatementX("int i1;");
        this.statements[1].setStatementX("i1 := 1;");
        this.statements[2].setStatementX("int i2;");
        this.statements[3].setStatementX("i2 := 2;");
        this.statements[4].setStatementX("Point p;");
        this.statements[5].setStatementX("p = new Point;");
        this.statements[6].setStatementX("p.x = i1;");
        this.statements[7].setStatementX("p.y = i2;");
        this.statements[8].setStatementX("Points ps;");
        this.statements[9].setStatementX("ps = new Points;");
        this.statements[10].setStatementX("ps.h = p;");
        this.statements[11].setStatementX("ps.t = ps;");
        this.statements[12].setStatementX("Point q;");
        this.statements[13].setStatementX("q = ps.t.t.t.t.h;");
    }

    public get numInstructions(): number
    {
        return this.statements.length;
    }

    private createDynVerElement(): JQuery
    {
        return $("<span>").addClass("intermediateState");
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

    private displayPreCondition(i: number, dynF: VerificationFormula, cond: VerificationFormulaGradual): boolean
    {
        var condx = [cond.staticFormula];
        condx.push(...cond.staticFormula.autoFraming().map(x => x.asFormula()));
        var dyn = dynF.autoFramedChecks(condx);
        if (dyn.some(x => !x.satisfiable()))
        {
            throw "shouldn't have happened";
        }

        this.verificationFormulas[i].text("").append(cond.norm().toString());

        if (dyn.length > 0)
            this.verificationFormulas[i].append($("<span>")
                .addClass("dynCheck")
                .text(dyn.join(", ")));
        
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
            if (!cond.satisfiable())
            {
                this.verificationFormulas[i].text("pre-condition malformed: not satisfiable").addClass("err");
                return;
            }
            if (!cond.sfrm())
            {
                this.verificationFormulas[i].text("pre-condition malformed: not self-framed").addClass("err");
                return;
            }

            var s = this.statements[i].getStatement();
            var errs = this.hoare.check(s, cond, g);
            if (errs != null)
            {
                this.verificationFormulas[i].text(errs[0]).addClass("err");
                return;
            }

            var res = this.hoare.post(s, cond, g);
            if (!this.displayPreCondition(i, res.dyn, cond)) return;
            cond = res.post;
            g = res.postGamma;
        }

        var lastDyn = this.condPost.staticFormula;
        if (!this.displayPreCondition(this.statements.length, lastDyn, cond)) return;
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