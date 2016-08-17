import { EditStatement } from "./EditStatement";
import { EditVerificationFormula } from "./EditVerificationFormula";
import { EditableElement } from "./EditableElement"; 

import { Gamma, GammaNew } from "../runtime/Gamma";
import { Hoare } from "../runtime/Hoare";
import { StackEnv, topEnv } from "../runtime/StackEnv";
import { printEnv } from "../runtime/EvalEnv";
import { GUIHelpers } from "../GUIHelpers";

import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual";
import { VerificationFormula, FormulaPart } from "../types/VerificationFormula";
import { Statement, StatementCast } from "../types/Statement";

export class EditInstructions
{
    private statements: EditStatement[];
    private verificationFormulas: JQuery[];

    private setNumInstructions(n: number): void
    {
        while (this.numInstructions > n)
            this.removeInstruction(0, false);
        while (this.numInstructions < n)
            this.insertInstruction(0, false);
        this.updateGUI();
    }
    private setInstructions(s: string[]): void
    {
        EditableElement.editEndAll();

        this.setNumInstructions(s.length);
        for (var i = 0; i < s.length; ++i)
            this.statements[i].setStatementX(s[i]);
    }

    public loadEx1(): void
    {
        this.setInstructions([
            "int x;",
            "int y;",
            "y = 3;",
            "x = y;",
            "assert (x = 3);"
        ]);
    }
    public loadEx2(): void
    {
        this.setInstructions([
            "int i1;",
            "i1 := 1;",
            "int i2;",
            "i2 := 2;",
            "Point p;",
            "p = new Point;",
            "p.x = i1;",
            "p.y = i2;",
            "Points ps;",
            "ps = new Points;",
            "ps.h = p;",
            "ps.t = ps;",
            "Point q;",
            "q = ps.t.t.t.t.h;",
            "assert (q.x = 1) * (q.y = 2);"
        ]);
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

    private displayPreCond(
        i: number, 
        cond: VerificationFormulaGradual): void
    {
        this.verificationFormulas[i].text("").append(cond.norm().toString());
    }
    private displayDynCond(
        i: number, 
        cond: VerificationFormulaGradual, 
        dynF: VerificationFormula,
        dynEnv: StackEnv, 
        dynSuccess: boolean): void
    {
        // dynamic check minimization
        var condClassic = cond.staticFormula.snorm();
        var condx = cond.staticFormula
            .autoFraming()
            .map(x => new VerificationFormula(null, (<FormulaPart[]>[x]).concat(condClassic.parts)));
        condx.push(cond.staticFormula);
        var dyn = dynF.autoFramedChecks(condx);
        if (dyn.some(x => !x.satisfiable()))
        {
            throw "shouldn't have happened";
        }

        // output
        var jqDyn = $("#ins" + i);
        if (dyn.length > 0)
            jqDyn.append($("<span>")
                .addClass("dynCheck")
                .addClass(dynEnv != null ? (dynSuccess ? "dynCheck1" : "dynCheck0") : "")
                .text(dyn.join(", ")));
    }

    private displayDynState(
        i: number, 
        dynEnv: StackEnv
        ): void
    {
        var jqEnv = $("#frm" + i);

        if (dynEnv != null)
            jqEnv.append($("<span>")
                .addClass("dynEnv")
                .text(printEnv(topEnv(dynEnv))));
        else
            jqEnv.append($("<span>")
                .addClass("dynEnv")
                .text("BLOCKED"));
    }

    private analyze(): void
    {
        // clear messages
        this.verificationFormulas.forEach(x => x.text("").removeClass("err").attr("title", null));
        $(".clearMe").text("");

        var statements = this.statements.map(x => x.getStatement());
        statements.push(new StatementCast(this.condPost));

        var g = GammaNew;
        var cond = this.condPre;

        var dynEnv: StackEnv = { H: {}, S: [{ r: {}, A: [], ss: statements }] };
        var dynEnvNextStmt: () => Statement = () => dynEnv.S.map(x => x.ss).filter(x => x.length > 0)[0][0];
        var dynStepInto: () => void = () => { dynEnv = dynEnv == null ? null : dynEnvNextStmt().smallStep(dynEnv, this.hoare.env); };
        var dynStepOver: () => void = () => { dynStepInto(); while (dynEnv != null && dynEnv.S.length > 1) dynStepInto(); };
        var dynCheckDyn: (frm: VerificationFormula) => boolean = frm => dynEnv != null && frm.eval(topEnv(dynEnv));
        var dynSuccess = true;

        for (var i = 0; i < statements.length; ++i)
        {
            this.displayPreCond(i, cond);
            this.displayDynState(i, dynEnv);

            if (!cond.satisfiable())
            {
                $("#frm" + i).text("pre-condition malformed: not satisfiable").addClass("err");
                return;
            }
            if (!cond.sfrm())
            {
                $("#frm" + i).text("pre-condition malformed: not self-framed").addClass("err");
                return;
            }

            var s = statements[i];
            var errs = this.hoare.check(s, cond, g);
            if (errs != null)
            {
                $("#ins" + i).text(errs[0]).addClass("err");
                return;
            }

            var res = this.hoare.post(s, cond, g);
            this.displayDynCond(i, cond, res.dyn, dynEnv, dynSuccess = dynSuccess && dynCheckDyn(res.dyn));
            cond = res.post;
            g = res.postGamma;

            // dyn
            dynStepOver();
            if (dynSuccess && dynEnv == null)
                throw "progress broke";
            if (dynSuccess && dynEnv != null && !cond.eval(topEnv(dynEnv)))
                throw "preservation broke";
        }
    }

    public updateConditions(pre: VerificationFormulaGradual, post: VerificationFormulaGradual): void
    {
        this.condPre = pre;
        this.condPost = post;
        this.analyze();
    }

    private removeInstruction(index: number, update: boolean = true): void
    {
        this.verificationFormulas.splice(index + 1, 1);
        this.statements.splice(index, 1);
        if (update)
            this.updateGUI();
    }

    private insertInstruction(index: number, update: boolean = true): void
    {
        this.verificationFormulas.splice(index + 1, 0, this.createDynVerElement());
        this.statements.splice(index, 0, new EditStatement(undefined, () => this.analyze()));
        if (update)
            this.updateGUI();
    }

    private updateGUI(): void
    {
        var createButton = (s: string) =>
            $("<span>")
                    .addClass("button")
                    .addClass("buttonAutohide")
                    .text(s);

        this.container.text("");

        var table = $("<table>")
            .addClass("instructionTable")
            .appendTo(this.container);

        var n = this.numInstructions;
        for (var i = 0; i <= n; ++i)
            ((i: number) =>
            {
                {
                    var tr = $("<tr>").appendTo(table);
                    tr.append($("<td>").append(
                        this.verificationFormulas[i]));
                    tr.append($("<td>").attr("id", "frm" + i).addClass("clearMe"));
                    tr.append($("<td>").append(
                        createButton("+").click(() => this.insertInstruction(i))));
                }
                if (i != n)
                {
                    var tr = $("<tr>").appendTo(table);
                    tr.append($("<td>").append(
                        this.statements[i].createHTML()));
                    tr.append($("<td>").attr("id", "ins" + i).addClass("clearMe"));
                    tr.append($("<td>").append(
                        createButton("-").click(() => this.removeInstruction(i))));
                }
                else
                {
                    var tr = $("<tr>").appendTo(table);
                    tr.append($("<td>"));
                    tr.append($("<td>").attr("id", "ins" + i).addClass("clearMe"));
                    tr.append($("<td>"));
                }
            })(i);
        this.analyze();
    }
}