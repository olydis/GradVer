import { EditStatement } from "./EditStatement";
import { EditVerificationFormula } from "./EditVerificationFormula";
import { EditableElement } from "./EditableElement"; 

import { Gamma, GammaNew } from "../runtime/Gamma";
import { Hoare } from "../runtime/Hoare";
import { StackEnv, topEnv } from "../runtime/StackEnv";
import { EvalEnv, printEnv } from "../runtime/EvalEnv";
import { GUIHelpers } from "../GUIHelpers";

import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual";
import { VerificationFormula, FormulaPart } from "../types/VerificationFormula";
import { Statement, StatementCast } from "../types/Statement";

import { ValueObject } from "../types/ValueExpression";

function splitCell(left: JQuery, right: JQuery, cls: string = ""): JQuery
{
    return $("<table>")
        .addClass(cls)
        .append($("<tr>")
            .append($("<td>").append(left))
            .append($("<td>").append(right)));
}

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
    }
    private setInstructions(s: string[]): void
    {
        this.suppressAnalysis = true;
        {
            EditableElement.editEndAll();

            this.setNumInstructions(s.length);
            for (var i = 0; i < s.length; ++i)
                this.statements[i].setStatementX(s[i]);
        }
        this.suppressAnalysis = false;
        this.updateGUI();
    }

    public loadEx0(): void
    {
        this.setInstructions([
            ""
        ]);
    }
    public loadEx1(): void
    {
        this.setInstructions([
            "// ♦ Basics ♦",
            "// • Can you change the assertion in order to make static|dynamic checks fail?",
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
            "// ♦ Fun with infinite linked list ♦",
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
    public loadEx3(): void
    {
        this.setInstructions([
            "// ♦ Method call ♦",
            "void v;",
            "int x;",
            "int y;",
            "x := 3;",
            "y := 4;",
            "Point p;",
            "p := new Point;",
            "p.x := x;",
            "p.y := y;",
            "Point q;",
            "// • Due to syntax limitations, 'swapXYweak' has a weak static postcondition",
            "q := p.swapXYweak(v);",
            "// • As a result, the following assertion cannot be proved statically",
            "assert (p.x = 3) * (p.y = 4) * (q.x = 4) * (q.y = 3);",
            "// • Gradualization to the rescue! Two choices:",
            "//     - use 'swapXYstrong', it has a gradual postcondition",
            "//     - gradualize the call site (introduce '?' via cast or as precondition)"
        ]);
    }
    public loadEx4(): void
    {
        this.setInstructions([
            "// ♦ Casts ♦",
            "int a;",
            "a := 43;",
            "// • comment the following in to convert static to dynamic failure:",
            "// { ? }",
            "assert (a = 42);",
        ]);
    }
    public loadEx5(): void
    {
        this.setInstructions([
            "FramingChallenge fc;",
            "fc = new FramingChallenge;",
            "void _;",
            "int i0;",
            "Point p;",
            "p = new Point;",
            "p.x = i0;",
            "p.y = i0;",
            "assert acc(p.y) * (p.y = 0) * acc(p.x) * (p.x = 0)",
            "_ = fc.bar(p);",
            "assert acc(p.y) * (p.y = 0)",
        ]);
    }
    public loadEx6(): void
    {
        this.setInstructions([
            "int i1;",
            "i1 = 1;",
            "Point p;",
            "p = new Point;",
            "hold acc(p.x) {",
            "p.y = i1;",
            "{ ? }",
            "}",
            "assert acc(p.x)",
            "assert acc(p.y)",
        ]);
    }

    public get numInstructions(): number
    {
        return this.statements.length;
    }

    private createDynVerElement(): JQuery
    {
        return $("<span>");
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
            jqEnv.text(printEnv(topEnv(dynEnv)));
        else
            jqEnv.text("BLOCKED");
    }

    private suppressAnalysis: boolean = false;
    private analyze(): void
    {
        if (this.suppressAnalysis)
            return;

        ValueObject.reset();

        // clear messages
        this.verificationFormulas.forEach(x => x.text("").attr("title", null));
        $(".clearMe").text("");
        $(".err").removeClass("err");

        var statements = this.statements.map(x => x.getStatement());
        statements.push(new StatementCast(this.condPost));

        var g = GammaNew;
        var cond = this.condPre;

        var pivotEnv: EvalEnv;
        {
            var nenv = this.condPre.createNormalizedEnv();
            if (nenv)
                pivotEnv = this.condPre.createNormalizedEnv().getPivotEnv();
            else
                pivotEnv = { H: {}, r: {}, A: [] };
        }
        var dynEnv: StackEnv = { H: pivotEnv.H, S: [{ r: pivotEnv.r, A: pivotEnv.A, ss: statements }] };
        var dynEnvNextStmt: () => Statement = () => dynEnv.S.map(x => x.ss).reverse().filter(x => x.length > 0).concat([[null]])[0][0];
        var dynStepInto: (untilIdxEx: number) => void = (untilIdxEx) => 
        {
            if (dynEnv == null)
                return false;
            var stmt = dynEnvNextStmt();
            if (stmt == null)
                return false;

            if (stmt == statements[untilIdxEx])
                return false;

            //console.log("State: ", printEnv(topEnv(dynEnv)));
            //console.log("Statement: ", stmt + "");
            dynEnv = stmt.smallStep(dynEnv, this.hoare.env);
            return true;
        };
        var dynStepOver: (untilIdxEx: number) => void = (untilIdxEx) => { while (dynStepInto(untilIdxEx)) ; };
        var dynCheckDyn: (frm: VerificationFormula) => boolean = frm => dynEnv != null && frm.eval(topEnv(dynEnv));
        var dynSuccess = true;

        var scopePostProcStack: any[] = [];

        for (var i = 0; i < statements.length; ++i)
        {
            this.displayPreCond(i, cond);
            this.displayDynState(i, dynEnv);

            if (!cond.satisfiable())
            {
                $("#ins" + i).text("pre-condition malformed: not satisfiable").addClass("err");
                return;
            }
            if (!cond.sfrm())
            {
                $("#ins" + i).text("pre-condition malformed: not self-framed").addClass("err");
                return;
            }

            var s = statements[i];
            var errs = this.hoare.check(s, cond, g, scopePostProcStack);
            if (errs != null)
            {
                $("#ins" + i).text(errs[0]).addClass("err");
                return;
            }

            var indent = scopePostProcStack.length;
            var res = this.hoare.post(s, cond, g, scopePostProcStack);
            indent = Math.min(indent, scopePostProcStack.length);
            dynSuccess = dynSuccess && dynCheckDyn(res.dyn);
            this.displayDynCond(i, cond, res.dyn, dynEnv, dynSuccess);
            if (!dynSuccess)
                dynEnv = null;

            cond = res.post;
            g = res.postGamma;

            if (this.statements[i])
                this.statements[i].stmtContainer.css("margin-left", (indent * 30) + "px");

            // dyn
            dynStepOver(i + 1);
            if (dynSuccess && dynEnv == null)
            {
                $("#ins" + i).text("dynCheck failed within method call").addClass("err");
                dynSuccess = false
            }
            if (dynSuccess && dynEnv != null && !cond.eval(topEnv(dynEnv)))
                throw "preservation broke";
        }

        if (scopePostProcStack.length != 0)
            $("#ins" + this.statements.length).text("close scope").addClass("err");
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

    private selectInstruction(index: number): void
    {
        while (index >= this.statements.length)
            this.insertInstruction(this.statements.length);
        this.statements[index].editBegin();
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
                        createButton("+").click(() => this.insertInstruction(i))));
                    tr.append($("<td>").append(
                        splitCell(
                            this.verificationFormulas[i], 
                            $("<span>").attr("id", "frm" + i).addClass("clearMe"), 
                            "splitStaticDynamic")
                        ).addClass("intermediateState"));
                }
                if (i != n)
                {
                    var tr = $("<tr>").appendTo(table);

                    tr.append($("<td>").append(
                        createButton("-").click(() => this.removeInstruction(i))));
                    tr.append($("<td>").append(
                        splitCell(
                            this.statements[i]
                                .createHTML()
                                .keydown(eo => { if (eo.which == 13) this.selectInstruction(i + 1); }), 
                            $("<span>").attr("id", "ins" + i).addClass("clearMe"), 
                            "splitStmtDyn")
                        ));
                }
                else
                {
                    var tr = $("<tr>").appendTo(table);

                    tr.append($("<td>"));
                    tr.append($("<td>").append(
                        splitCell(
                            $("<span>"), 
                            $("<span>").attr("id", "ins" + i).addClass("clearMe"), 
                            "splitStmtDyn")
                        ));
                }
            })(i);
        this.analyze();
    }
}