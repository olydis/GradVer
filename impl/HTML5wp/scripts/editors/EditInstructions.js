define(["require", "exports", "./EditStatement", "./EditableElement", "../runtime/Gamma", "../runtime/StackEnv", "../runtime/EvalEnv", "../runtime/EvalEnvVisu", "../types/VerificationFormulaGradual", "../types/VerificationFormula", "../types/Statement", "../types/ValueExpression"], function (require, exports, EditStatement_1, EditableElement_1, Gamma_1, StackEnv_1, EvalEnv_1, EvalEnvVisu_1, VerificationFormulaGradual_1, VerificationFormula_1, Statement_1, ValueExpression_1) {
    "use strict";
    function splitCell(left, right, cls) {
        if (cls === void 0) { cls = ""; }
        return $("<table>")
            .addClass(cls)
            .append($("<tr>")
            .append($("<td>").append(left))
            .append($("<td>").append(right)));
    }
    var EditInstructions = (function () {
        function EditInstructions(container, hoare) {
            this.container = container;
            this.hoare = hoare;
            this.suppressAnalysis = false;
            this.condPre = VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, VerificationFormula_1.VerificationFormula.empty());
            this.condPost = VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, VerificationFormula_1.VerificationFormula.empty());
            this.statements = [];
            this.verificationFormulas = [];
            this.verificationFormulas.push(this.createDynVerElement());
            this.insertInstruction(0);
            this.updateGUI();
        }
        EditInstructions.prototype.setNumInstructions = function (n) {
            while (this.numInstructions > n)
                this.removeInstruction(0, false);
            while (this.numInstructions < n)
                this.insertInstruction(0, false);
        };
        EditInstructions.prototype.setInstructions = function (s) {
            this.suppressAnalysis = true;
            {
                EditableElement_1.EditableElement.editEndAll();
                this.setNumInstructions(s.length);
                for (var i = 0; i < s.length; ++i)
                    this.statements[i].setStatementX(s[i]);
            }
            this.suppressAnalysis = false;
            this.updateGUI();
        };
        EditInstructions.prototype.loadEx0 = function () {
            this.setInstructions([
                ""
            ]);
        };
        EditInstructions.prototype.loadEx1 = function () {
            this.setInstructions([
                "// ♦ Basics ♦",
                "// • Can you change the assertion in order to make static|dynamic checks fail?",
                "int x;",
                "int y;",
                "y = 3;",
                "x = y;",
                "assert (x = 3);"
            ]);
        };
        EditInstructions.prototype.loadEx2 = function () {
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
        };
        EditInstructions.prototype.loadEx3 = function () {
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
        };
        EditInstructions.prototype.loadEx4 = function () {
            this.setInstructions([
                "// ♦ Casts ♦",
                "int a;",
                "a := 43;",
                "// • comment the following in to convert static to dynamic failure:",
                "// { ? }",
                "assert (a = 42);",
            ]);
        };
        EditInstructions.prototype.loadEx5 = function () {
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
        };
        EditInstructions.prototype.loadEx6 = function () {
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
        };
        EditInstructions.prototype.loadEx7 = function () {
            this.setInstructions([
                "int i1;",
                "i1 = 1;",
                "int i2;",
                "i2 = 2;",
                "Point p;",
                "Point q;",
                "p = new Point;",
                "void _;",
                "Points ps;",
                "ps = new Points;",
                "q := p.clone(_);",
                "_ = ps.insertHere(q);",
                "p.x = i1;",
                "q := p.clone(_);",
                "_ = ps.insertHere(q);",
                "p.y = i2;",
                "q := p.clone(_);",
                "_ = ps.insertHere(q);",
                "p = null;",
                "q = null;",
            ]);
        };
        EditInstructions.prototype.loadEx8 = function () {
            this.setInstructions([
                "Point p;",
                "hold true {",
                "p := new Point;",
                "int temp;",
                "temp := 1;",
                "p.x := temp;",
                "temp := 2;",
                "p.y := temp;",
                "}",
                "assert (p.x = 1) * (p.y = 2);",
            ]);
        };
        Object.defineProperty(EditInstructions.prototype, "numInstructions", {
            get: function () {
                return this.statements.length;
            },
            enumerable: true,
            configurable: true
        });
        EditInstructions.prototype.createDynVerElement = function () {
            return $("<span>");
        };
        EditInstructions.prototype.displayPreCond = function (i, cond) {
            this.verificationFormulas[i].text("").append(cond.norm().toString());
        };
        EditInstructions.prototype.displayDynCond = function (i, cond, dyn, dynEnv, dynSuccess) {
            // output
            var jqDyn = $("#ins" + i);
            if (dyn.length > 0)
                jqDyn.append($("<span>")
                    .addClass("dynCheck")
                    .addClass(dynEnv != null ? (dynSuccess ? "dynCheck1" : "dynCheck0") : "")
                    .text(dyn.join(", ")));
        };
        EditInstructions.prototype.displayDynState = function (i, dynEnv, gamma) {
            var jqEnv = $("#frm" + i);
            if (dynEnv != null) {
                var top = StackEnv_1.topEnv(dynEnv);
                jqEnv.text(EvalEnv_1.printEnv(top));
                jqEnv.parents(".intermediateState").on("mouseenter", function (eo) {
                    return EvalEnvVisu_1.showAt({ x: eo.clientX, y: eo.clientY }, top, gamma);
                });
            }
            else
                jqEnv.text("BLOCKED");
        };
        EditInstructions.prototype.analyze = function () {
            var _this = this;
            if (this.suppressAnalysis)
                return;
            ValueExpression_1.ValueObject.reset();
            // clear messages
            this.verificationFormulas.forEach(function (x) { return x.text("").attr("title", null); });
            $(".clearMe").text("");
            $(".err").removeClass("err");
            $(".intermediateState").off("mouseenter");
            $(".intermediateState").off("mouseleave").on("mouseleave", function () { return EvalEnvVisu_1.hide(); });
            this.statements.forEach(function (s) { return s.stmtContainer.css("margin-left", "0px"); });
            var statements = this.statements.map(function (x) { return x.getStatement(); });
            var statRes = this.hoare.checkMethod(Gamma_1.GammaNew, statements, this.condPre, this.condPost);
            // errs
            statRes.forEach(function (sr) { return sr.error = sr.error != null ? sr.error :
                (sr.wlp == null ? "instruction cannot meet postcondition" :
                    (sr.residual == null ? "should not have happened" : null)); });
            statements.push(new Statement_1.StatementCast(this.condPost));
            var pivotEnv;
            {
                var nenv = this.condPre.createNormalizedEnv();
                if (nenv)
                    pivotEnv = this.condPre.createNormalizedEnv().getPivotEnv();
                else
                    pivotEnv = { H: {}, r: {}, A: [] };
            }
            var dynEnv = { H: pivotEnv.H, S: [{ r: pivotEnv.r, A: pivotEnv.A, ss: statements }] };
            var dynEnvNextStmt = function () { return dynEnv.S.map(function (x) { return x.ss; }).reverse().filter(function (x) { return x.length > 0; }).concat([[null]])[0][0]; };
            var dynStepInto = function (untilIdxEx) {
                if (dynEnv == null)
                    return false;
                var stmt = dynEnvNextStmt();
                if (stmt == null)
                    return false;
                if (stmt == statements[untilIdxEx])
                    return false;
                //console.log("State: ", printEnv(topEnv(dynEnv)));
                //console.log("Statement: ", stmt + "");
                dynEnv = stmt.smallStep(dynEnv, _this.hoare.env);
                return true;
            };
            var dynStepOver = function (untilIdxEx) { while (dynStepInto(untilIdxEx))
                ; };
            var dynCheckDyn = function (frm) { return dynEnv != null && frm.eval(StackEnv_1.topEnv(dynEnv)); };
            var dynSuccess = true;
            var scopePostProcStack = [];
            for (var i = 0; i < statements.length; ++i) {
                console.log(JSON.stringify(statRes[i]));
                if (statRes[i].error != null) {
                    $("#ins" + i).text(statRes[i].error).addClass("err");
                    continue;
                }
                var cond = statRes[i].wlp;
                this.displayPreCond(i, cond);
                this.displayDynState(i, dynEnv, statRes[i].g);
                if (!cond.satisfiable()) {
                    $("#ins" + i).text("pre-condition malformed: not satisfiable").addClass("err");
                    return;
                }
                if (!cond.sfrm()) {
                    $("#ins" + i).text("pre-condition malformed: not self-framed").addClass("err");
                    return;
                }
                var indent = scopePostProcStack.length;
                var res = statRes[i].residual; //this.hoare.post(s, cond, g, scopePostProcStack);
                indent = Math.min(indent, scopePostProcStack.length);
                dynSuccess = dynSuccess && res.every(function (r) { return dynCheckDyn(r); });
                this.displayDynCond(i, cond, res, dynEnv, dynSuccess);
                if (!dynSuccess)
                    dynEnv = null;
                if (this.statements[i])
                    this.statements[i].stmtContainer.css("margin-left", (indent * 30) + "px");
                // dyn
                dynStepOver(i + 1);
                if (dynSuccess && dynEnv == null) {
                    $("#ins" + i).text("dynCheck failed within method call").addClass("err");
                    dynSuccess = false;
                }
                if (dynSuccess && dynEnv != null && !cond.eval(StackEnv_1.topEnv(dynEnv)))
                    throw "preservation broke";
            }
            if (scopePostProcStack.length != 0)
                $("#ins" + this.statements.length).text("close scope").addClass("err");
        };
        EditInstructions.prototype.updateConditions = function (pre, post) {
            this.condPre = pre;
            this.condPost = post;
            this.analyze();
        };
        EditInstructions.prototype.removeInstruction = function (index, update) {
            if (update === void 0) { update = true; }
            this.verificationFormulas.splice(index + 1, 1);
            this.statements.splice(index, 1);
            if (update)
                this.updateGUI();
        };
        EditInstructions.prototype.insertInstruction = function (index, update) {
            var _this = this;
            if (update === void 0) { update = true; }
            this.verificationFormulas.splice(index + 1, 0, this.createDynVerElement());
            this.statements.splice(index, 0, new EditStatement_1.EditStatement(undefined, function () { return _this.analyze(); }));
            if (update)
                this.updateGUI();
        };
        EditInstructions.prototype.selectInstruction = function (index) {
            while (index >= this.statements.length)
                this.insertInstruction(this.statements.length);
            this.statements[index].editBegin();
        };
        EditInstructions.prototype.updateGUI = function () {
            var _this = this;
            var createButton = function (s) {
                return $("<span>")
                    .addClass("button")
                    .addClass("buttonAutohide")
                    .text(s);
            };
            this.container.text("");
            var table = $("<table>")
                .addClass("instructionTable")
                .appendTo(this.container);
            var n = this.numInstructions;
            for (var i = 0; i <= n; ++i)
                (function (i) {
                    {
                        var tr = $("<tr>").appendTo(table);
                        tr.append($("<td>").append(createButton("+").click(function () { return _this.insertInstruction(i); })));
                        tr.append($("<td>").append(splitCell(_this.verificationFormulas[i], $("<span>").attr("id", "frm" + i).addClass("clearMe"), "splitStaticDynamic")).addClass("intermediateState"));
                    }
                    if (i != n) {
                        var tr = $("<tr>").appendTo(table);
                        tr.append($("<td>").append(createButton("-").click(function () { return _this.removeInstruction(i); })));
                        tr.append($("<td>").append(splitCell(_this.statements[i]
                            .createHTML()
                            .keydown(function (eo) { if (eo.which == 13)
                            _this.selectInstruction(i + 1); }), $("<span>").attr("id", "ins" + i).addClass("clearMe"), "splitStmtDyn")));
                    }
                    else {
                        var tr = $("<tr>").appendTo(table);
                        tr.append($("<td>"));
                        tr.append($("<td>").append(splitCell($("<span>"), $("<span>").attr("id", "ins" + i).addClass("clearMe"), "splitStmtDyn")));
                    }
                })(i);
            this.analyze();
            //setTimeout(() => this.analyze(), 0);
        };
        return EditInstructions;
    }());
    exports.EditInstructions = EditInstructions;
});
