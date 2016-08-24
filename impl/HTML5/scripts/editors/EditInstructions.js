define(["require", "exports", "./EditStatement", "./EditableElement", "../runtime/Gamma", "../runtime/StackEnv", "../runtime/EvalEnv", "../types/VerificationFormulaGradual", "../types/VerificationFormula", "../types/Statement", "../types/ValueExpression"], function (require, exports, EditStatement_1, EditableElement_1, Gamma_1, StackEnv_1, EvalEnv_1, VerificationFormulaGradual_1, VerificationFormula_1, Statement_1, ValueExpression_1) {
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
        EditInstructions.prototype.displayDynCond = function (i, cond, dynF, dynEnv, dynSuccess) {
            // dynamic check minimization
            var condClassic = cond.staticFormula.snorm();
            var condx = cond.staticFormula
                .autoFraming()
                .map(function (x) { return new VerificationFormula_1.VerificationFormula(null, [x].concat(condClassic.parts)); });
            condx.push(cond.staticFormula);
            var dyn = dynF.autoFramedChecks(condx);
            if (dyn.some(function (x) { return !x.satisfiable(); })) {
                throw "shouldn't have happened";
            }
            // output
            var jqDyn = $("#ins" + i);
            if (dyn.length > 0)
                jqDyn.append($("<span>")
                    .addClass("dynCheck")
                    .addClass(dynEnv != null ? (dynSuccess ? "dynCheck1" : "dynCheck0") : "")
                    .text(dyn.join(", ")));
        };
        EditInstructions.prototype.displayDynState = function (i, dynEnv) {
            var jqEnv = $("#frm" + i);
            if (dynEnv != null)
                jqEnv.text(EvalEnv_1.printEnv(StackEnv_1.topEnv(dynEnv)));
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
            var statements = this.statements.map(function (x) { return x.getStatement(); });
            statements.push(new Statement_1.StatementCast(this.condPost));
            var g = Gamma_1.GammaNew;
            var cond = this.condPre;
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
                this.displayPreCond(i, cond);
                this.displayDynState(i, dynEnv);
                if (!cond.satisfiable()) {
                    $("#ins" + i).text("pre-condition malformed: not satisfiable").addClass("err");
                    return;
                }
                if (!cond.sfrm()) {
                    $("#ins" + i).text("pre-condition malformed: not self-framed").addClass("err");
                    return;
                }
                var s = statements[i];
                var errs = this.hoare.check(s, cond, g, scopePostProcStack);
                if (errs != null) {
                    $("#ins" + i).text(errs[0]).addClass("err");
                    return;
                }
                var res = this.hoare.post(s, cond, g, scopePostProcStack);
                dynSuccess = dynSuccess && dynCheckDyn(res.dyn);
                this.displayDynCond(i, cond, res.dyn, dynEnv, dynSuccess);
                if (!dynSuccess)
                    dynEnv = null;
                cond = res.post;
                g = res.postGamma;
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
        };
        return EditInstructions;
    }());
    exports.EditInstructions = EditInstructions;
});
