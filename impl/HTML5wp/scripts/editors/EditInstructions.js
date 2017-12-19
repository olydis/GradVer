define(["require", "exports", "./EditStatement", "./EditableElement", "../runtime/Gamma", "../runtime/StackEnv", "../runtime/EvalEnv", "../runtime/EvalEnvVisu", "../types/VerificationFormulaGradual", "../types/VerificationFormula", "../types/ValueExpression"], function (require, exports, EditStatement_1, EditableElement_1, Gamma_1, StackEnv_1, EvalEnv_1, EvalEnvVisu_1, VerificationFormulaGradual_1, VerificationFormula_1, ValueExpression_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    function splitCell(left, right, cls) {
        if (cls === void 0) { cls = ""; }
        return $("<table>")
            .addClass(cls)
            .append($("<tr>")
            .append($("<td>").append(left))
            .append($("<td>").append(right)));
    }
    var EditInstructions = /** @class */ (function () {
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
                "// • the recursive data structure introduces ambiguous framing",
                "// • causing a (static) WLP to be undefined (no unique max. formula exists)",
                "// • play with imprecise casts or an imprecise postcondition to resolve",
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
                "assert (q.x = 1) * (q.y = 2);",
                "// { ? } this cast will overcome the syntax limitations of precise fomulas",
                "// ...without introducing any runtime checks or an imprecise method contract!"
            ]);
        };
        EditInstructions.prototype.loadEx3 = function () {
            this.setInstructions([
                "// ♦ Method call ♦",
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
                "q := p.swapXYweak();",
                "// • As a result, the following assertion cannot be proved statically",
                "assert (p.x = 3) * (p.y = 4) * (q.x = 4) * (q.y = 3);",
                "// • Gradualization to the rescue! Two choices:",
                "//     - use 'swapXYstrong', it has a gradual postcondition",
                "//     - gradualize the call site (introduce '?' via cast)"
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
                "int i0;",
                "Point p;",
                "p = new Point;",
                "p.x = i0;",
                "p.y = i0;",
                "assert acc(p.y) * (p.y = 0) * acc(p.x) * (p.x = 0)",
                "fc.bar(p);",
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
                "{ ? }",
                "p.x = i1;",
                "// nice try",
                "}",
                "assert acc(p.x)",
                "assert acc(p.y)",
            ]);
        };
        EditInstructions.prototype.loadEx7 = function () {
            this.setInstructions([
                "// some fun with the state visualization",
                "int i1;",
                "i1 = 1;",
                "int i2;",
                "i2 = 2;",
                "Point p;",
                "Point q;",
                "p = new Point;",
                "Points ps;",
                "ps = new Points;",
                "q := p.clone();",
                "ps.insertHere(q);",
                "p.x = i1;",
                "q := p.clone();",
                "ps.insertHere(q);",
                "p.y = i2;",
                "q := p.clone();",
                "ps.insertHere(q);",
                "p = null;",
                "q = null;",
            ]);
        };
        EditInstructions.prototype.loadEx8 = function () {
            this.setInstructions([
                "// `hold` as a scope",
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
        EditInstructions.prototype.displayDynCond = function (i, dyn) {
            // output
            var jqDyn = $("#ins" + i);
            if (dyn.length > 0 && jqDyn.text() == "")
                jqDyn.append($("<span>")
                    .addClass("dynCheck")
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
            $(".instructionStatement").removeClass("stmtFramed").removeClass("stmtUnframed");
            this.statements.forEach(function (s) { return s.stmtContainer.css("margin-left", "0px"); });
            this.verificationFormulas.forEach(function (s) { return s.parent().parent().parent().parent().css("margin-left", "0px"); });
            var statements = this.statements.map(function (x) { return x.getStatement(); });
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
            // static ver.
            var statRes = this.hoare.checkMethod(Gamma_1.GammaNew, statements, this.condPre, this.condPost);
            var failure = statRes.some(function (x) { return x.error != null; });
            // render static results
            //var stmtFramed = !this.condPre.gradual;
            for (var i = 0; i <= statements.length; ++i) {
                //$("#ins" + i).addClass(stmtFramed ? "stmtFramed" : "stmtUnframed");
                console.log(i + " " + JSON.stringify(statRes[i]));
                if (statRes[i].error != null)
                    $("#ins" + i).text(statRes[i].error).addClass("err");
                if (statRes[i].wlp != null)
                    this.displayPreCond(i, statRes[i].wlp);
                this.displayDynCond(i, statRes[i].residual);
            }
            // indentation
            for (var i = 0; i <= statements.length; ++i)
                this.verificationFormulas[i].parent().parent().parent().parent().css("margin-left", (statRes[i].scopeStack.length * 30) + "px");
            for (var i = 0; i < statements.length; ++i) {
                var indent = Math.min(statRes[i].scopeStack.length, statRes[i + 1].scopeStack.length);
                if (this.statements[i])
                    this.statements[i].stmtContainer.css("margin-left", (indent * 30) + "px");
            }
            var dynSuccess = !failure;
            for (var i = 0; dynSuccess && i <= statements.length; ++i) {
                dynSuccess = dynSuccess && statRes[i].residual.every(function (r) { return dynCheckDyn(r); });
                $("#ins" + i + " .dynCheck").addClass(dynSuccess ? "dynCheck1" : "dynCheck0");
                if (!dynSuccess) {
                    dynEnv = null;
                    this.displayDynState(i, null, statRes[i].g); // display BLOCKED
                    break;
                }
                if (i > 0) {
                    // step
                    dynStepOver(i);
                    if (dynEnv == null) {
                        $("#ins" + (i - 1)).text("dyn check failed within method call").addClass("err");
                        break;
                    }
                }
                this.displayDynState(i, dynEnv, statRes[i].g);
            }
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
                    if (i == 0) {
                        var tr = $("<tr>").appendTo(table);
                        tr.append($("<td>"));
                        tr.append($("<td>").append(splitCell($("<span>"), $("<span>").attr("id", "ins" + i).addClass("clearMe"), "splitStmtDyn")));
                    }
                    else {
                        var tr = $("<tr>").appendTo(table);
                        tr.append($("<td>").append(createButton("-").click(function () { return _this.removeInstruction(i - 1); })));
                        tr.append($("<td>").append(splitCell(_this.statements[i - 1]
                            .createHTML()
                            .keydown(function (eo) { if (eo.which == 13)
                            _this.selectInstruction(i); }), $("<span>").attr("id", "ins" + i).addClass("clearMe"), "splitStmtDyn")));
                    }
                    {
                        var tr = $("<tr>").appendTo(table);
                        tr.append($("<td>").append(createButton("+").click(function () { return _this.insertInstruction(i); })));
                        tr.append($("<td>").append(splitCell(_this.verificationFormulas[i], $("<span>").attr("id", "frm" + i).addClass("clearMe"), "splitStaticDynamic")).addClass("intermediateState"));
                    }
                })(i);
            this.analyze();
            //setTimeout(() => this.analyze(), 0);
        };
        return EditInstructions;
    }());
    exports.EditInstructions = EditInstructions;
});
