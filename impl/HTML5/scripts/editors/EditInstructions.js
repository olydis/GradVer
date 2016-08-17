define(["require", "exports", "./EditStatement", "./EditableElement", "../runtime/Gamma", "../runtime/StackEnv", "../runtime/EvalEnv", "../types/VerificationFormulaGradual", "../types/VerificationFormula", "../types/Statement"], function (require, exports, EditStatement_1, EditableElement_1, Gamma_1, StackEnv_1, EvalEnv_1, VerificationFormulaGradual_1, VerificationFormula_1, Statement_1) {
    "use strict";
    var EditInstructions = (function () {
        function EditInstructions(container, hoare) {
            this.container = container;
            this.hoare = hoare;
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
            this.updateGUI();
        };
        EditInstructions.prototype.setInstructions = function (s) {
            EditableElement_1.EditableElement.editEndAll();
            this.setNumInstructions(s.length);
            for (var i = 0; i < s.length; ++i)
                this.statements[i].setStatementX(s[i]);
        };
        EditInstructions.prototype.loadEx1 = function () {
            this.setInstructions([
                "int x;",
                "int y;",
                "y = 3;",
                "x = y;",
                "assert (x = 3);"
            ]);
        };
        EditInstructions.prototype.loadEx2 = function () {
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
        };
        Object.defineProperty(EditInstructions.prototype, "numInstructions", {
            get: function () {
                return this.statements.length;
            },
            enumerable: true,
            configurable: true
        });
        EditInstructions.prototype.createDynVerElement = function () {
            return $("<span>").addClass("intermediateState");
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
                jqEnv.append($("<span>")
                    .addClass("dynEnv")
                    .text(EvalEnv_1.printEnv(StackEnv_1.topEnv(dynEnv))));
            else
                jqEnv.append($("<span>")
                    .addClass("dynEnv")
                    .text("BLOCKED"));
        };
        EditInstructions.prototype.analyze = function () {
            var _this = this;
            // clear messages
            this.verificationFormulas.forEach(function (x) { return x.text("").removeClass("err").attr("title", null); });
            $(".clearMe").text("");
            var statements = this.statements.map(function (x) { return x.getStatement(); });
            statements.push(new Statement_1.StatementCast(this.condPost));
            var g = Gamma_1.GammaNew;
            var cond = this.condPre;
            var dynEnv = { H: {}, S: [{ r: {}, A: [], ss: statements }] };
            var dynEnvNextStmt = function () { return dynEnv.S.map(function (x) { return x.ss; }).filter(function (x) { return x.length > 0; })[0][0]; };
            var dynStepInto = function () { dynEnv = dynEnv == null ? null : dynEnvNextStmt().smallStep(dynEnv, _this.hoare.env); };
            var dynStepOver = function () { dynStepInto(); while (dynEnv != null && dynEnv.S.length > 1)
                dynStepInto(); };
            var dynCheckDyn = function (frm) { return dynEnv != null && frm.eval(StackEnv_1.topEnv(dynEnv)); };
            var dynSuccess = true;
            for (var i = 0; i < statements.length; ++i) {
                this.displayPreCond(i, cond);
                this.displayDynState(i, dynEnv);
                if (!cond.satisfiable()) {
                    $("#frm" + i).text("pre-condition malformed: not satisfiable").addClass("err");
                    return;
                }
                if (!cond.sfrm()) {
                    $("#frm" + i).text("pre-condition malformed: not self-framed").addClass("err");
                    return;
                }
                var s = statements[i];
                var errs = this.hoare.check(s, cond, g);
                if (errs != null) {
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
                if (dynSuccess && dynEnv != null && !cond.eval(StackEnv_1.topEnv(dynEnv)))
                    throw "preservation broke";
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
                        tr.append($("<td>").append(_this.verificationFormulas[i]));
                        tr.append($("<td>").attr("id", "frm" + i).addClass("clearMe"));
                        tr.append($("<td>").append(createButton("+").click(function () { return _this.insertInstruction(i); })));
                    }
                    if (i != n) {
                        var tr = $("<tr>").appendTo(table);
                        tr.append($("<td>").append(_this.statements[i].createHTML()));
                        tr.append($("<td>").attr("id", "ins" + i).addClass("clearMe"));
                        tr.append($("<td>").append(createButton("-").click(function () { return _this.removeInstruction(i); })));
                    }
                    else {
                        var tr = $("<tr>").appendTo(table);
                        tr.append($("<td>"));
                        tr.append($("<td>").attr("id", "ins" + i).addClass("clearMe"));
                        tr.append($("<td>"));
                    }
                })(i);
            this.analyze();
        };
        return EditInstructions;
    }());
    exports.EditInstructions = EditInstructions;
});
