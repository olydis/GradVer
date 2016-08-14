define(["require", "exports", "./EditStatement", "../runtime/Gamma", "../types/VerificationFormulaGradual", "../types/VerificationFormula"], function (require, exports, EditStatement_1, Gamma_1, VerificationFormulaGradual_1, VerificationFormula_1) {
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
        EditInstructions.prototype.loadEx1 = function () {
            while (this.numInstructions > 5)
                this.removeInstruction(0);
            while (this.numInstructions < 5)
                this.insertInstruction(0);
            this.statements[0].setStatementX("int x;");
            this.statements[1].setStatementX("int y;");
            this.statements[2].setStatementX("y = 3;");
            this.statements[3].setStatementX("x = y;");
            this.statements[4].setStatementX("assert (x = 3);");
        };
        EditInstructions.prototype.loadEx2 = function () {
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
        EditInstructions.prototype.displayPreCondition = function (i, dynF, cond) {
            var condx = [cond.staticFormula];
            condx.push.apply(condx, cond.staticFormula.autoFraming().map(function (x) { return x.asFormula(); }));
            var dyn = dynF.autoFramedChecks(condx);
            if (dyn.some(function (x) { return !x.satisfiable(); })) {
                throw "shouldn't have happened";
            }
            this.verificationFormulas[i].text("").append(cond.norm().toString());
            if (dyn.length > 0)
                this.verificationFormulas[i].append($("<span>")
                    .addClass("dynCheck")
                    .text(dyn.join(", ")));
            return true;
        };
        EditInstructions.prototype.update = function () {
            // clear messages
            this.verificationFormulas.forEach(function (x) { return x.text(" ").removeClass("err").attr("title", null); });
            var g = Gamma_1.GammaNew;
            var cond = this.condPre;
            for (var i = 0; i < this.statements.length; ++i) {
                if (!cond.satisfiable()) {
                    this.verificationFormulas[i].text("pre-condition malformed: not satisfiable").addClass("err");
                    return;
                }
                if (!cond.sfrm()) {
                    this.verificationFormulas[i].text("pre-condition malformed: not self-framed").addClass("err");
                    return;
                }
                var s = this.statements[i].getStatement();
                var errs = this.hoare.check(s, cond, g);
                if (errs != null) {
                    this.verificationFormulas[i].text(errs[0]).addClass("err");
                    return;
                }
                var res = this.hoare.post(s, cond, g);
                if (!this.displayPreCondition(i, res.dyn, cond))
                    return;
                cond = res.post;
                g = res.postGamma;
            }
            var lastDyn = this.condPost.staticFormula;
            if (!this.displayPreCondition(this.statements.length, lastDyn, cond))
                return;
        };
        EditInstructions.prototype.updateConditions = function (pre, post) {
            this.condPre = pre;
            this.condPost = post;
            this.update();
        };
        EditInstructions.prototype.removeInstruction = function (index) {
            this.verificationFormulas.splice(index + 1, 1);
            this.statements.splice(index, 1);
            this.updateGUI();
        };
        EditInstructions.prototype.insertInstruction = function (index) {
            var _this = this;
            this.verificationFormulas.splice(index + 1, 0, this.createDynVerElement());
            this.statements.splice(index, 0, new EditStatement_1.EditStatement(undefined, function () { return _this.update(); }));
            this.updateGUI();
        };
        EditInstructions.prototype.updateGUI = function () {
            var _this = this;
            var createRightButton = function (s) {
                return $("<span>")
                    .addClass("rightFloat")
                    .append($("<span>")
                    .addClass("button")
                    .addClass("buttonAutohide")
                    .text(s));
            };
            this.container.text("");
            var n = this.numInstructions;
            for (var i = 0; i <= n; ++i)
                (function (i) {
                    _this.container.append(createRightButton("+").click(function () { return _this.insertInstruction(i); }));
                    _this.container.append(_this.verificationFormulas[i]);
                    if (i != n) {
                        var ins = _this.statements[i].createHTML();
                        _this.container.append(createRightButton("-").click(function () { return _this.removeInstruction(i); }));
                        _this.container.append(ins);
                    }
                })(i);
            this.update();
        };
        return EditInstructions;
    }());
    exports.EditInstructions = EditInstructions;
});
