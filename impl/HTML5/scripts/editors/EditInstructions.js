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
        Object.defineProperty(EditInstructions.prototype, "numInstructions", {
            get: function () {
                return this.statements.length;
            },
            enumerable: true,
            configurable: true
        });
        EditInstructions.prototype.createDynVerElement = function () {
            return $("<span>").addClass("dynCheck");
        };
        EditInstructions.prototype.displayDynCondition = function (i, dyn, cond) {
            if (!dyn.satisfiable()) {
                this.verificationFormulas[i].text("implication cannot hold").addClass("err");
                return false;
            }
            this.verificationFormulas[i].text("").append(cond.createHTML().text());
            if (dyn.createHTML().text() != "true")
                this.verificationFormulas[i].append($("<b style='font-weight: bold'>")
                    .text("   +   " + dyn.createHTML().text()));
            return true;
        };
        EditInstructions.prototype.update = function () {
            // clear messages
            this.verificationFormulas.forEach(function (x) { return x.text(" ").removeClass("err").attr("title", null); });
            var g = Gamma_1.GammaNew;
            var cond = this.condPre;
            for (var i = 0; i < this.statements.length; ++i) {
                var s = this.statements[i].getStatement();
                var errs = this.hoare.check(s, cond, g);
                if (errs != null) {
                    this.verificationFormulas[i].text(errs[0]).addClass("err");
                    return;
                }
                var res = this.hoare.post(s, cond, g);
                if (!this.displayDynCondition(i, res.dyn, cond))
                    return;
                cond = res.post;
                g = res.postGamma;
            }
            var lastDyn = cond.impliesRuntime(this.condPost.staticFormula);
            if (!this.displayDynCondition(this.statements.length, lastDyn, cond))
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
