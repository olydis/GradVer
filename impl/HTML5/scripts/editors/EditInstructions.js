define(["require", "exports", "./EditStatement", "./EditVerificationFormula", "../GUIHelpers", "../types/VerificationFormulaGradual", "../types/VerificationFormula"], function (require, exports, EditStatement_1, EditVerificationFormula_1, GUIHelpers_1, VerificationFormulaGradual_1, VerificationFormula_1) {
    "use strict";
    var EditInstructions = (function () {
        function EditInstructions(container, hoare) {
            this.container = container;
            this.hoare = hoare;
            this.statements = [];
            this.verificationFormulas = [];
            this.verificationFormulas.push(new EditVerificationFormula_1.EditVerificationFormula());
            this.insertInstruction(0);
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
        Object.defineProperty(EditInstructions.prototype, "numInstructions", {
            get: function () {
                return this.statements.length;
            },
            enumerable: true,
            configurable: true
        });
        EditInstructions.prototype.removeInstruction = function (index) {
            this.verificationFormulas.splice(index + 1, 1);
            this.statements.splice(index, 1);
            this.updateGUI();
        };
        EditInstructions.prototype.insertInstruction = function (index) {
            this.verificationFormulas.splice(index + 1, 0, new EditVerificationFormula_1.EditVerificationFormula());
            this.statements.splice(index, 0, new EditStatement_1.EditStatement());
            this.updateGUI();
        };
        EditInstructions.prototype.checkStatement = function (index) {
            var s = this.statements[index].getStatement();
            var pre = this.verificationFormulas[index].getFormula();
            var post = this.verificationFormulas[index + 1].getFormula();
            return this.hoare.validate(s, pre, post);
        };
        EditInstructions.prototype.btnCheckAll = function () {
            for (var i = 0; i < this.numInstructions; ++i)
                this.btnCheck(i);
        };
        EditInstructions.prototype.btnCheck = function (index) {
            var ins = this.statements[index].stmtContainer;
            var errs = this.checkStatement(index);
            if (errs == null)
                GUIHelpers_1.GUIHelpers.flashCorrect(ins);
            else
                GUIHelpers_1.GUIHelpers.flashError(ins, errs[0]);
            return errs == null;
        };
        EditInstructions.prototype.btnPropDownAll = function () {
            for (var i = 0; i < this.numInstructions; ++i)
                this.btnPropDown(i);
        };
        EditInstructions.prototype.btnPropDown = function (index) {
            var stmt = this.statements[index].getStatement();
            var pre = this.verificationFormulas[index].getFormula();
            var post = this.verificationFormulas[index + 1].getFormula();
            var npost = this.hoare.genPost(stmt, pre, post);
            this.verificationFormulas[index + 1].setFormula(npost);
        };
        EditInstructions.prototype.btnResetAssertionsAll = function (grad) {
            for (var i = 0; i <= this.numInstructions; ++i)
                this.btnResetAssertions(grad, i);
        };
        EditInstructions.prototype.btnResetAssertions = function (grad, index) {
            this.verificationFormulas[index].setFormula(VerificationFormulaGradual_1.VerificationFormulaGradual.create(grad, new VerificationFormula_1.VerificationFormula()));
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
                    if (i != 0)
                        _this.container.append(createRightButton("↲").click(function () { return _this.btnPropDown(i - 1); }));
                    if (i != n)
                        _this.container.append(createRightButton("↰").click(function () {
                            var stmt = _this.statements[i].getStatement();
                            var pre = _this.verificationFormulas[i].getFormula();
                            var post = _this.verificationFormulas[i + 1].getFormula();
                            var npre = _this.hoare.genPre(stmt, pre, post);
                            _this.verificationFormulas[i].setFormula(npre);
                        }));
                    _this.container.append(_this.verificationFormulas[i].createHTML());
                    if (i != n) {
                        var ins = _this.statements[i].createHTML();
                        _this.container.append(createRightButton("-").click(function () { return _this.removeInstruction(i); }));
                        _this.container.append(createRightButton("✓").click(function () {
                            _this.btnCheck(i);
                        }));
                        // this.container.append(createRightButton("⇳").click(() => {
                        // }));
                        _this.container.append(ins);
                    }
                })(i);
        };
        return EditInstructions;
    }());
    exports.EditInstructions = EditInstructions;
});
