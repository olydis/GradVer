define(["require", "exports", "./EditStatement", "./EditVerificationFormula"], function (require, exports, EditStatement_1, EditVerificationFormula_1) {
    "use strict";
    var EditInstructions = (function () {
        function EditInstructions(container) {
            this.container = container;
            this.statements = [];
            this.verificationFormulas = [];
            this.verificationFormulas.push(new EditVerificationFormula_1.EditVerificationFormula());
            this.insertInstruction(0);
        }
        Object.defineProperty(EditInstructions.prototype, "numInstructions", {
            get: function () {
                return this.statements.length;
            },
            enumerable: true,
            configurable: true
        });
        EditInstructions.prototype.removeInstruction = function (index) {
            this.verificationFormulas.splice(index, 1);
            this.statements.splice(index, 1);
            this.updateGUI();
        };
        EditInstructions.prototype.insertInstruction = function (index) {
            this.verificationFormulas.splice(index, 0, new EditVerificationFormula_1.EditVerificationFormula());
            this.statements.splice(index, 0, new EditStatement_1.EditStatement());
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
                    _this.container.append(_this.verificationFormulas[i].createHTML());
                    if (i != n) {
                        _this.container.append(createRightButton("-").click(function () { return _this.removeInstruction(i); }));
                        _this.container.append(createRightButton("▲").click(function () { }));
                        _this.container.append(createRightButton("▼").click(function () { }));
                        _this.container.append(_this.statements[i].createHTML());
                    }
                })(i);
        };
        return EditInstructions;
    }());
    exports.EditInstructions = EditInstructions;
});
