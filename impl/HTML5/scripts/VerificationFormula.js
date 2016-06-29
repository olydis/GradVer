var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports"], function (require, exports) {
    "use strict";
    var FormulaPart = (function () {
        function FormulaPart() {
        }
        return FormulaPart;
    }());
    var FormulaPartTrue = (function (_super) {
        __extends(FormulaPartTrue, _super);
        function FormulaPartTrue() {
            _super.apply(this, arguments);
        }
        FormulaPartTrue.prototype.createHTML = function () {
            return $("<span>").text("true");
        };
        return FormulaPartTrue;
    }(FormulaPart));
    var VerificationFormula = (function () {
        function VerificationFormula() {
            this.html = $("<span>");
            this.parts = [];
            this.updateHTML();
        }
        VerificationFormula.prototype.isEmpty = function () {
            return this.parts.length == 0;
        };
        VerificationFormula.prototype.updateHTML = function () {
            var parts = this.isEmpty() ? [new FormulaPartTrue()] : this.parts;
            this.html.text("");
            for (var i = 0; i < parts.length; ++i) {
                if (i > 0)
                    this.html.append($("<span>").addClass("sepConj"));
                this.html.append(parts[i].createHTML());
            }
        };
        VerificationFormula.prototype.createHTML = function () {
            return this.html;
        };
        return VerificationFormula;
    }());
    exports.VerificationFormula = VerificationFormula;
});
