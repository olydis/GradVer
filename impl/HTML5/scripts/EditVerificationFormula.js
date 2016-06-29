define(["require", "exports", "./VerificationFormulaGradual"], function (require, exports, VerificationFormulaGradual_1) {
    "use strict";
    var EditVerificationFormula = (function () {
        function EditVerificationFormula(verForm) {
            if (verForm === void 0) { verForm = new VerificationFormulaGradual_1.VerificationFormulaGradual(); }
            this.verForm = verForm;
        }
        EditVerificationFormula.prototype.createHTML = function () {
            var container = $("<span>")
                .addClass("instructionVerForm");
            container.append("{");
            container.append(this.verForm.createHTML());
            container.append("}");
            return container;
        };
        return EditVerificationFormula;
    }());
    exports.EditVerificationFormula = EditVerificationFormula;
});
