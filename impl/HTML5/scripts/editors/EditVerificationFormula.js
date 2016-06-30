var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports", "./EditableElement", "../types/VerificationFormulaGradual", "../types/VerificationFormulaDataServices"], function (require, exports, EditableElement_1, VerificationFormulaGradual_1, VerificationFormulaDataServices_1) {
    "use strict";
    var EditVerificationFormula = (function (_super) {
        __extends(EditVerificationFormula, _super);
        function EditVerificationFormula(initialSource) {
            var _this = this;
            if (initialSource === void 0) { initialSource = ""; }
            var formulaContainer = $("<span>");
            _super.call(this, formulaContainer, initialSource, function (source) {
                _this.verForm = new VerificationFormulaGradual_1.VerificationFormulaGradual(source);
                var html = _this.verForm.createHTML();
                if (!_this.verForm.sfrm())
                    html.addClass("errSfrm");
                // DEBUG: normalized data
                var data = _this.verForm.staticFormula.collectData();
                data = VerificationFormulaDataServices_1.vfdNormalize(data);
                console.log(JSON.stringify(data));
                // DEBUG end
                return {
                    source: html.text(),
                    html: html
                };
            });
            this.formulaContainer = formulaContainer;
        }
        EditVerificationFormula.prototype.createHTML = function () {
            var _this = this;
            return $("<p>")
                .addClass("clickable")
                .addClass("instructionVerForm")
                .append("{")
                .append(this.formulaContainer)
                .append("}")
                .click(function (eo) {
                _this.editBegin();
                eo.stopPropagation();
            });
        };
        return EditVerificationFormula;
    }(EditableElement_1.EditableElement));
    exports.EditVerificationFormula = EditVerificationFormula;
});
