var __extends = (this && this.__extends) || (function () {
    var extendStatics = Object.setPrototypeOf ||
        ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||
        function (d, b) { for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p]; };
    return function (d, b) {
        extendStatics(d, b);
        function __() { this.constructor = d; }
        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
    };
})();
define(["require", "exports", "./EditableElement", "../types/VerificationFormulaGradual"], function (require, exports, EditableElement_1, VerificationFormulaGradual_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    var EditVerificationFormula = /** @class */ (function (_super) {
        __extends(EditVerificationFormula, _super);
        function EditVerificationFormula(initialSource, onChange) {
            if (initialSource === void 0) { initialSource = ""; }
            if (onChange === void 0) { onChange = function () { }; }
            var _this = this;
            var formulaContainer = $("<span>");
            _this = _super.call(this, formulaContainer, initialSource, function (source, tthis) {
                tthis.verForm = new VerificationFormulaGradual_1.VerificationFormulaGradual(source);
                var src = tthis.verForm.toString();
                var html = $("<span>").text(src);
                // if (!tthis.verForm.sfrm())
                //     html.addClass("errSfrm");
                // // DEBUG: normalized data
                // var phi = tthis.verForm.staticFormula;
                // if (!phi.satisfiable())
                //     html.addClass("errFalse");
                // // DEBUG end
                return {
                    source: src,
                    html: html
                };
            }, function (tthis) { return onChange(tthis.verForm); }) || this;
            _this.formulaContainer = formulaContainer;
            return _this;
        }
        EditVerificationFormula.prototype.createHTML = function () {
            var _this = this;
            return $("<p>")
                .addClass("clickable")
                .addClass("instructionVerForm")
                .append(this.formulaContainer)
                .click(function (eo) {
                _this.editBegin();
                eo.stopPropagation();
            });
        };
        EditVerificationFormula.prototype.getFormula = function () { return this.verForm; };
        EditVerificationFormula.prototype.setFormula = function (frm) {
            this.verForm = frm;
            this.source = frm.toString();
            this.rerender();
        };
        return EditVerificationFormula;
    }(EditableElement_1.EditableElement));
    exports.EditVerificationFormula = EditVerificationFormula;
});
