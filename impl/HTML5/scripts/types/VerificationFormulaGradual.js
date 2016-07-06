define(["require", "exports", "./VerificationFormula"], function (require, exports, VerificationFormula_1) {
    "use strict";
    var VerificationFormulaGradual = (function () {
        function VerificationFormulaGradual(source) {
            if (source === void 0) { source = "?"; }
            this.html = $("<span>");
            source = source.trim();
            this.gradual = false;
            if (source.charAt(0) == "?") {
                this.gradual = true;
                source = source.substr(1).trim().substr(1);
            }
            this.staticFormula = new VerificationFormula_1.VerificationFormula(source);
            this.updateHTML();
        }
        VerificationFormulaGradual.create = function (gradual, staticFormula) {
            var res = new VerificationFormulaGradual();
            res.gradual = gradual;
            res.staticFormula = staticFormula;
            res.updateHTML();
            return res;
        };
        VerificationFormulaGradual.prototype.updateHTML = function () {
            this.html.text("");
            var grad = $("<span>").text("?");
            if (!this.staticFormula.isEmpty())
                grad.append($("<span>").addClass("sepConj").text(" * "));
            if (this.gradual)
                this.html.append(grad);
            if (!this.gradual || !this.staticFormula.isEmpty())
                this.html.append(this.staticFormula.createHTML());
        };
        VerificationFormulaGradual.prototype.createHTML = function () {
            return this.html;
        };
        VerificationFormulaGradual.prototype.sfrm = function (fp) {
            if (fp === void 0) { fp = []; }
            return this.gradual || this.staticFormula.sfrm(fp);
        };
        VerificationFormulaGradual.prototype.substs = function (m) {
            var frm = new VerificationFormulaGradual();
            frm.gradual = this.gradual;
            frm.staticFormula = this.staticFormula.substs(m);
            return frm;
        };
        // may produce false negatives
        VerificationFormulaGradual.prototype.impliesApprox = function (phi) {
            if (this.gradual)
                return VerificationFormula_1.VerificationFormula.intersect(this.staticFormula, phi).satisfiableApprox();
            else
                return this.staticFormula.impliesApprox(phi);
        };
        VerificationFormulaGradual.prototype.impliesApproxMissing = function (phi) {
            return this.staticFormula.impliesApproxMissing(phi);
        };
        VerificationFormulaGradual.prototype.containsApprox = function (phi) {
            if (!this.gradual)
                return VerificationFormula_1.VerificationFormula.eq(this.staticFormula, phi);
            // gradual
            if (!phi.satisfiableApprox())
                return false;
            if (!phi.sfrm([]))
                return false;
            return phi.impliesApprox(this.staticFormula);
        };
        return VerificationFormulaGradual;
    }());
    exports.VerificationFormulaGradual = VerificationFormulaGradual;
});
