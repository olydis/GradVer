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
        VerificationFormulaGradual.supremum = function (a, b) {
            if (!a.gradual || !b.gradual)
                return null;
            var sA = a.norm().staticFormula;
            var sB = b.norm().staticFormula;
            var parts = [];
            for (var _i = 0, _a = sA.impliedEqualities().concat(sB.impliedEqualities()); _i < _a.length; _i++) {
                var eq = _a[_i];
                var part = new VerificationFormula_1.VerificationFormula(null, [eq]);
                if (sB.implies(part) && sA.implies(part))
                    parts.push(eq);
            }
            for (var _b = 0, _c = sA.impliedInequalities().concat(sB.impliedInequalities()); _b < _c.length; _b++) {
                var neq = _c[_b];
                var part = new VerificationFormula_1.VerificationFormula(null, [neq]);
                if (sB.implies(part) && sA.implies(part))
                    parts.push(neq);
            }
            var res = VerificationFormulaGradual.create(true, new VerificationFormula_1.VerificationFormula(null, parts));
            return res.norm();
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
            return this.html.clone();
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
        VerificationFormulaGradual.prototype.satisfiable = function () {
            return this.staticFormula.satisfiable();
        };
        VerificationFormulaGradual.prototype.norm = function () {
            var res = VerificationFormulaGradual.create(this.gradual, this.staticFormula.norm());
            // gradual post-normalization
            if (this.gradual)
                res = VerificationFormulaGradual.create(true, this.staticFormula.snorm());
            return res;
        };
        VerificationFormulaGradual.prototype.woVar = function (x) {
            return VerificationFormulaGradual.create(this.gradual, this.staticFormula.woVar(x));
        };
        VerificationFormulaGradual.prototype.woAcc = function (e, f) {
            return VerificationFormulaGradual.create(this.gradual, this.staticFormula.woAcc(e, f));
        };
        VerificationFormulaGradual.prototype.append = function (part) {
            return VerificationFormulaGradual.create(this.gradual, this.staticFormula.append(part));
        };
        VerificationFormulaGradual.prototype.implies = function (phi) {
            if (this.gradual) {
                var staticIntersection = this.staticFormula.snorm().parts
                    .concat(phi.snorm().parts);
                // implication fails statically?
                var res = new VerificationFormula_1.VerificationFormula(null, staticIntersection).norm();
                if (!res.satisfiable())
                    return null;
                // simplify
                return VerificationFormulaGradual.create(true, res);
            }
            else {
                var sf = this.staticFormula.implies(phi);
                if (sf == null)
                    return null;
                return VerificationFormulaGradual.create(false, sf);
            }
        };
        // MUST return false if implication impossible (for hoare rules to be gradual lifting!)
        // on the otherhand, witnesses don't need to be optimal
        VerificationFormulaGradual.prototype.impliesRuntime = function (phi) {
            var res = this.implies(phi);
            return res == null
                ? VerificationFormula_1.VerificationFormula.getFalse()
                : res.staticFormula.simplifyAssuming(this.staticFormula);
        };
        return VerificationFormulaGradual;
    }());
    exports.VerificationFormulaGradual = VerificationFormulaGradual;
});
