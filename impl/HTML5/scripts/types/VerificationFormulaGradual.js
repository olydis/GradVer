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
        VerificationFormulaGradual.prototype.satisfiable = function () {
            return this.staticFormula.satisfiable();
        };
        VerificationFormulaGradual.prototype.norm = function () {
            return VerificationFormulaGradual.create(this.gradual, this.staticFormula.norm());
        };
        VerificationFormulaGradual.prototype.woVar = function (x) {
            return VerificationFormulaGradual.create(this.gradual, this.staticFormula.woVar(x));
        };
        VerificationFormulaGradual.prototype.woAcc = function (e, f) {
            return VerificationFormulaGradual.create(this.gradual, this.staticFormula.woAcc(e, f));
        };
        VerificationFormulaGradual.prototype.impliesRuntime = function (phi) {
            var _this = this;
            if (this.gradual) {
                // impossible by itself?
                if (!phi.satisfiable())
                    return VerificationFormula_1.VerificationFormula.getFalse();
                var linearPart = phi.parts.filter(function (p) { return p instanceof VerificationFormula_1.FormulaPartAcc; });
                var classicalPart = phi.parts.filter(function (p) { return !(p instanceof VerificationFormula_1.FormulaPartAcc); });
                // augment classical parts
                for (var i = 0; i < linearPart.length; ++i)
                    for (var j = i + 1; j < linearPart.length; ++j)
                        if (linearPart[i].f == linearPart[j].f)
                            classicalPart.push(new VerificationFormula_1.FormulaPartNeq(linearPart[i].e, linearPart[j].e));
                // impossible to imply?
                if (!new VerificationFormula_1.VerificationFormula(null, this.staticFormula.parts.concat(classicalPart)).satisfiable())
                    return VerificationFormula_1.VerificationFormula.getFalse();
                // simplify
                classicalPart = classicalPart.filter(function (x) {
                    return !_this.staticFormula.implies(new VerificationFormula_1.VerificationFormula(null, [x]));
                });
                linearPart = linearPart.filter(function (x) {
                    return !_this.staticFormula.implies(new VerificationFormula_1.VerificationFormula(null, [x]));
                });
                // not required if more sophisticated:
                // - create meet of A and B (structured disjunction)
                // - eliminate unsatisfiable
                // - simplify remaining
                // BUT: that makes runtime checks more expensive!
                return new VerificationFormula_1.VerificationFormula(null, classicalPart.concat(linearPart)).norm();
            }
            else
                return this.staticFormula.impliesRuntime(phi);
        };
        // may produce false negatives
        VerificationFormulaGradual.prototype.impliesApprox = function (phi) {
            if (this.gradual)
                return VerificationFormula_1.VerificationFormula.intersect(this.staticFormula, phi).satisfiable();
            else
                return this.staticFormula.implies(phi);
        };
        return VerificationFormulaGradual;
    }());
    exports.VerificationFormulaGradual = VerificationFormulaGradual;
});
