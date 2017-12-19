define(["require", "exports", "./VerificationFormula"], function (require, exports, VerificationFormula_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    var VerificationFormulaGradual = /** @class */ (function () {
        function VerificationFormulaGradual(source) {
            if (source === void 0) { source = "?"; }
            source = source.trim();
            this.gradual = false;
            if (source.charAt(0) == "?") {
                this.gradual = true;
                source = source.substr(1).trim().substr(1);
            }
            this.staticFormula = new VerificationFormula_1.VerificationFormula(source);
        }
        VerificationFormulaGradual.create = function (gradual, staticFormula) {
            var res = new VerificationFormulaGradual();
            res.gradual = gradual;
            res.staticFormula = staticFormula;
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
        VerificationFormulaGradual.infimum = function (a, b) {
            if (!a.gradual && !b.gradual)
                if (a.staticFormula.implies(b.staticFormula) && b.staticFormula.implies(a.staticFormula))
                    return a;
                else
                    return null;
            if (!a.gradual)
                if (a.staticFormula.implies(b.staticFormula))
                    return a;
                else
                    return null;
            if (!b.gradual)
                if (b.staticFormula.implies(a.staticFormula))
                    return b;
                else
                    return null;
            return VerificationFormulaGradual.create(true, new VerificationFormula_1.VerificationFormula(null, a.staticFormula.snorm().parts.concat(b.staticFormula.snorm().parts)).snorm());
        };
        VerificationFormulaGradual.nonSepAnd = function (a, b) {
            if (!a.gradual && !b.gradual) {
                var nsa = VerificationFormula_1.VerificationFormula.nonSepAnd(a.staticFormula, b.staticFormula);
                return nsa == null ? null : VerificationFormulaGradual.create(false, nsa);
            }
            return VerificationFormulaGradual.create(true, new VerificationFormula_1.VerificationFormula(null, a.staticFormula.snorm().parts.concat(b.staticFormula.snorm().parts)).snorm());
        };
        VerificationFormulaGradual.prototype.toString = function () {
            if (this.staticFormula.isEmpty() && this.gradual)
                return "?";
            return (this.gradual ? "? * " : "") + this.staticFormula.toString();
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
        VerificationFormulaGradual.prototype.subste = function (a, b) {
            var frm = new VerificationFormulaGradual();
            frm.gradual = this.gradual;
            frm.staticFormula = this.staticFormula.subste(a, b);
            return frm;
        };
        VerificationFormulaGradual.prototype.createNormalizedEnv = function () {
            var env = this.staticFormula.createNormalizedEnv();
            for (var _i = 0, _a = this.staticFormula.autoFraming(); _i < _a.length; _i++) {
                var acc = _a[_i];
                env = acc.envAdd(env) || env;
            }
            return env;
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
                var res = new VerificationFormula_1.VerificationFormula(null, staticIntersection);
                if (!res.satisfiable())
                    return null;
                // simplify
                return VerificationFormulaGradual.create(true, res.norm());
            }
            else {
                var sf = this.staticFormula.implies(phi);
                if (sf == null)
                    return null;
                return VerificationFormulaGradual.create(false, sf);
            }
        };
        VerificationFormulaGradual.prototype.impliesRemaindors = function (phi) {
            var condClassic = this.staticFormula.snorm();
            var condx = this.staticFormula
                .autoFraming()
                .map(function (x) { return new VerificationFormula_1.VerificationFormula(null, [x].concat(condClassic.parts)); });
            condx.push(this.staticFormula);
            return phi.autoFramedChecks(condx);
        };
        VerificationFormulaGradual.prototype.impliesFully = function (phi) {
            var rem = this.impliesRemaindors(phi);
            return rem.length == 0;
        };
        VerificationFormulaGradual.prototype.eval = function (env) {
            var frm = this.staticFormula.autoFraming();
            if (!this.staticFormula.eval(env))
                return false;
            return frm.every(function (acc) { return acc.eval(env); });
        };
        VerificationFormulaGradual.eq = function (a, b) {
            return JSON.stringify(a) == JSON.stringify(b);
        };
        VerificationFormulaGradual.qm = function () {
            return VerificationFormulaGradual.create(true, VerificationFormula_1.VerificationFormula.empty());
        };
        return VerificationFormulaGradual;
    }());
    exports.VerificationFormulaGradual = VerificationFormulaGradual;
});
