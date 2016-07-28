var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports", "./Expression", "./ValueExpression", "../runtime/EvalEnv"], function (require, exports, Expression_1, ValueExpression_1, EvalEnv_1) {
    "use strict";
    var FormulaPart = (function () {
        function FormulaPart() {
        }
        FormulaPart.prototype.footprintStatic = function () {
            return [];
        };
        FormulaPart.prototype.footprintDynamic = function (env) {
            return [];
        };
        FormulaPart.prototype.envImpiledBy = function (env) { return this.eval(env.getEnv()); };
        Object.defineProperty(FormulaPart, "subs", {
            get: function () {
                return [
                    FormulaPartAcc,
                    FormulaPartTrue,
                    FormulaPartNeq,
                    FormulaPartEq,
                ];
            },
            enumerable: true,
            configurable: true
        });
        FormulaPart.parse = function (source) {
            source = source.replace(/\s/g, "");
            source = source.replace(/\(/g, "");
            source = source.replace(/\)/g, "");
            var result = null;
            for (var _i = 0, _a = FormulaPart.subs; _i < _a.length; _i++) {
                var sub = _a[_i];
                if (result)
                    break;
                result = sub.parse(source);
            }
            return result;
        };
        FormulaPart.eq = function (p1, p2) {
            for (var _i = 0, _a = FormulaPart.subs; _i < _a.length; _i++) {
                var sub = _a[_i];
                if (p1 instanceof sub && p2 instanceof sub)
                    return JSON.stringify(p1) == JSON.stringify(p2);
            }
            return false;
        };
        return FormulaPart;
    }());
    exports.FormulaPart = FormulaPart;
    var FormulaPartTrue = (function (_super) {
        __extends(FormulaPartTrue, _super);
        function FormulaPartTrue() {
            _super.apply(this, arguments);
        }
        FormulaPartTrue.parse = function (source) {
            return source.toLowerCase() == "true"
                ? new FormulaPartTrue()
                : null;
        };
        FormulaPartTrue.prototype.createHTML = function () {
            return $("<span>").text("true");
        };
        FormulaPartTrue.prototype.substs = function (m) {
            return this;
        };
        FormulaPartTrue.prototype.sfrm = function (fp) {
            return true;
        };
        FormulaPartTrue.prototype.FV = function () { return []; };
        FormulaPartTrue.prototype.envAdd = function (env) { return env; };
        FormulaPartTrue.prototype.eval = function (env) { return true; };
        return FormulaPartTrue;
    }(FormulaPart));
    exports.FormulaPartTrue = FormulaPartTrue;
    var FormulaPartEq = (function (_super) {
        __extends(FormulaPartEq, _super);
        function FormulaPartEq(e1, e2) {
            _super.call(this);
            this.e1 = e1;
            this.e2 = e2;
            if (e1 == null)
                throw "null arg";
            if (e2 == null)
                throw "null arg";
        }
        FormulaPartEq.parse = function (source) {
            var eqIndex = source.indexOf("=");
            if (eqIndex == -1)
                return null;
            var a = source.substr(0, eqIndex);
            var b = source.substr(eqIndex + 1).replace(/=/g, "");
            var ea = Expression_1.Expression.parse(a);
            var eb = Expression_1.Expression.parse(b);
            return ea != null && eb != null
                ? new FormulaPartEq(ea, eb)
                : null;
        };
        FormulaPartEq.prototype.createHTML = function () {
            return $("<span>")
                .append($("<span>").text("("))
                .append(this.e1.createHTML())
                .append($("<span>").text(" = "))
                .append(this.e2.createHTML())
                .append($("<span>").text(")"));
        };
        FormulaPartEq.prototype.substs = function (m) {
            return new FormulaPartEq(this.e1.substs(m), this.e2.substs(m));
        };
        FormulaPartEq.prototype.sfrm = function (fp) {
            return this.e1.sfrm(fp)
                && this.e2.sfrm(fp);
        };
        FormulaPartEq.prototype.FV = function () { return this.e1.FV().concat(this.e2.FV()); };
        FormulaPartEq.prototype.envAdd = function (env) { return env.addEq(this.e1, this.e2); };
        FormulaPartEq.prototype.eval = function (env) {
            var v1 = this.e1.eval(env);
            var v2 = this.e2.eval(env);
            return v1 != null && v2 != null && v1.equalTo(v2);
        };
        return FormulaPartEq;
    }(FormulaPart));
    exports.FormulaPartEq = FormulaPartEq;
    var FormulaPartNeq = (function (_super) {
        __extends(FormulaPartNeq, _super);
        function FormulaPartNeq(e1, e2) {
            _super.call(this);
            this.e1 = e1;
            this.e2 = e2;
            if (e1 == null)
                throw "null arg";
            if (e2 == null)
                throw "null arg";
        }
        FormulaPartNeq.parse = function (source) {
            var eqIndex = source.indexOf("!=");
            if (eqIndex == -1)
                eqIndex = source.indexOf("<>");
            if (eqIndex == -1)
                eqIndex = source.indexOf("≠");
            if (eqIndex == -1)
                return null;
            var a = source.substr(0, eqIndex);
            var b = source.substr(eqIndex + 1).replace(/=/g, "").replace(/>/g, "");
            var ea = Expression_1.Expression.parse(a);
            var eb = Expression_1.Expression.parse(b);
            return ea != null && eb != null
                ? new FormulaPartNeq(ea, eb)
                : null;
        };
        FormulaPartNeq.prototype.createHTML = function () {
            return $("<span>")
                .append($("<span>").text("("))
                .append(this.e1.createHTML())
                .append($("<span>").text(" ≠ "))
                .append(this.e2.createHTML())
                .append($("<span>").text(")"));
        };
        FormulaPartNeq.prototype.substs = function (m) {
            return new FormulaPartNeq(this.e1.substs(m), this.e2.substs(m));
        };
        FormulaPartNeq.prototype.sfrm = function (fp) {
            return this.e1.sfrm(fp)
                && this.e2.sfrm(fp);
        };
        FormulaPartNeq.prototype.FV = function () { return this.e1.FV().concat(this.e2.FV()); };
        FormulaPartNeq.prototype.envAdd = function (env) { return env.addIneq(this.e1, this.e2); };
        FormulaPartNeq.prototype.envImpiledBy = function (env) {
            if (!_super.prototype.envImpiledBy.call(this, env))
                return false;
            return env.addEq(this.e1, this.e2) == null;
        };
        FormulaPartNeq.prototype.eval = function (env) {
            var v1 = this.e1.eval(env);
            var v2 = this.e2.eval(env);
            return v1 != null && v2 != null && !v1.equalTo(v2);
        };
        return FormulaPartNeq;
    }(FormulaPart));
    exports.FormulaPartNeq = FormulaPartNeq;
    var FormulaPartAcc = (function (_super) {
        __extends(FormulaPartAcc, _super);
        function FormulaPartAcc(e, f) {
            _super.call(this);
            this.e = e;
            this.f = f;
            if (e == null)
                throw "null arg";
            if (!Expression_1.Expression.isValidX(f))
                throw "null arg";
        }
        FormulaPartAcc.parse = function (source) {
            if (source.substr(0, 3) != "acc")
                return null;
            source = source.substr(3);
            var dotIndex = source.lastIndexOf(".");
            if (dotIndex == -1)
                dotIndex = source.lastIndexOf(",");
            if (dotIndex == -1)
                return null;
            var e = Expression_1.Expression.parse(source.substr(0, dotIndex));
            var f = source.substr(dotIndex + 1);
            return e != null
                ? new FormulaPartAcc(e, f)
                : null;
        };
        FormulaPartAcc.prototype.createHTML = function () {
            return $("<span>")
                .append($("<span>").text("acc("))
                .append(this.e.createHTML())
                .append($("<span>").text("." + this.f))
                .append($("<span>").text(")"));
        };
        FormulaPartAcc.prototype.substs = function (m) {
            return new FormulaPartAcc(this.e.substs(m), this.f);
        };
        FormulaPartAcc.prototype.footprintStatic = function () {
            return [{ e: this.e, f: this.f }];
        };
        FormulaPartAcc.prototype.FootprintDynamic = function (env) {
            var v = this.e.eval(env);
            if (v instanceof ValueExpression_1.ValueObject)
                return [{ o: v.UID, f: this.f }];
            return [];
        };
        FormulaPartAcc.prototype.sfrm = function (fp) {
            return this.e.sfrm(fp);
        };
        FormulaPartAcc.prototype.FV = function () { return this.e.FV(); };
        FormulaPartAcc.prototype.envAdd = function (env) { return env.addAcc(this.e, this.f); };
        FormulaPartAcc.prototype.eval = function (env) {
            var _this = this;
            var v = this.e.eval(env);
            if (v instanceof ValueExpression_1.ValueObject)
                return env.A.some(function (a) { return a.o == v.UID && a.f == _this.f; });
            return false;
        };
        return FormulaPartAcc;
    }(FormulaPart));
    exports.FormulaPartAcc = FormulaPartAcc;
    var VerificationFormula = (function () {
        function VerificationFormula(source, parts) {
            if (source === void 0) { source = null; }
            if (parts === void 0) { parts = []; }
            this.parts = parts;
            this.html = $("<span>");
            if (source) {
                this.parts = [];
                source = source.trim();
                if (source != "")
                    this.parts = source.split("*").map(FormulaPart.parse).filter(function (part) { return part != null; });
            }
            this.updateHTML();
        }
        VerificationFormula.getFalse = function () {
            return new VerificationFormula(null, [new FormulaPartNeq(Expression_1.Expression.getNull(), Expression_1.Expression.getNull())]);
        };
        VerificationFormula.empty = function () {
            return new VerificationFormula(null, []);
        };
        VerificationFormula.intersect = function (p1, p2) {
            var parts = p1.parts.slice();
            parts.push.apply(parts, p2.parts.filter(function (x) { return !parts.some(function (y) { return FormulaPart.eq(x, y); }); }));
            parts = parts.filter(function (p) { return !(p instanceof FormulaPartTrue); });
            return new VerificationFormula(null, parts);
        };
        VerificationFormula.eq = function (p1, p2) {
            if (p1.parts.length != p2.parts.length)
                return false;
            return p1.parts.every(function (p, i) { return FormulaPart.eq(p, p2.parts[i]); });
        };
        VerificationFormula.prototype.isEmpty = function () {
            return this.parts.length == 0;
        };
        VerificationFormula.prototype.updateHTML = function () {
            var parts = this.isEmpty() ? [new FormulaPartTrue()] : this.parts;
            this.html.text("");
            for (var i = 0; i < parts.length; ++i) {
                if (i > 0)
                    this.html.append($("<span>").addClass("sepConj").text(" * "));
                this.html.append(parts[i].createHTML());
            }
        };
        VerificationFormula.prototype.createHTML = function () {
            return this.html;
        };
        VerificationFormula.prototype.substs = function (m) {
            var frm = new VerificationFormula();
            frm.parts = this.parts.map(function (part) { return part.substs(m); });
            return frm;
        };
        VerificationFormula.prototype.sfrm = function (fp) {
            if (fp === void 0) { fp = []; }
            for (var _i = 0, _a = this.parts; _i < _a.length; _i++) {
                var part = _a[_i];
                if (!part.sfrm(fp))
                    return false;
                fp.push.apply(fp, part.footprintStatic());
            }
            return true;
        };
        VerificationFormula.prototype.footprintStatic = function () {
            var res = [];
            this.parts.forEach(function (p) { return res.push.apply(res, p.footprintStatic()); });
            return res;
        };
        VerificationFormula.prototype.footprintDynamic = function (env) {
            var res = [];
            this.parts.forEach(function (p) { return res.push.apply(res, p.footprintDynamic(env)); });
            return res;
        };
        VerificationFormula.prototype.eval = function (env) {
            if (!this.parts.every(function (p) { return p.eval(env); }))
                return false;
            var fp = this.footprintDynamic(env);
            // nodup
            var a = [];
            for (var _i = 0, fp_1 = fp; _i < fp_1.length; _i++) {
                var x = fp_1[_i];
                if (a.some(function (y) { return y.f == x.f && y.o == x.o; }))
                    return false;
                a.push(x);
            }
            return true;
        };
        VerificationFormula.prototype.envImpliedBy = function (env) {
            if (env == null)
                return true;
            if (!this.parts.every(function (p) { return p.envImpiledBy(env); }))
                return false;
            return this.eval(env.getEnv());
        };
        VerificationFormula.prototype.FV = function () {
            return this.parts.reduce(function (a, b) { return a.concat(b.FV()); }, []);
        };
        VerificationFormula.prototype.createNormalizedEnv = function () {
            var env = EvalEnv_1.NormalizedEnv.create();
            for (var _i = 0, _a = this.parts; _i < _a.length; _i++) {
                var part = _a[_i];
                env = env ? part.envAdd(env) : null;
            }
            return env;
        };
        VerificationFormula.prototype.satisfiable = function () {
            return this.createNormalizedEnv() != null;
        };
        VerificationFormula.prototype.implies = function (phi) {
            return phi.envImpliedBy(this.createNormalizedEnv());
        };
        VerificationFormula.prototype.impliesRuntime = function (phi) {
            return this.implies(phi)
                ? VerificationFormula.empty()
                : VerificationFormula.getFalse();
        };
        VerificationFormula.prototype.norm = function () {
            var nenv = this.createNormalizedEnv();
            return nenv == null
                ? VerificationFormula.getFalse()
                : nenv.createFormula();
        };
        VerificationFormula.prototype.woVar = function (x) {
            var nenv = this.createNormalizedEnv();
            return nenv == null
                ? VerificationFormula.getFalse()
                : nenv.woVar(x).createFormula();
        };
        VerificationFormula.prototype.woAcc = function (e, f) {
            var nenv = this.createNormalizedEnv();
            return nenv == null
                ? VerificationFormula.getFalse()
                : nenv.woAcc(e, f).createFormula();
        };
        return VerificationFormula;
    }());
    exports.VerificationFormula = VerificationFormula;
});
