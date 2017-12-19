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
define(["require", "exports", "./Expression", "./ValueExpression", "../runtime/EvalEnv"], function (require, exports, Expression_1, ValueExpression_1, EvalEnv_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    var FormulaPart = /** @class */ (function () {
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
            try {
                var result = null;
                for (var _i = 0, _a = FormulaPart.subs; _i < _a.length; _i++) {
                    var sub = _a[_i];
                    if (result)
                        break;
                    result = sub.parse(source);
                }
                return result;
            }
            catch (e) {
                console.error("parse error", e);
                return new FormulaPartTrue();
            }
        };
        FormulaPart.eq = function (p1, p2) {
            for (var _i = 0, _a = FormulaPart.subs; _i < _a.length; _i++) {
                var sub = _a[_i];
                if (p1 instanceof sub && p2 instanceof sub)
                    return JSON.stringify(p1) == JSON.stringify(p2);
            }
            return false;
        };
        FormulaPart.prototype.asFormula = function () {
            return new VerificationFormula(null, [this]);
        };
        return FormulaPart;
    }());
    exports.FormulaPart = FormulaPart;
    var FormulaPartTrue = /** @class */ (function (_super) {
        __extends(FormulaPartTrue, _super);
        function FormulaPartTrue() {
            return _super !== null && _super.apply(this, arguments) || this;
        }
        FormulaPartTrue.parse = function (source) {
            return source.toLowerCase() == "true"
                ? new FormulaPartTrue()
                : null;
        };
        FormulaPartTrue.prototype.toString = function () {
            return "true";
        };
        FormulaPartTrue.prototype.substs = function (m) {
            return this;
        };
        FormulaPartTrue.prototype.subste = function (a, b) {
            return this;
        };
        FormulaPartTrue.prototype.sfrm = function (fp) {
            return true;
        };
        FormulaPartTrue.prototype.sfrmInv = function () {
            return [];
        };
        FormulaPartTrue.prototype.FV = function () { return []; };
        FormulaPartTrue.prototype.envAdd = function (env) { return env; };
        FormulaPartTrue.prototype.eval = function (env) { return true; };
        return FormulaPartTrue;
    }(FormulaPart));
    exports.FormulaPartTrue = FormulaPartTrue;
    var FormulaPartEq = /** @class */ (function (_super) {
        __extends(FormulaPartEq, _super);
        function FormulaPartEq(e1, e2) {
            var _this = _super.call(this) || this;
            _this.e1 = e1;
            _this.e2 = e2;
            if (e1 == null)
                throw "null arg";
            if (e2 == null)
                throw "null arg";
            return _this;
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
        FormulaPartEq.prototype.toString = function () {
            return "(" + this.e1.toString() + " = " + this.e2.toString() + ")";
        };
        FormulaPartEq.prototype.substs = function (m) {
            return new FormulaPartEq(this.e1.substs(m), this.e2.substs(m));
        };
        FormulaPartEq.prototype.subste = function (a, b) {
            return new FormulaPartEq(this.e1.subste(a, b), this.e2.subste(a, b));
        };
        FormulaPartEq.prototype.sfrm = function (fp) {
            return this.e1.sfrm(fp)
                && this.e2.sfrm(fp);
        };
        FormulaPartEq.prototype.sfrmInv = function () {
            return this.e1.necessaryFraming().concat(this.e2.necessaryFraming());
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
    var FormulaPartNeq = /** @class */ (function (_super) {
        __extends(FormulaPartNeq, _super);
        function FormulaPartNeq(e1, e2) {
            var _this = _super.call(this) || this;
            _this.e1 = e1;
            _this.e2 = e2;
            if (e1 == null)
                throw "null arg";
            if (e2 == null)
                throw "null arg";
            return _this;
        }
        FormulaPartNeq.parse = function (source) {
            if (source == "false")
                return new FormulaPartNeq(Expression_1.Expression.getNull(), Expression_1.Expression.getNull());
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
        FormulaPartNeq.prototype.toString = function () {
            var e1 = this.e1.toString();
            var e2 = this.e2.toString();
            if (e1 == e2 && e1 == "null")
                return "false";
            return "(" + e1 + " ≠ " + e2 + ")";
        };
        FormulaPartNeq.prototype.substs = function (m) {
            return new FormulaPartNeq(this.e1.substs(m), this.e2.substs(m));
        };
        FormulaPartNeq.prototype.subste = function (a, b) {
            return new FormulaPartNeq(this.e1.subste(a, b), this.e2.subste(a, b));
        };
        FormulaPartNeq.prototype.sfrm = function (fp) {
            return this.e1.sfrm(fp)
                && this.e2.sfrm(fp);
        };
        FormulaPartNeq.prototype.sfrmInv = function () {
            return this.e1.necessaryFraming().concat(this.e2.necessaryFraming());
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
    var FormulaPartAcc = /** @class */ (function (_super) {
        __extends(FormulaPartAcc, _super);
        function FormulaPartAcc(e, f) {
            var _this = _super.call(this) || this;
            _this.e = e;
            _this.f = f;
            if (e == null)
                throw "null arg";
            if (!Expression_1.Expression.isValidX(f))
                throw "null arg";
            return _this;
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
        FormulaPartAcc.prototype.toString = function () {
            return "acc(" + this.e.toString() + "." + this.f + ")";
        };
        FormulaPartAcc.prototype.substs = function (m) {
            return new FormulaPartAcc(this.e.substs(m), this.f);
        };
        FormulaPartAcc.prototype.subste = function (a, b) {
            return new FormulaPartAcc(this.e.subste(a, b), this.f);
        };
        FormulaPartAcc.prototype.footprintStatic = function () {
            return [{ e: this.e, f: this.f }];
        };
        FormulaPartAcc.prototype.footprintDynamic = function (env) {
            var v = this.e.eval(env);
            if (v instanceof ValueExpression_1.ValueObject)
                return [{ o: v.UID, f: this.f }];
            return [];
        };
        FormulaPartAcc.prototype.sfrm = function (fp) {
            return this.e.sfrm(fp);
        };
        FormulaPartAcc.prototype.sfrmInv = function () {
            return this.e.necessaryFraming();
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
    var VerificationFormula = /** @class */ (function () {
        function VerificationFormula(source, parts) {
            if (source === void 0) { source = null; }
            if (parts === void 0) { parts = []; }
            this.parts = parts;
            if (source) {
                this.parts = [];
                source = source.trim();
                if (source != "")
                    this.parts = source.split("*").map(FormulaPart.parse).filter(function (part) { return part !== null; });
            }
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
        VerificationFormula.prototype.toString = function () {
            var parts = this.isEmpty() ? [new FormulaPartTrue()] : this.parts;
            return parts.join(" * ");
        };
        VerificationFormula.prototype.substs = function (m) {
            var frm = new VerificationFormula();
            frm.parts = this.parts.map(function (part) { return part.substs(m); });
            return frm;
        };
        VerificationFormula.prototype.subste = function (a, b) {
            var frm = new VerificationFormula();
            frm.parts = this.parts.map(function (part) { return part.subste(a, b); });
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
        VerificationFormula.prototype.autoFraming = function () {
            var framing = [];
            for (var _i = 0, _a = this.snorm().parts; _i < _a.length; _i++) {
                var part = _a[_i];
                framing.push.apply(framing, part.sfrmInv());
            }
            var framingFrm = framing.map(function (x) { return new FormulaPartAcc(x.e, x.f); });
            var partsAcc = [];
            for (var _b = 0, framingFrm_1 = framingFrm; _b < framingFrm_1.length; _b++) {
                var acc = framingFrm_1[_b];
                if (partsAcc.every(function (x) { return !FormulaPart.eq(acc, x); }))
                    partsAcc.push(acc);
            }
            return partsAcc;
        };
        VerificationFormula.prototype.autoFramedChecks = function (knowns) {
            var parts = this.snorm().parts;
            // add framing
            var partsAcc = this.autoFraming();
            // simpl classical
            parts = parts.filter(function (x) { return partsAcc.every(function (y) {
                return new VerificationFormula(null, [y]).implies(new VerificationFormula(null, [x])) == null;
            }); });
            for (var _i = 0, knowns_1 = knowns; _i < knowns_1.length; _i++) {
                var known = knowns_1[_i];
                parts = parts.filter(function (x) { return known.implies(new VerificationFormula(null, [x])) == null; });
            }
            // simpl framing
            for (var _a = 0, knowns_2 = knowns; _a < knowns_2.length; _a++) {
                var known = knowns_2[_a];
                partsAcc = partsAcc.filter(function (x) { return new VerificationFormula(null, known.parts.concat(parts)).implies(new VerificationFormula(null, [x])) == null; });
            }
            return parts.concat(partsAcc).map(function (x) { return new VerificationFormula(null, [x]); });
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
        // partial function "imp" of PDF!
        VerificationFormula.prototype.implies = function (phi) {
            return phi.envImpliedBy(this.createNormalizedEnv())
                ? this
                : null;
        };
        VerificationFormula.prototype.impliedEqualities = function () {
            var nenv = this.createNormalizedEnv();
            return nenv == null
                ? null
                : nenv.impliedEqualities().map(function (x) { return new FormulaPartEq(x.e1, x.e2); });
        };
        VerificationFormula.prototype.impliedInequalities = function () {
            var nenv = this.createNormalizedEnv();
            return nenv == null
                ? null
                : nenv.impliedInequalities().map(function (x) { return new FormulaPartNeq(x.e1, x.e2); });
        };
        VerificationFormula.prototype.norm = function () {
            var nenv = this.createNormalizedEnv();
            return nenv == null
                ? VerificationFormula.getFalse()
                : nenv.createFormula();
        };
        VerificationFormula.prototype.snorm = function () {
            var linearPart = this.parts.filter(function (p) { return p instanceof FormulaPartAcc; });
            var classicalPart = this.parts.filter(function (p) { return !(p instanceof FormulaPartAcc); });
            // augment classical parts
            for (var i = 0; i < linearPart.length; ++i) {
                for (var j = i + 1; j < linearPart.length; ++j)
                    if (linearPart[i].f == linearPart[j].f)
                        classicalPart.push(new FormulaPartNeq(linearPart[i].e, linearPart[j].e));
                var pivot = new Expression_1.ExpressionDot(linearPart[i].e, linearPart[i].f);
                classicalPart.push(new FormulaPartEq(pivot, pivot));
            }
            return new VerificationFormula(null, classicalPart).norm();
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
        VerificationFormula.prototype.append = function (part) {
            var env = this.createNormalizedEnv();
            if (env != null)
                env = part.envAdd(env);
            if (part instanceof FormulaPartAcc) {
                var f = part.f;
                for (var _i = 0, _a = this.autoFraming(); _i < _a.length; _i++) {
                    var fx = _a[_i];
                    if (fx.f == f && env != null)
                        env = new FormulaPartNeq(fx.e, part.e).envAdd(env);
                }
            }
            return env == null
                ? VerificationFormula.getFalse()
                : env.createFormula();
        };
        VerificationFormula.prototype.dominators = function () {
            var result = [this.snorm()];
            var fp = this.autoFraming();
            for (var i = 0; i < fp.length; ++i)
                for (var j = i + 1; j < fp.length; ++j) {
                    if (fp[i].f != fp[j].f)
                        continue;
                    result = result.map(function (x) { return x.append(new FormulaPartEq(fp[i].e, fp[j].e)); }).concat(result.map(function (x) { return x.append(new FormulaPartNeq(fp[i].e, fp[j].e)); }));
                }
            result = result.map(function (f) { return f.norm(); });
            result = result.map(function (f) { return new VerificationFormula(null, f.autoFraming().concat(f.parts)); });
            result = result.map(function (f) { return f.norm(); });
            return result.filter(function (f) { return f.satisfiable(); });
        };
        VerificationFormula.nonSepAnd = function (a, b) {
            var inf = VerificationFormula.intersect(a.snorm(), b.snorm());
            var doms = inf.dominators();
            return doms.length == 1 ? doms[0] : null;
        };
        return VerificationFormula;
    }());
    exports.VerificationFormula = VerificationFormula;
});
