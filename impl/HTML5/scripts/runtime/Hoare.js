define(["require", "exports", "../types/VerificationFormula", "../types/Statement", "../types/Type", "../types/Expression", "./Gamma"], function (require, exports, VerificationFormula_1, Statement_1, Type_1, Expression_1, Gamma_1) {
    "use strict";
    var Hoare = (function () {
        function Hoare(env) {
            var _this = this;
            this.env = env;
            this.ruleHandlers = [];
            this.addHandler("NewObject", Statement_1.StatementAlloc, function (s, pre, g, onErr) {
                var ex = new Expression_1.ExpressionX(s.x);
                var fs = _this.env.fields(s.C);
                // check
                if (fs == null) {
                    onErr("class '" + s.C + "' not found");
                    return null;
                }
                if (!new Type_1.TypeClass(s.C).compatibleWith(ex.getType(env, g))) {
                    onErr("type mismatch");
                    return null;
                }
                // processing
                pre = pre.woVar(s.x);
                pre = pre.append(new VerificationFormula_1.FormulaPartNeq(ex, Expression_1.Expression.getNull()));
                for (var _i = 0, fs_1 = fs; _i < fs_1.length; _i++) {
                    var f = fs_1[_i];
                    pre = pre.append(new VerificationFormula_1.FormulaPartAcc(ex, f.name));
                }
                return {
                    post: pre,
                    dyn: VerificationFormula_1.VerificationFormula.empty(),
                    postGamma: g
                };
            });
            this.addHandler("FieldAssign", Statement_1.StatementMemberSet, function (s, pre, g, onErr) {
                var ex = new Expression_1.ExpressionX(s.x);
                var ey = new Expression_1.ExpressionX(s.y);
                var CT = ex.getType(env, g);
                // check
                if (CT instanceof Type_1.TypeClass) {
                    var C = CT.C;
                    var fT = _this.env.fieldType(C, s.f);
                    if (fT == null) {
                        onErr("field not found");
                        return null;
                    }
                    if (!fT.compatibleWith(ey.getType(env, g))) {
                        onErr("type mismatch");
                        return null;
                    }
                    // processing
                    var accPart = new VerificationFormula_1.FormulaPartAcc(ex, s.f);
                    var dyn = pre.impliesRuntime(new VerificationFormula_1.VerificationFormula(null, [accPart]));
                    pre = pre.woAcc(ex, s.f);
                    pre = pre.append(accPart);
                    pre = pre.append(new VerificationFormula_1.FormulaPartNeq(ex, Expression_1.Expression.getNull()));
                    pre = pre.append(new VerificationFormula_1.FormulaPartEq(new Expression_1.ExpressionDot(ex, s.f), ey));
                    return {
                        post: pre,
                        dyn: dyn,
                        postGamma: g
                    };
                }
                onErr("type error");
                return null;
            });
            this.addHandler("VarAssign", Statement_1.StatementAssign, function (s, pre, g, onErr) {
                var ex = new Expression_1.ExpressionX(s.x);
                var xT = ex.getType(env, g);
                var eT = s.e.getType(env, g);
                // check
                if (xT == null) {
                    onErr("type error");
                    return null;
                }
                if (!xT.compatibleWith(eT)) {
                    onErr("type mismatch");
                    return null;
                }
                // processing
                pre = pre.woVar(s.x);
                var accParts = s.e.necessaryFraming().map(function (a) { return new VerificationFormula_1.FormulaPartAcc(a.e, a.f); });
                var dyn = pre.impliesRuntime(new VerificationFormula_1.VerificationFormula(null, accParts));
                pre = pre.append(new VerificationFormula_1.FormulaPartEq(ex, s.e));
                return {
                    post: pre,
                    dyn: dyn,
                    postGamma: g
                };
            });
            this.addHandler("Return", Statement_1.StatementReturn, function (s, pre, g, onErr) {
                var ex = new Expression_1.ExpressionX(s.x);
                var er = new Expression_1.ExpressionX(Expression_1.Expression.getResult());
                var xT = ex.getType(env, g);
                var rT = er.getType(env, g);
                // check
                if (xT == null) {
                    onErr("type error");
                    return null;
                }
                if (!xT.compatibleWith(rT)) {
                    onErr("type mismatch");
                    return null;
                }
                // processing
                pre = pre.woVar(Expression_1.Expression.getResult());
                pre = pre.append(new VerificationFormula_1.FormulaPartEq(er, ex));
                return {
                    post: pre,
                    dyn: VerificationFormula_1.VerificationFormula.empty(),
                    postGamma: g
                };
            });
            this.addHandler("Call", Statement_1.StatementCall, function (s, pre, g, onErr) {
                return null;
                // throw "not implemented";
            });
            this.addHandler("Assert", Statement_1.StatementAssert, function (s, pre, g, onErr) {
                var dyn = pre.impliesRuntime(s.assertion);
                pre = pre.implies(s.assertion);
                if (pre == null) {
                    onErr("implication failure");
                    return null;
                }
                return {
                    post: pre,
                    dyn: dyn,
                    postGamma: g
                };
            });
            this.addHandler("Release", Statement_1.StatementRelease, function (s, pre, g, onErr) {
                var dyn = pre.impliesRuntime(s.assertion);
                // processing
                pre = pre.implies(s.assertion);
                if (pre == null) {
                    onErr("implication failure");
                    return null;
                }
                for (var _i = 0, _a = s.assertion.footprintStatic(); _i < _a.length; _i++) {
                    var fp = _a[_i];
                    pre = pre.woAcc(fp.e, fp.f);
                }
                return {
                    post: pre,
                    dyn: dyn,
                    postGamma: g
                };
            });
            this.addHandler("Declare", Statement_1.StatementDeclare, function (s, pre, g, onErr) {
                var ex = new Expression_1.ExpressionX(s.x);
                var xT = ex.getType(env, g);
                if (xT) {
                    onErr("already defined");
                    return null;
                }
                pre = pre.woVar(s.x);
                pre = pre.append(new VerificationFormula_1.FormulaPartEq(ex, s.T.defaultValue()));
                return {
                    post: pre,
                    dyn: VerificationFormula_1.VerificationFormula.empty(),
                    postGamma: Gamma_1.GammaAdd(s.x, s.T, g)
                };
            });
        }
        Hoare.prototype.addHandler = function (rule, SS, check) {
            var y = Statement_1.StatementAlloc;
            var x;
            this.ruleHandlers.push({
                name: rule,
                statementMatch: function (s) { return s instanceof SS; },
                check: check
            });
        };
        Hoare.prototype.getRule = function (s) {
            for (var _i = 0, _a = this.ruleHandlers; _i < _a.length; _i++) {
                var rule = _a[_i];
                if (rule.statementMatch(s))
                    return rule;
            }
            throw "unknown statement type";
        };
        Hoare.prototype.check = function (s, pre, g) {
            var rule = this.getRule(s);
            var errs = [];
            var res = rule.check(s, pre, g, function (msg) { return errs.push(msg); });
            return res == null ? errs : null;
        };
        Hoare.prototype.post = function (s, pre, g) {
            var rule = this.getRule(s);
            var errs = [];
            return rule.check(s, pre, g, function (msg) { return errs.push(msg); });
        };
        return Hoare;
    }());
    exports.Hoare = Hoare;
});
