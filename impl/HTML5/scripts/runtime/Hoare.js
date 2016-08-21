define(["require", "exports", "../types/VerificationFormula", "../types/VerificationFormulaGradual", "../types/Statement", "../types/Type", "../types/Expression", "./Gamma"], function (require, exports, VerificationFormula_1, VerificationFormulaGradual_1, Statement_1, Type_1, Expression_1, Gamma_1) {
    "use strict";
    var Hoare = (function () {
        function Hoare(env) {
            var _this = this;
            this.env = env;
            this.ruleHandlers = [];
            this.addHandler("NewObject", Statement_1.StatementAlloc, function (s, g, onErr) {
                var ex = new Expression_1.ExpressionX(s.x);
                var fs = _this.env.fields(s.C);
                if (fs == null) {
                    onErr("class '" + s.C + "' not found");
                    return null;
                }
                var exT = ex.getType(env, g);
                if (!new Type_1.TypeClass(s.C).compatibleWith(exT)) {
                    onErr("type mismatch: " + s.C + " <-> " + exT);
                    return null;
                }
                return {
                    info: {
                        ex: ex,
                        fs: fs
                    },
                    postGamma: g
                };
            }, function (info) { return VerificationFormula_1.VerificationFormula.empty(); }, function (info, pre) {
                pre = pre.woVar(info.ex.x);
                pre = pre.append(new VerificationFormula_1.FormulaPartNeq(info.ex, Expression_1.Expression.getNull()));
                for (var _i = 0, _a = info.fs; _i < _a.length; _i++) {
                    var f = _a[_i];
                    pre = pre.append(new VerificationFormula_1.FormulaPartAcc(info.ex, f.name));
                }
                return pre;
            });
            this.addHandler("FieldAssign", Statement_1.StatementMemberSet, function (s, g, onErr) {
                var ex = new Expression_1.ExpressionX(s.x);
                var ey = new Expression_1.ExpressionX(s.y);
                var CT = ex.getType(env, g);
                if (CT instanceof Type_1.TypeClass) {
                    var C = CT.C;
                    var fT = _this.env.fieldType(C, s.f);
                    if (fT == null) {
                        onErr("field not found");
                        return null;
                    }
                    var eyT = ey.getType(env, g);
                    if (!fT.compatibleWith(eyT)) {
                        onErr("type mismatch: " + fT + " <-> " + eyT);
                        return null;
                    }
                    return {
                        info: {
                            ex: ex,
                            ey: ey,
                            f: s.f
                        },
                        postGamma: g
                    };
                }
                onErr(ex + " not declared (as class type)");
                return null;
            }, function (info) { return new VerificationFormula_1.FormulaPartAcc(info.ex, info.f).asFormula(); }, function (info, pre) {
                pre = pre.woAcc(info.ex, info.f);
                pre = pre.append(new VerificationFormula_1.FormulaPartAcc(info.ex, info.f));
                pre = pre.append(new VerificationFormula_1.FormulaPartNeq(info.ex, Expression_1.Expression.getNull()));
                pre = pre.append(new VerificationFormula_1.FormulaPartEq(new Expression_1.ExpressionDot(info.ex, info.f), info.ey));
                return pre;
            });
            this.addHandler("VarAssign", Statement_1.StatementAssign, function (s, g, onErr) {
                var ex = new Expression_1.ExpressionX(s.x);
                var xT = ex.getType(env, g);
                var eT = s.e.getType(env, g);
                if (xT == null) {
                    onErr(ex + " not declared");
                    return null;
                }
                if (!xT.compatibleWith(eT)) {
                    onErr("type mismatch: " + xT + " <-> " + eT);
                    return null;
                }
                if (s.e.FV().indexOf(s.x) != -1) {
                    onErr("LHS not to appear in RHS");
                    return null;
                }
                return {
                    info: {
                        ex: ex,
                        e: s.e
                    },
                    postGamma: g
                };
            }, function (info) { return new VerificationFormula_1.VerificationFormula(null, info.e.necessaryFraming().slice(0, 1).map(function (a) { return new VerificationFormula_1.FormulaPartAcc(a.e, a.f); })); }, function (info, pre) {
                pre = pre.woVar(info.ex.x);
                pre = pre.append(new VerificationFormula_1.FormulaPartEq(info.ex, info.e));
                return pre;
            });
            this.addHandler("Return", Statement_1.StatementReturn, function (s, g, onErr) {
                var ex = new Expression_1.ExpressionX(s.x);
                var er = new Expression_1.ExpressionX(Expression_1.Expression.getResult());
                var xT = ex.getType(env, g);
                var rT = er.getType(env, g);
                if (xT == null) {
                    onErr(ex + " not declared");
                    return null;
                }
                if (!xT.compatibleWith(rT)) {
                    onErr("type mismatch: " + xT + " <-> " + rT);
                    return null;
                }
                return {
                    info: {
                        ex: ex,
                        er: er
                    },
                    postGamma: g
                };
            }, function (info) { return VerificationFormula_1.VerificationFormula.empty(); }, function (info, pre) {
                pre = pre.woVar(Expression_1.Expression.getResult());
                pre = pre.append(new VerificationFormula_1.FormulaPartEq(info.er, info.ex));
                return pre;
            });
            this.addHandler("Call", Statement_1.StatementCall, function (s, g, onErr) {
                var ex = new Expression_1.ExpressionX(s.x);
                var ey = new Expression_1.ExpressionX(s.y);
                var ez = new Expression_1.ExpressionX(s.z);
                var exT = ex.getType(env, g);
                var eyT = ey.getType(env, g);
                var ezT = ez.getType(env, g);
                if (s.x == s.y || s.x == s.z) {
                    onErr("LHS not to appear in RHS");
                    return null;
                }
                if (eyT instanceof Type_1.TypeClass) {
                    var C = eyT.C;
                    var m = _this.env.mmethod(C, s.m);
                    if (m == null) {
                        onErr("method not found");
                        return null;
                    }
                    if (!m.retType.compatibleWith(exT)) {
                        onErr("type mismatch: " + m.retType + " <-> " + exT);
                        return null;
                    }
                    if (!m.argType.compatibleWith(ezT)) {
                        onErr("type mismatch: " + m.argType + " <-> " + ezT);
                        return null;
                    }
                    var p_pre = m.frmPre.substs(function (xx) {
                        if (xx == Expression_1.Expression.getThis())
                            return s.y;
                        if (xx == m.argName)
                            return s.z;
                        return xx;
                    });
                    var p_post = m.frmPost.substs(function (xx) {
                        if (xx == Expression_1.Expression.getThis())
                            return s.y;
                        if (xx == m.argName)
                            return s.z;
                        if (xx == Expression_1.Expression.getResult())
                            return s.x;
                        return xx;
                    });
                    return {
                        info: {
                            pre: p_pre,
                            post: p_post,
                            ynn: new VerificationFormula_1.FormulaPartNeq(ey, Expression_1.Expression.getNull()),
                            x: s.x
                        },
                        postGamma: g
                    };
                }
                onErr(ey + " not declared (as class type)");
                return null;
            }, function (info) { return info.pre.append(info.ynn).staticFormula; }, function (info, pre) {
                pre = pre.woVar(info.x);
                if (info.pre.gradual)
                    for (var _i = 0, _a = pre.staticFormula.footprintStatic(); _i < _a.length; _i++) {
                        var fp = _a[_i];
                        pre = pre.woAcc(fp.e, fp.f);
                    }
                else
                    for (var _b = 0, _c = info.pre.staticFormula.footprintStatic(); _b < _c.length; _b++) {
                        var fp = _c[_b];
                        pre = pre.woAcc(fp.e, fp.f);
                    }
                for (var _d = 0, _e = info.post.staticFormula.parts; _d < _e.length; _d++) {
                    var p_part = _e[_d];
                    pre = pre.append(p_part);
                }
                // gradualness of info.post and info.pre
                pre = VerificationFormulaGradual_1.VerificationFormulaGradual.create(info.pre.gradual || info.post.gradual || pre.gradual, pre.staticFormula);
                return pre;
            });
            this.addHandler("Assert", Statement_1.StatementAssert, function (s, g, onErr) {
                return {
                    info: s.assertion,
                    postGamma: g
                };
            }, function (info) { return info; }, function (info, pre) {
                return pre;
            });
            this.addHandler("Release", Statement_1.StatementRelease, function (s, g, onErr) {
                return {
                    info: s.assertion,
                    postGamma: g
                };
            }, function (info) { return info; }, function (info, pre) {
                for (var _i = 0, _a = info.footprintStatic(); _i < _a.length; _i++) {
                    var fp = _a[_i];
                    pre = pre.woAcc(fp.e, fp.f);
                }
                return pre;
            });
            this.addHandler("Declare", Statement_1.StatementDeclare, function (s, g, onErr) {
                var ex = new Expression_1.ExpressionX(s.x);
                var xT = ex.getType(env, g);
                if (xT) {
                    onErr("conflicting declaration");
                    return null;
                }
                return {
                    info: {
                        ex: ex,
                        T: s.T
                    },
                    postGamma: Gamma_1.GammaAdd(s.x, s.T, g)
                };
            }, function (info) { return VerificationFormula_1.VerificationFormula.empty(); }, function (info, pre) {
                pre = pre.woVar(info.ex.x);
                pre = pre.append(new VerificationFormula_1.FormulaPartEq(info.ex, info.T.defaultValue()));
                return pre;
            });
            this.addHandler("Cast", Statement_1.StatementCast, function (s, g, onErr) {
                return {
                    info: s.T,
                    postGamma: g
                };
            }, function (info) { return info.staticFormula; }, function (info, pre) {
                return info;
            });
            this.addHandler("Comment", Statement_1.StatementComment, function (s, g, onErr) {
                return {
                    info: {},
                    postGamma: g
                };
            }, function (info) { return VerificationFormula_1.VerificationFormula.empty(); }, function (info, pre) {
                return pre;
            });
        }
        Hoare.prototype.addHandler = function (rule, SS, 
            // returns null on error
            checkStrucural, 
            // cannot fail
            checkImplication, 
            // cannot fail
            checkPost) {
            var y = Statement_1.StatementAlloc;
            var x;
            this.ruleHandlers.push({
                name: rule,
                statementMatch: function (s) { return s instanceof SS; },
                checkStrucural: checkStrucural,
                checkImplication: checkImplication,
                checkPost: checkPost
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
        Hoare.prototype.checkMethod = function (g, s, pre, post) {
            s = s.slice();
            s.push(new Statement_1.StatementCast(post));
            for (var _i = 0, s_1 = s; _i < s_1.length; _i++) {
                var ss = s_1[_i];
                var err = this.check(ss, pre, g);
                if (err != null)
                    return ss + " failed check: " + err.join(", ");
                var res = this.post(ss, pre, g);
                pre = res.post;
                g = res.postGamma;
            }
            return null;
        };
        Hoare.prototype.check = function (s, pre, g) {
            var rule = this.getRule(s);
            var errs = [];
            var res = rule.checkStrucural(s, g, function (msg) { return errs.push(msg); });
            if (res == null)
                return errs;
            var dyn = rule.checkImplication(res.info);
            var prex = pre.implies(dyn);
            if (prex == null)
                return ["could not prove: " + dyn];
            return null;
        };
        Hoare.prototype.post = function (s, pre, g) {
            var rule = this.getRule(s);
            var errs = [];
            var res = rule.checkStrucural(s, g, function (msg) { return errs.push(msg); });
            if (res == null)
                throw "call check first";
            var dyn = rule.checkImplication(res.info);
            pre = pre.implies(dyn);
            if (pre == null)
                throw "call check first";
            return {
                post: rule.checkPost(res.info, pre),
                dyn: dyn,
                postGamma: res.postGamma
            };
        };
        return Hoare;
    }());
    exports.Hoare = Hoare;
});
