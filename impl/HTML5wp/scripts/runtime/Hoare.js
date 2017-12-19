define(["require", "exports", "../types/VerificationFormula", "../types/VerificationFormulaGradual", "../types/Statement", "../types/Type", "../types/Expression", "./Gamma"], function (require, exports, VerificationFormula_1, VerificationFormulaGradual_1, Statement_1, Type_1, Expression_1, Gamma_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    var Hoare = /** @class */ (function () {
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
            }, function (info, post) {
                var pre = post.woVar(info.ex.x);
                // remodel
                var xpost = pre.append(new VerificationFormula_1.FormulaPartNeq(info.ex, Expression_1.Expression.getNull()));
                for (var _i = 0, _a = info.fs; _i < _a.length; _i++) {
                    var f = _a[_i];
                    xpost = xpost.append(new VerificationFormula_1.FormulaPartAcc(info.ex, f.name));
                }
                // cannot say more than xpost
                if (!pre.satisfiable() || null == xpost.implies(post.staticFormula))
                    return null;
                return [pre, xpost.impliesRemaindors(post.staticFormula)];
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
            }, function (info, post) {
                var pre = post;
                pre = pre.subste(new Expression_1.ExpressionDot(info.ex, info.f), info.ey);
                pre = pre.woAcc(info.ex, info.f).append(new VerificationFormula_1.FormulaPartAcc(info.ex, info.f));
                // remodel
                var xpost = pre.append(new VerificationFormula_1.FormulaPartEq(new Expression_1.ExpressionDot(info.ex, info.f), info.ey));
                // cannot say more than xpost
                if (!pre.satisfiable() || null == xpost.implies(post.staticFormula))
                    return null;
                return [pre, xpost.impliesRemaindors(post.staticFormula)];
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
            }, function (info, post) {
                var pre = post.subste(info.ex, info.e);
                for (var _i = 0, _a = info.e.necessaryFraming().map(function (x) { return new VerificationFormula_1.FormulaPartAcc(x.e, x.f); }); _i < _a.length; _i++) {
                    var frm = _a[_i];
                    if (!pre.implies(frm.asFormula()))
                        pre = pre.append(frm);
                } // TODO: verify that order is right...
                // remodel
                var xpost = pre.append(new VerificationFormula_1.FormulaPartEq(info.ex, info.e));
                // cannot say more than xpost
                if (!pre.satisfiable() || null == xpost.implies(post.staticFormula))
                    return null;
                return [pre, xpost.impliesRemaindors(post.staticFormula)];
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
            }, function (info, post) {
                var pre = post.woVar(Expression_1.Expression.getResult());
                // remodel
                var xpost = pre.append(new VerificationFormula_1.FormulaPartEq(info.er, info.ex));
                // cannot say more than xpost
                if (!pre.satisfiable() || null == xpost.implies(post.staticFormula))
                    return null;
                return [pre, xpost.impliesRemaindors(post.staticFormula)];
            });
            this.addHandler("Call", Statement_1.StatementCall, function (s, g, onErr) {
                var ex = s.x === null ? null : new Expression_1.ExpressionX(s.x);
                var ey = new Expression_1.ExpressionX(s.y);
                var ezs = s.z.map(function (z) { return new Expression_1.ExpressionX(z); });
                var exT = ex === null ? null : ex.getType(env, g);
                var eyT = ey.getType(env, g);
                var ezTs = ezs.map(function (z) { return z.getType(env, g); });
                if (s.x == s.y || s.z.some(function (z) { return z === s.x; })) {
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
                    if (exT !== null && !m.retType.compatibleWith(exT)) {
                        onErr("type mismatch: " + m.retType + " <-> " + exT);
                        return null;
                    }
                    if (m.args.length !== ezTs.length) {
                        onErr("argument count mismatch: expected " + m.args.length + " but provided " + ezTs.length);
                        return null;
                    }
                    for (var i = 0; i < m.args.length; ++i) {
                        if (!m.args[i].type.compatibleWith(ezTs[i])) {
                            onErr("type mismatch: " + m.args[i].type + " <-> " + ezTs[i]);
                            return null;
                        }
                    }
                    var p_pre = m.frmPre.substs(function (xx) {
                        if (xx == Expression_1.Expression.getThis())
                            return s.y;
                        for (var i = 0; i < m.args.length; ++i)
                            if (xx == m.args[i].name)
                                return s.z[i];
                        return xx;
                    });
                    var p_post = m.frmPost.substs(function (xx) {
                        if (xx == Expression_1.Expression.getThis())
                            return s.y;
                        for (var i = 0; i < m.args.length; ++i)
                            if (xx == m.args[i].name)
                                return s.z[i];
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
            }, function (info, post) {
                var pre = post;
                if (info.x !== null)
                    pre = pre.woVar(info.x);
                // framed off part
                if (info.post.gradual)
                    pre = VerificationFormulaGradual_1.VerificationFormulaGradual.qm();
                else
                    for (var _i = 0, _a = info.post.staticFormula.footprintStatic(); _i < _a.length; _i++) {
                        var acc = _a[_i];
                        pre = pre.woAcc(acc.e, acc.f);
                    }
                // pre
                if (info.pre.gradual)
                    pre.gradual = true;
                for (var _b = 0, _c = info.pre.staticFormula.parts; _b < _c.length; _b++) {
                    var prep = _c[_b];
                    pre.staticFormula = pre.staticFormula.append(prep);
                }
                pre.staticFormula = pre.staticFormula.append(info.ynn);
                // remodel
                var xpost = pre;
                if (info.x !== null)
                    xpost = xpost.woVar(info.x);
                if (info.pre.gradual)
                    for (var _d = 0, _e = xpost.staticFormula.autoFraming(); _d < _e.length; _d++) {
                        var fp1 = _e[_d];
                        xpost = xpost.woAcc(fp1.e, fp1.f);
                    }
                else
                    for (var _f = 0, _g = info.pre.staticFormula.footprintStatic(); _f < _g.length; _f++) {
                        var fp2 = _g[_f];
                        xpost = xpost.woAcc(fp2.e, fp2.f);
                    }
                for (var _h = 0, _j = info.post.staticFormula.parts; _h < _j.length; _h++) {
                    var p_part = _j[_h];
                    xpost = xpost.append(p_part);
                }
                // gradualness of info.post and info.pre
                xpost = VerificationFormulaGradual_1.VerificationFormulaGradual.create(info.pre.gradual || info.post.gradual || xpost.gradual, xpost.staticFormula);
                // cannot say more than xpost
                if (!pre.satisfiable() || null == xpost.implies(post.staticFormula))
                    return null;
                return [pre, xpost.impliesRemaindors(post.staticFormula)];
            });
            this.addHandler("Assert", Statement_1.StatementAssert, function (s, g, onErr) {
                return {
                    info: s.assertion,
                    postGamma: g
                };
            }, function (info, post) {
                return [VerificationFormulaGradual_1.VerificationFormulaGradual.nonSepAnd(post, VerificationFormulaGradual_1.VerificationFormulaGradual.create(false, info)), []];
            });
            this.addHandler("Release", Statement_1.StatementRelease, function (s, g, onErr) {
                return {
                    info: s.assertion,
                    postGamma: g
                };
            }, function (info, post) {
                var pre = VerificationFormulaGradual_1.VerificationFormulaGradual.nonSepAnd(post, VerificationFormulaGradual_1.VerificationFormulaGradual.create(false, info));
                if (pre == null)
                    return null;
                // remodel
                var xpost = pre;
                for (var _i = 0, _a = info.footprintStatic(); _i < _a.length; _i++) {
                    var fp = _a[_i];
                    xpost = xpost.woAcc(fp.e, fp.f);
                }
                // cannot say more than xpost
                if (!pre.satisfiable() || !xpost.impliesFully(post.staticFormula))
                    return null;
                return [pre, xpost.impliesRemaindors(post.staticFormula)];
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
            }, function (info, post) {
                var pre = post.woVar(info.ex.x);
                // remodel
                var xpost = pre.append(new VerificationFormula_1.FormulaPartEq(info.ex, info.T.defaultValue()));
                // cannot say more than xpost
                if (!pre.satisfiable() || null == xpost.implies(post.staticFormula))
                    return null;
                return [pre, xpost.impliesRemaindors(post.staticFormula)];
            });
            this.addHandler("Cast", Statement_1.StatementCast, function (s, g, onErr) {
                return {
                    info: s.T,
                    postGamma: g
                };
            }, function (info, post) {
                // must have chance of implying the postcondnition
                if (!info.satisfiable() || null == info.implies(post.staticFormula))
                    return null;
                return [info, info.impliesRemaindors(post.staticFormula)];
            });
            this.addHandler("Comment", Statement_1.StatementComment, function (s, g, onErr) {
                return {
                    info: {},
                    postGamma: g
                };
            }, function (info, post) {
                return [post, []];
            });
            this.addHandler("Hold", Statement_1.StatementHold, function (s, g, onErr, scopeStack) {
                if (!s.p.sfrm()) {
                    onErr("framed-off formula must be self-framed");
                    return null;
                }
                var readOnly = s.p.FV();
                scopeStack.push({
                    gamma: g,
                    checkInnerStmt: function (s) {
                        if (readOnly.some(function (x) { return s.writesTo(x); }))
                            return "writes to protected variable";
                        return null;
                    },
                    postProc: s.p
                });
                return {
                    info: { phi: s.p, gamma: g },
                    postGamma: g
                };
            }, function (info, post) {
                var pre = VerificationFormulaGradual_1.VerificationFormulaGradual.nonSepAnd(post, VerificationFormulaGradual_1.VerificationFormulaGradual.create(false, info.phi));
                if (pre == null)
                    return null;
                // remodel
                var xpost = pre;
                for (var _i = 0, _a = info.phi.footprintStatic(); _i < _a.length; _i++) {
                    var fp = _a[_i];
                    xpost = xpost.woAcc(fp.e, fp.f);
                }
                // cannot say more than xpost
                if (!pre.satisfiable() || !xpost.impliesFully(post.staticFormula))
                    return null;
                return [pre, []];
            });
            this.addHandler("Unhold", Statement_1.StatementUnhold, function (s, g, onErr, postProcStack) {
                if (postProcStack.length == 0) {
                    onErr("no scope to close");
                    return null;
                }
                var top = postProcStack.pop();
                return {
                    info: top.postProc,
                    postGamma: top.gamma
                };
            }, function (info, post) {
                var framedOff = info;
                var readOnly = info.FV();
                for (var _i = 0, _a = framedOff.footprintStatic(); _i < _a.length; _i++) {
                    var fp = _a[_i];
                    post = post.woAcc(fp.e, fp.f);
                }
                // for (var fv of readOnly)
                //     post = post.woVar(fv);
                return [post, []]; // TODO
            }
            // ,
            // (info) => VerificationFormula.empty(),
            // (info, pre, postProcStack) => {
            //     var proc = postProcStack.pop();
            //     return proc.postProc(pre);
            // }
            );
        }
        Hoare.prototype.addHandler = function (rule, SS, 
            // returns null on error
            checkStrucural, 
            // cannot fail
            wlp) {
            var y = Statement_1.StatementAlloc;
            var x;
            this.ruleHandlers.push({
                name: rule,
                statementMatch: function (s) { return s instanceof SS; },
                checkStrucural: checkStrucural,
                wlp: wlp
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
            var scopePostProcStack = [];
            var infos = [];
            var result = [];
            // init
            result.push({ g: g, wlp: null, residual: [], error: null, scopeStack: [] });
            for (var _i = 0, s_1 = s; _i < s_1.length; _i++) {
                var ss = s_1[_i];
                result.push({ g: null /*of +*/, wlp: null /*of - below*/, residual: [] /*of - above*/, error: null /*of - above*/, scopeStack: [] /*of +*/ });
            }
            // structural check and parse
            for (var i = 0; i < s.length; ++i) {
                var ss = s[i];
                // nested stuff checking
                for (var _a = 0, scopePostProcStack_1 = scopePostProcStack; _a < scopePostProcStack_1.length; _a++) {
                    var scopeItem = scopePostProcStack_1[_a];
                    var err = scopeItem.checkInnerStmt(ss);
                    if (err != null) {
                        result[i + 1].error = "ill-formed: " + err;
                        return result;
                    }
                }
                // parse & check structure
                var rule = this.getRule(ss);
                var errs = [];
                var res = rule.checkStrucural(ss, result[i].g, function (msg) { return errs.push(msg); }, scopePostProcStack);
                if (res == null) {
                    result[i + 1].error = "ill-formed: " + errs.join(", ");
                    return result;
                }
                infos.push(res.info);
                result[i + 1].g = res.postGamma;
                result[i + 1].scopeStack = scopePostProcStack.slice();
            }
            // scopes closed?
            if (scopePostProcStack.length != 0) {
                result[0].error = "scopes not closed";
                return result;
            }
            // WLP
            result[s.length].wlp = post;
            for (var i = s.length - 1; i >= 0; --i) {
                var residual = [];
                if (post != null) {
                    var ress = this.getRule(s[i]).wlp(infos[i], post, result[i].scopeStack);
                    if (ress == null || ress[0] == null || !ress[0].satisfiable() || !ress[0].sfrm()) {
                        result[i + 1].error = "verification failed (WLP undefined)";
                        return result;
                    }
                    post = ress[0];
                    residual = ress[1];
                }
                result[i + 1].residual = residual;
                result[i].wlp = post;
            }
            // valid
            if (pre.implies(post.staticFormula) != null)
                result[0].residual = pre.impliesRemaindors(post.staticFormula);
            else
                result[0].error = "verification failed (precondition does not imply WLP)";
            return result;
        };
        return Hoare;
    }());
    exports.Hoare = Hoare;
});
