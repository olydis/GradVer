define(["require", "exports", "../types/VerificationFormula", "../types/Statement", "../types/Type", "../types/Expression"], function (require, exports, VerificationFormula_1, Statement_1, Type_1, Expression_1) {
    "use strict";
    var Hoare = (function () {
        function Hoare(env) {
            var _this = this;
            this.env = env;
            this.ruleHandlers = [];
            this.addHandler("NewObject", Statement_1.StatementAlloc, function (s, pre, onErr) {
                var fs = _this.env.fields(s.C);
                // check
                if (fs == null) {
                    onErr("class '" + s.C + "' not found");
                    return null;
                }
                return { fs: fs };
            }, function (s) { return [s.x]; }, function (s, phi, params) {
                var res = [];
                res.push(new VerificationFormula_1.FormulaPartType(s.x, new Type_1.TypeClass(s.C)));
                res.push.apply(res, phi.parts);
                return new VerificationFormula_1.VerificationFormula(null, res);
            }, function (s, phi, params) {
                var ex = new Expression_1.ExpressionX(s.x);
                var res = [];
                res.push.apply(res, params.fs.map(function (f) { return new VerificationFormula_1.FormulaPartAcc(ex, f.name); }));
                res.push(new VerificationFormula_1.FormulaPartType(s.x, new Type_1.TypeClass(s.C)));
                res.push(new VerificationFormula_1.FormulaPartNeq(ex, Expression_1.ExpressionX.getNull()));
                res.push.apply(res, phi.parts);
                return new VerificationFormula_1.VerificationFormula(null, res);
            });
            this.addHandler("FieldAssign", Statement_1.StatementMemberSet, function (s, pre, onErr) {
                var Tx = pre.staticFormula.tryGetType(s.x);
                if (!(Tx instanceof Type_1.TypeClass)) {
                    if (pre.gradual)
                        return { C: null, T: null };
                    onErr("couldn't determine type of '" + s.x + "'");
                    return null;
                }
                var Cx = Tx;
                var Cf = _this.env.fieldType(Cx.C, s.f);
                // check
                if (Cf == null) {
                    onErr("class '" + Cx + "' doesn't have field '" + s.f + "'");
                    return null;
                }
                return { C: Cx, T: Cf };
            }, function (s) { return []; }, function (s, phi, params) {
                var ex = new Expression_1.ExpressionX(s.x);
                var res = [];
                if (params.C)
                    res.push(new VerificationFormula_1.FormulaPartType(s.x, params.C));
                if (params.T)
                    res.push(new VerificationFormula_1.FormulaPartType(s.y, params.T));
                res.push.apply(res, phi.parts);
                res.push(new VerificationFormula_1.FormulaPartAcc(ex, s.f));
                return new VerificationFormula_1.VerificationFormula(null, res);
            }, function (s, phi, params) {
                var ex = new Expression_1.ExpressionX(s.x);
                var res = [];
                if (params.C)
                    res.push(new VerificationFormula_1.FormulaPartType(s.x, params.C));
                res.push(new VerificationFormula_1.FormulaPartAcc(ex, s.f));
                res.push(new VerificationFormula_1.FormulaPartEq(new Expression_1.ExpressionDot(ex, s.f), new Expression_1.ExpressionX(s.y)));
                res.push.apply(res, phi.parts);
                return new VerificationFormula_1.VerificationFormula(null, res);
            });
            this.addHandler("VarAssign", Statement_1.StatementAssign, function (s, pre, onErr) {
                var Tx = pre.staticFormula.tryGetType(s.x);
                if (Tx == null) {
                    if (pre.gradual)
                        return { T: null, Tx: null };
                    onErr("couldn't determine type of '" + s.x + "'");
                    return null;
                }
                var Te = _this.env.tryGetType(pre.staticFormula, s.e);
                if (Te == null) {
                    if (pre.gradual)
                        return { T: null, Tx: null };
                    onErr("couldn't determine type of RHS expression");
                    return null;
                }
                var TeCore = _this.env.tryGetCoreType(pre.staticFormula, s.e);
                // check
                if (s.e.FV().some(function (x) { return x == s.x; })) {
                    onErr("RHS expression cannot contain variable '" + s.x + "'");
                    return null;
                }
                if (!Type_1.Type.eq(Tx, Te)) {
                    onErr("type mismatch");
                    return null;
                }
                return { T: Te, Tx: TeCore };
            }, function (s) { return [s.x]; }, function (s, phi, params) {
                var ex = new Expression_1.ExpressionX(s.x);
                var res = [];
                if (params.T)
                    res.push(new VerificationFormula_1.FormulaPartType(s.x, params.T));
                if (params.Tx)
                    res.push.apply(res, _this.unfoldTypeFormula(s.e, params.Tx));
                res.push.apply(res, phi.parts);
                return new VerificationFormula_1.VerificationFormula(null, res);
            }, function (s, phi, params) {
                var ex = new Expression_1.ExpressionX(s.x);
                var res = [];
                if (params.Tx)
                    res.push.apply(res, _this.unfoldTypeFormula(s.e, params.Tx));
                res.push.apply(res, phi.parts);
                res.push(new VerificationFormula_1.FormulaPartEq(ex, s.e));
                return new VerificationFormula_1.VerificationFormula(null, res);
            });
            this.addHandler("Return", Statement_1.StatementReturn, function (s, pre, onErr) {
                var Tx = pre.staticFormula.tryGetType(s.x);
                if (Tx == null) {
                    if (pre.gradual)
                        return { T: null };
                    onErr("couldn't determine type of '" + s.x + "'");
                    return null;
                }
                return { T: Tx };
            }, function (s) { return [Expression_1.Expression.getResult()]; }, function (s, phi, params) {
                var ex = new Expression_1.ExpressionX(s.x);
                var res = [];
                if (params.T)
                    res.push(new VerificationFormula_1.FormulaPartType(s.x, params.T));
                res.push(new VerificationFormula_1.FormulaPartType(Expression_1.Expression.getResult(), params.T));
                res.push.apply(res, phi.parts);
                return new VerificationFormula_1.VerificationFormula(null, res);
            }, function (s, phi, params) {
                var ex = new Expression_1.ExpressionX(s.x);
                var res = [];
                if (params.T)
                    res.push(new VerificationFormula_1.FormulaPartType(Expression_1.Expression.getResult(), params.T));
                res.push(new VerificationFormula_1.FormulaPartEq(new Expression_1.ExpressionX(Expression_1.Expression.getResult()), ex));
                res.push.apply(res, phi.parts);
                return new VerificationFormula_1.VerificationFormula(null, res);
            });
            this.addHandler("Call", Statement_1.StatementCall, function (s, pre, onErr) {
                var Ty = pre.staticFormula.tryGetType(s.y);
                if (!(Ty instanceof Type_1.TypeClass)) {
                    if (pre.gradual)
                        return { m: null, C: null };
                    onErr("'" + s.y + "' must have class type");
                    return null;
                }
                var Cy = Ty;
                var m = _this.env.mmethod(Cy.C, s.m);
                // check
                if (m == null) {
                    onErr("class '" + Cy + "' doesn't have method '" + s.m + "'");
                    return null;
                }
                if (s.x == s.y || s.x == s.z) {
                    onErr("'" + s.x + "' cannot appear both in LHS and RHS");
                    return null;
                }
                return { m: m, C: Cy };
            }, function (s) { return [s.x]; }, function (s, phi, params) {
                var ex = new Expression_1.ExpressionX(s.x);
                var res = [];
                if (params.m)
                    res.push(new VerificationFormula_1.FormulaPartType(s.x, params.m.retType));
                if (params.C)
                    res.push(new VerificationFormula_1.FormulaPartType(s.y, params.C));
                if (params.m)
                    res.push(new VerificationFormula_1.FormulaPartType(s.z, params.m.argType));
                res.push.apply(res, phi.parts);
                res.push(new VerificationFormula_1.FormulaPartNeq(new Expression_1.ExpressionX(s.y), Expression_1.Expression.getNull()));
                if (params.m)
                    res.push.apply(res, params.m.frmPre.staticFormula.substs(function (x) {
                        if (x == Expression_1.Expression.getThis())
                            return s.y;
                        if (x == params.m.argName)
                            return s.z;
                        return x;
                    }).parts);
                return new VerificationFormula_1.VerificationFormula(null, res);
            }, function (s, phi, params) {
                var ex = new Expression_1.ExpressionX(s.x);
                var res = [];
                res.push.apply(res, phi.parts);
                if (params.m)
                    res.push.apply(res, params.m.frmPre.staticFormula.substs(function (x) {
                        if (x == Expression_1.Expression.getThis())
                            return s.y;
                        if (x == params.m.argName)
                            return s.z;
                        if (x == Expression_1.Expression.getResult())
                            return s.x;
                        return x;
                    }).parts);
                return new VerificationFormula_1.VerificationFormula(null, res);
            });
            this.addHandler("Assert", Statement_1.StatementAssert, function (s, pre, onErr) {
                if (!pre.impliesApprox(s.assertion)) {
                    onErr("couldn't prove assertion");
                    return null;
                }
                return {};
            }, function (s) { return []; }, function (s, phi, params) {
                return phi;
            }, function (s, phi, params) {
                return phi;
            });
            this.addHandler("Release", Statement_1.StatementRelease, function (s, pre, onErr) {
                return {};
            }, function (s) { return []; }, function (s, phi, params) {
                return new VerificationFormula_1.VerificationFormula(null, phi.parts.concat(s.assertion.parts));
            }, function (s, phi, params) {
                return phi;
            });
            this.addHandler("Declare", Statement_1.StatementDeclare, function (s, pre, onErr) {
                return {};
            }, function (s) { return [s.x]; }, function (s, phi, params) {
                return phi;
            }, function (s, phi, params) {
                var res = [];
                res.push(new VerificationFormula_1.FormulaPartType(s.x, s.T));
                res.push(new VerificationFormula_1.FormulaPartEq(new Expression_1.ExpressionX(s.x), s.T.defaultValue()));
                res.push.apply(res, phi.parts);
                return new VerificationFormula_1.VerificationFormula(null, res);
            });
        }
        Hoare.prototype.addHandler = function (rule, SS, getParams, notInPhi, getPre, getPost) {
            var y = Statement_1.StatementAlloc;
            var x;
            this.ruleHandlers.push({
                name: rule,
                statementMatch: function (s) { return s instanceof SS; },
                params: getParams,
                notInPhi: notInPhi,
                pre: getPre,
                post: getPost
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
        Hoare.prototype.check = function (s, pre) {
            var rule = this.getRule(s);
            var errs = [];
            var res = rule.params(s, pre, function (msg) { return errs.push(msg); });
            return res == null ? errs : null;
        };
        Hoare.prototype.guessPhiFromPre = function (s, pre) {
            var rule = this.getRule(s);
            var params = rule.params(s, pre, function () { });
            var barePre = rule.pre(s, VerificationFormula_1.VerificationFormula.empty(), params);
            var nonos = rule.notInPhi(s);
            var isNono = function (x) { return nonos.indexOf(x) != -1; };
            var remaining = pre.staticFormula.parts.filter(function (p1) { return !(p1 instanceof VerificationFormula_1.FormulaPartAcc &&
                barePre.parts.some(function (p2) { return VerificationFormula_1.FormulaPart.eq(p1, p2); })); });
            remaining = remaining.filter(function (p) { return p.FV().every(function (x) { return !isNono(x); }); });
            return new VerificationFormula_1.VerificationFormula(null, remaining);
        };
        Hoare.prototype.guessPhiFromPost = function (s, pre, post) {
            var rule = this.getRule(s);
            var params = rule.params(s, pre, function () { });
            var barePost = rule.post(s, VerificationFormula_1.VerificationFormula.empty(), params);
            var nonos = rule.notInPhi(s);
            var isNono = function (x) { return nonos.indexOf(x) != -1; };
            var remaining = post.staticFormula.parts.filter(function (p1) { return !(barePost.parts.some(function (p2) { return VerificationFormula_1.FormulaPart.eq(p1, p2); })); });
            remaining = remaining.filter(function (p) { return p.FV().every(function (x) { return !isNono(x); }); });
            return new VerificationFormula_1.VerificationFormula(null, remaining);
        };
        Hoare.prototype.guessPhi = function (s, pre, post) {
            var phiPre = this.guessPhiFromPre(s, pre);
            var phiPost = this.guessPhiFromPost(s, pre, post);
            return VerificationFormula_1.VerificationFormula.intersect(phiPre, phiPost);
        };
        Hoare.prototype.genPost = function (s, pre, post) {
            var rule = this.getRule(s);
            var params = rule.params(s, pre, function () { });
            var phi = this.guessPhi(s, pre, post);
            return rule.post(s, phi, params);
        };
        Hoare.prototype.genPre = function (s, pre, post) {
            var rule = this.getRule(s);
            var params = rule.params(s, pre, function () { });
            var phi = this.guessPhi(s, pre, post);
            return rule.pre(s, phi, params);
        };
        Hoare.prototype.validate = function (s, pre, post) {
            var check = this.check(s, pre);
            if (check)
                return check;
            var rule = this.getRule(s);
            var params = rule.params(s, pre, function () { });
            var phi = this.guessPhiFromPost(s, pre, post);
            var xpre = rule.pre(s, phi, params);
            var xpost = rule.post(s, phi, params);
            if (!pre.impliesApprox(xpre))
                return ["couldn't prove pre implication"];
            if (!post.containsApprox(xpost))
                return ["couldn't prove post membership"];
            return null;
        };
        Hoare.prototype.unfoldTypeFormula = function (e, coreType) {
            if (e instanceof Expression_1.ExpressionV)
                return [];
            if (e instanceof Expression_1.ExpressionX)
                return [new VerificationFormula_1.FormulaPartType(e.x, coreType)];
            if (e instanceof Expression_1.ExpressionDot)
                return this.unfoldTypeFormula(e.e, coreType).concat([new VerificationFormula_1.FormulaPartAcc(e.e, e.f)]);
            throw "unexpected subclass";
        };
        return Hoare;
    }());
    exports.Hoare = Hoare;
});
