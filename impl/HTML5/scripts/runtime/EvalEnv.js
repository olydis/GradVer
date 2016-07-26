define(["require", "exports", "../types/Expression", "../types/ValueExpression", "../types/VerificationFormula"], function (require, exports, Expression_1, ValueExpression_1, VerificationFormula_1) {
    "use strict";
    function cloneHeapEntry(He) {
        var res = { C: He.C, fs: {} };
        for (var f in He.fs)
            res.fs[f] = He.fs[f];
        return res;
    }
    function cloneHeap(H) {
        var res = {};
        for (var o in H)
            res[o] = cloneHeapEntry(H[o]);
        return res;
    }
    function cloneRho(rho) {
        var res = {};
        for (var x in rho)
            res[x] = rho[x];
        return res;
    }
    function cloneAccess(A) {
        var res = [];
        for (var _i = 0, A_1 = A; _i < A_1.length; _i++) {
            var a = A_1[_i];
            res.push({ o: a.o, f: a.f });
        }
        return res;
    }
    function cloneEvalEnv(env) {
        return { H: cloneHeap(env.H),
            r: cloneRho(env.r),
            A: cloneAccess(env.A) };
    }
    var NormalizedEnv = (function () {
        function NormalizedEnv(ineq, env) {
            if (ineq === void 0) { ineq = []; }
            if (env === void 0) { env = { H: {}, r: {}, A: [] }; }
            this.ineq = ineq;
            this.env = env;
        }
        NormalizedEnv.create = function (ineq, env) {
            if (ineq === void 0) { ineq = []; }
            if (env === void 0) { env = { H: {}, r: {}, A: [] }; }
            var result = new NormalizedEnv(ineq, env);
            return result.getConsistent() ? result : null;
        };
        NormalizedEnv.mergeObjHeapFields = function (fs1, fs2) {
            var res = [];
            for (var f in fs1) {
                if (fs2[f])
                    res.push({ v1: fs1[f], v2: fs2[f] });
                fs2[f] = fs1[f];
            }
            return res;
        };
        NormalizedEnv.mergeObjHeap = function (o, v, H) {
            H = cloneHeap(H);
            var HEntry = H[o];
            if (!HEntry)
                return { H: H, todo: [] };
            if (v instanceof ValueExpression_1.ValueObject) {
                var oo = v.UID;
                var todo = [];
                if (H[oo]) {
                    if (HEntry.C != H[oo].C)
                        return null;
                    todo = NormalizedEnv.mergeObjHeapFields(HEntry.fs, H[oo].fs);
                }
                else
                    H[oo] = H[o];
                delete H[o];
                return { H: H, todo: todo };
            }
            return null;
        };
        NormalizedEnv.mergeObjHeapC = function (vo, v, H) {
            H = cloneHeap(H);
            for (var o in H) {
                var fs = H[o].fs;
                for (var f in fs)
                    if (fs[f].equalTo(vo))
                        fs[f] = v;
            }
            return H;
        };
        NormalizedEnv.mergeObjAccess = function (o, v, A) {
            if (v instanceof ValueExpression_1.ValueObject)
                return A.map(function (a) { return { o: a.o == o ? v.UID : a.o, f: a.f }; });
            return A.some(function (a) { return a.o == o; })
                ? null
                : A;
        };
        NormalizedEnv.mergeObjIneq = function (vo, v, ineq) {
            return ineq.map(function (a) {
                return {
                    v1: a.v1 == vo ? v : a.v1,
                    v2: a.v2 == vo ? v : a.v2 };
            });
        };
        NormalizedEnv.prototype.createFormula = function () {
            var _this = this;
            var dfs = function (e, seen, todo) {
                var v = e.eval(_this.env);
                todo(e, v);
                if (v instanceof ValueExpression_1.ValueObject) {
                    var o = v.UID;
                    if (seen.indexOf(o) == -1) {
                        seen = seen.concat([o]);
                        var he = _this.env.H[o];
                        if (he) {
                            var fs = he.fs;
                            for (var f in fs)
                                dfs(new Expression_1.ExpressionDot(e, f), seen, todo);
                        }
                    }
                }
            };
            var dfsx = function (todo) {
                for (var x in _this.env.r)
                    dfs(new Expression_1.ExpressionX(x), [], todo);
            };
            // collect reachable objects
            var reachableObjects = [];
            dfsx(function (e, v) {
                if (v instanceof ValueExpression_1.ValueObject)
                    reachableObjects.push({ e: e, o: v.UID });
            });
            var os = reachableObjects.map(function (x) { return x.o; }).sort();
            os = os.filter(function (x, i) { return i == 0 || os[i - 1] != x; });
            var objs = {};
            for (var _i = 0, os_1 = os; _i < os_1.length; _i++) {
                var o = os_1[_i];
                objs[o] = reachableObjects.filter(function (x) { return x.o == o; }).map(function (x) { return x.e; }).sort(function (a, b) { return a.depth() - b.depth(); });
            }
            // BUILD
            var parts = [];
            // accs
            for (var _a = 0, _b = this.env.A; _a < _b.length; _a++) {
                var acc = _b[_a];
                if (objs[acc.o])
                    parts.push(new VerificationFormula_1.FormulaPartAcc(objs[acc.o][0], acc.f));
            }
            // ineq
            var getExpression = function (v) {
                if (v instanceof ValueExpression_1.ValueExpression)
                    return new Expression_1.ExpressionV(v);
                if (v instanceof ValueExpression_1.ValueObject) {
                    var o = v.UID;
                    if (objs[o])
                        return objs[o][0];
                    return null;
                }
                throw "unknown subtype";
            };
            for (var _c = 0, _d = this.ineq; _c < _d.length; _c++) {
                var ineq = _d[_c];
                var e1 = getExpression(ineq.v1);
                var e2 = getExpression(ineq.v2);
                if (e1 && e2)
                    parts.push(new VerificationFormula_1.FormulaPartNeq(e1, e2));
            }
            // eq
            dfsx(function (e, v) {
                var ex = getExpression(v);
                if (ex)
                    parts.push(new VerificationFormula_1.FormulaPartEq(e, ex));
            });
            return new VerificationFormula_1.VerificationFormula(null, parts);
        };
        NormalizedEnv.prototype.getEnv = function () { return cloneEvalEnv(this.env); };
        // consistent
        NormalizedEnv.prototype.getConsistentAcc = function () {
            var a = [];
            for (var _i = 0, _a = this.env.A; _i < _a.length; _i++) {
                var x = _a[_i];
                if (a.some(function (y) { return y.f == x.f && y.o == x.o; }))
                    return false;
                a.push(x);
            }
            return true;
        };
        NormalizedEnv.prototype.getConsistentIneq = function () {
            return this.ineq.every(function (x) { return !x.v1.equalTo(x.v2); });
        };
        NormalizedEnv.prototype.getConsistent = function () {
            return this.getConsistentAcc() && this.getConsistentIneq();
        };
        NormalizedEnv.prototype.ensure = function (e) {
            if (e.eval(this.env))
                return this;
            if (e instanceof Expression_1.ExpressionX) {
                var env = this.getEnv();
                env.r[e.x] = new ValueExpression_1.ValueObject();
                return NormalizedEnv.create(this.ineq, env);
            }
            if (e instanceof Expression_1.ExpressionDot) {
                var nenv = this.ensure(e.e);
                if (!nenv)
                    return null;
                var vo = e.e.eval(nenv.env);
                if (vo instanceof ValueExpression_1.ValueObject) {
                    var o = vo.UID;
                    var env = nenv.getEnv();
                    // check heap entry
                    if (!env.H[o])
                        env.H[o] = { C: null, fs: {} };
                    var HEntry = env.H[o];
                    // check field entry
                    if (!HEntry.fs[e.f])
                        HEntry.fs[e.f] = new ValueExpression_1.ValueObject();
                    return NormalizedEnv.create(nenv.ineq, env);
                }
                return null;
            }
            throw "wat";
        };
        NormalizedEnv.prototype.addAccV = function (v, f) {
            if (v instanceof ValueExpression_1.ValueObject) {
                var env = this.getEnv();
                env.A.push({ o: v.UID, f: f });
                return NormalizedEnv.create(this.ineq, env);
            }
            return null;
        };
        NormalizedEnv.prototype.addIneqV = function (v1, v2) {
            return NormalizedEnv.create(this.ineq.concat([{ v1: v1, v2: v2 }]), this.env);
        };
        NormalizedEnv.prototype.mergeObj = function (o, v) {
            var ineq = NormalizedEnv.mergeObjIneq(o, v, this.ineq);
            var acc = NormalizedEnv.mergeObjAccess(o.UID, v, this.env.A);
            var Htodo = NormalizedEnv.mergeObjHeap(o.UID, v, NormalizedEnv.mergeObjHeapC(o, v, this.env.H));
            var rho = cloneRho(this.env.r);
            for (var x in rho)
                if (rho[x].equalTo(o))
                    rho[x] = v;
            if (!ineq || !acc || !Htodo)
                return null;
            var env = NormalizedEnv.create(ineq, { H: Htodo.H, r: rho, A: acc });
            return env
                ? { env: env, todo: Htodo.todo }
                : null;
        };
        NormalizedEnv.prototype.merge = function (v1, v2) {
            if (v1.equalTo(v2))
                return { env: this, todo: [] };
            if (v1 instanceof ValueExpression_1.ValueObject)
                return this.mergeObj(v1, v2);
            if (v2 instanceof ValueExpression_1.ValueObject)
                return this.mergeObj(v2, v1);
            return null;
        };
        NormalizedEnv.prototype.addEqV = function (v1, v2) {
            var res = this;
            var todo = [{ v1: v1, v2: v2 }];
            while (todo.length > 0) {
                var job = todo.pop();
                var mergeRes = res.merge(job.v1, job.v2);
                if (!mergeRes)
                    return null;
                res = mergeRes.env;
                todo.push.apply(todo, mergeRes.todo);
            }
            return res;
        };
        NormalizedEnv.prototype.addAcc = function (e, f) {
            var env = this.ensure(e);
            if (!env)
                return null;
            return env.addAccV(e.eval(env.env), f);
        };
        NormalizedEnv.prototype.addIneq = function (e1, e2) {
            var env = this.ensure(e1);
            if (!env)
                return null;
            env = env.ensure(e2);
            if (!env)
                return null;
            return env.addIneqV(e1.eval(env.env), e2.eval(env.env));
        };
        NormalizedEnv.prototype.addEq = function (e1, e2) {
            var env = this.ensure(e1);
            if (!env)
                return null;
            env = env.ensure(e2);
            if (!env)
                return null;
            return env.addEqV(e1.eval(env.env), e2.eval(env.env));
        };
        NormalizedEnv.prototype.woVar = function (x) {
            var env = cloneEvalEnv(this.env);
            delete env.r[x];
            return NormalizedEnv.create(this.ineq, env);
        };
        NormalizedEnv.prototype.createExpression = function (o) {
            var _this = this;
            var dfs = function (e, seen, todo) {
                var v = e.eval(_this.env);
                todo(e, v);
                if (v instanceof ValueExpression_1.ValueObject) {
                    var o = v.UID;
                    if (seen.indexOf(o) == -1) {
                        seen = seen.concat([o]);
                        var he = _this.env.H[o];
                        if (he) {
                            var fs = he.fs;
                            for (var f in fs)
                                dfs(new Expression_1.ExpressionDot(e, f), seen, todo);
                        }
                    }
                }
            };
            var dfsx = function (todo) {
                for (var x in _this.env.r)
                    dfs(new Expression_1.ExpressionX(x), [], todo);
            };
            // collect reachable objects
            var reachableObjects = [];
            dfsx(function (e, v) {
                if (v instanceof ValueExpression_1.ValueObject)
                    reachableObjects.push({ e: e, o: v.UID });
            });
            var res = reachableObjects.filter(function (x) { return x.o == o; })[0];
            if (res)
                return res.e;
            return null;
        };
        NormalizedEnv.prototype.woAccInternal = function (o, f) {
            var env = cloneEvalEnv(this.env);
            env.A = env.A.filter(function (x) { return x.o != o || x.f != f; });
            var he = env.H[o];
            if (he)
                delete he.fs[f];
            return NormalizedEnv.create(this.ineq, env);
        };
        NormalizedEnv.prototype.woAcc = function (e, f) {
            if (new VerificationFormula_1.FormulaPartAcc(e, f).envImpiledBy(this)) {
                var v = e.eval(this.env);
                if (v instanceof ValueExpression_1.ValueObject)
                    return this.woAccInternal(v.UID, f);
                throw "unreachable";
            }
            else {
                var x = this;
                for (var _i = 0, _a = this.env.A; _i < _a.length; _i++) {
                    var a = _a[_i];
                    if (a.f == f) {
                        var ex = this.createExpression(a.o);
                        if (ex && this.addEq(e, ex) == null) {
                            continue; // aliasing apparently impossible
                        }
                        x = x.woAccInternal(a.o, f);
                    }
                }
                return x;
            }
        };
        return NormalizedEnv;
    }());
    exports.NormalizedEnv = NormalizedEnv;
});
