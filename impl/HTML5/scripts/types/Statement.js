var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports", "./VerificationFormula", "./VerificationFormulaGradual", "./Type", "./Expression", "../runtime/StackEnv", "./ValueExpression"], function (require, exports, VerificationFormula_1, VerificationFormulaGradual_1, Type_1, Expression_1, StackEnv_1, ValueExpression_1) {
    "use strict";
    var Statement = (function () {
        function Statement() {
        }
        Statement.parse = function (source) {
            var result = null;
            source = source.replace(/;$/, "");
            var sourceWS = source;
            try {
                if (!result)
                    result = StatementComment.parse(source);
                source = source.replace(/\s/g, "");
                if (!result)
                    result = StatementCast.parse(source);
                if (!result)
                    result = StatementCall.parse(source);
                if (!result)
                    result = StatementAlloc.parse(source);
                if (!result)
                    result = StatementAssert.parse(source);
                if (!result)
                    result = StatementRelease.parse(source);
                if (!result)
                    result = StatementMemberSet.parse(source);
                if (!result)
                    result = StatementAssign.parse(source);
                if (!result)
                    result = StatementDeclare.parse(sourceWS);
            }
            catch (e) {
                console.error("parse error");
                result = Statement.getNop();
            }
            return result;
        };
        Statement.getNop = function () {
            return new StatementAssert(new VerificationFormula_1.VerificationFormula());
        };
        return Statement;
    }());
    exports.Statement = Statement;
    var StatementMemberSet = (function (_super) {
        __extends(StatementMemberSet, _super);
        function StatementMemberSet(x, f, y) {
            _super.call(this);
            this.x = x;
            this.f = f;
            this.y = y;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(f))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(y))
                throw "null arg";
        }
        StatementMemberSet.parse = function (source) {
            var eqIndex = source.indexOf(":=");
            if (eqIndex == -1)
                eqIndex = source.indexOf("=");
            if (eqIndex == -1)
                return null;
            var a = source.substr(0, eqIndex);
            var b = source.substr(eqIndex + 1).replace(/=/g, "");
            var dotIndex = a.lastIndexOf(".");
            if (dotIndex == -1)
                return null;
            var x = a.substr(0, dotIndex);
            var f = a.substr(dotIndex + 1);
            return new StatementMemberSet(x, f, b);
        };
        StatementMemberSet.prototype.toString = function () {
            return this.x + "." + this.f + " := " + this.y + ";";
        };
        StatementMemberSet.prototype.smallStep = function (env, context) {
            var _this = this;
            var envx = StackEnv_1.topEnv(env);
            env = StackEnv_1.cloneStackEnv(env);
            if (env.S[env.S.length - 1].ss.shift() != this)
                throw "dispatch failure";
            var o = new Expression_1.ExpressionX(this.x).eval(envx);
            if (o instanceof ValueExpression_1.ValueObject) {
                if (!envx.A.some(function (a) { return a.o == o.UID && a.f == _this.f; }))
                    return null;
                var v = new Expression_1.ExpressionX(this.y).eval(envx);
                if (v == null)
                    return null;
                var Hentry = env.H[o.UID];
                if (Hentry == null || Hentry.fs == null)
                    return null;
                Hentry.fs[this.f] = v;
                return env;
            }
            return null;
        };
        return StatementMemberSet;
    }(Statement));
    exports.StatementMemberSet = StatementMemberSet;
    var StatementAssign = (function (_super) {
        __extends(StatementAssign, _super);
        function StatementAssign(x, e) {
            _super.call(this);
            this.x = x;
            this.e = e;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
            if (e == null)
                throw "null arg";
        }
        StatementAssign.parse = function (source) {
            var eqIndex = source.indexOf(":=");
            if (eqIndex == -1)
                eqIndex = source.indexOf("=");
            if (eqIndex == -1)
                return null;
            var a = source.substr(0, eqIndex);
            var b = source.substr(eqIndex + 1).replace(/=/g, "");
            var e = Expression_1.Expression.parse(b);
            return e != null
                ? new StatementAssign(a, e)
                : null;
        };
        StatementAssign.prototype.toString = function () {
            return this.x + " := " + this.e.toString() + ";";
        };
        StatementAssign.prototype.smallStep = function (env, context) {
            var envx = StackEnv_1.topEnv(env);
            env = StackEnv_1.cloneStackEnv(env);
            if (env.S[env.S.length - 1].ss.shift() != this)
                throw "dispatch failure";
            var v = this.e.eval(envx);
            if (v == null)
                return null;
            StackEnv_1.topEnv(env).r[this.x] = v;
            return env;
        };
        return StatementAssign;
    }(Statement));
    exports.StatementAssign = StatementAssign;
    var StatementAlloc = (function (_super) {
        __extends(StatementAlloc, _super);
        function StatementAlloc(x, C) {
            _super.call(this);
            this.x = x;
            this.C = C;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(C))
                throw "null arg";
        }
        StatementAlloc.parse = function (source) {
            var eqIndex = source.indexOf(":=");
            if (eqIndex == -1)
                eqIndex = source.indexOf("=");
            if (eqIndex == -1)
                return null;
            var a = source.substr(0, eqIndex);
            var b = source.substr(eqIndex + 1).replace(/=/g, "");
            if (b.substr(0, 3) != "new")
                return null;
            b = b.substr(3);
            return new StatementAlloc(a, b);
        };
        StatementAlloc.prototype.toString = function () {
            return this.x + " := new " + this.C + ";";
        };
        StatementAlloc.prototype.smallStep = function (env, context) {
            var envx = StackEnv_1.topEnv(env);
            env = StackEnv_1.cloneStackEnv(env);
            if (env.S[env.S.length - 1].ss.shift() != this)
                throw "dispatch failure";
            // find first free object
            var o = 0;
            while (envx.H[o] != null)
                o++;
            var vo = new ValueExpression_1.ValueObject(o);
            var fs = context.fields(this.C);
            if (fs == null)
                return null;
            StackEnv_1.topEnv(env).H[o] = { C: this.C, fs: {} };
            StackEnv_1.topEnv(env).r[this.x] = vo;
            for (var _i = 0, fs_1 = fs; _i < fs_1.length; _i++) {
                var f = fs_1[_i];
                StackEnv_1.topEnv(env).H[o].fs[f.name] = f.type.defaultValue().eval(envx);
                StackEnv_1.topEnv(env).A.push({ o: o, f: f.name });
            }
            return env;
        };
        return StatementAlloc;
    }(Statement));
    exports.StatementAlloc = StatementAlloc;
    var StatementCall = (function (_super) {
        __extends(StatementCall, _super);
        function StatementCall(x, y, m, z) {
            _super.call(this);
            this.x = x;
            this.y = y;
            this.m = m;
            this.z = z;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(y))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(m))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(z))
                throw "null arg";
        }
        StatementCall.parse = function (source) {
            var eqIndex = source.indexOf(":=");
            if (eqIndex == -1)
                eqIndex = source.indexOf("=");
            if (eqIndex == -1)
                return null;
            var x = source.substr(0, eqIndex);
            var b = source.substr(eqIndex + 1).replace(/=/g, "");
            var dotIndex = b.lastIndexOf(".");
            if (dotIndex == -1)
                return null;
            var y = b.substr(0, dotIndex);
            var call = b.substr(dotIndex + 1);
            var braceIndex = call.indexOf("(");
            if (braceIndex == -1)
                return null;
            var m = call.substr(0, braceIndex);
            var z = call.substr(braceIndex + 1).replace(")", "");
            return new StatementCall(x, y, m, z);
        };
        StatementCall.prototype.toString = function () {
            return this.x + " := " + this.y + "." + this.m + "(" + this.z + ");";
        };
        StatementCall.prototype.smallStep = function (env, context) {
            var envx = StackEnv_1.topEnv(env);
            env = StackEnv_1.cloneStackEnv(env);
            var vo = new Expression_1.ExpressionX(this.y).eval(envx);
            if (vo instanceof ValueExpression_1.ValueObject) {
                var o = vo.UID;
                var Hentry = envx.H[o];
                if (Hentry == null)
                    return null;
                var m = context.mmethod(Hentry.C, this.m);
                if (m == null || m.name != this.m)
                    return null;
                if (env.S[env.S.length - 1].ss.length != 0) {
                    if (env.S[env.S.length - 1].ss[0] != this)
                        throw "dispatch failure";
                    var v = new Expression_1.ExpressionX(this.z).eval(envx);
                    if (v == null)
                        return null;
                    var rr = {};
                    rr[Expression_1.Expression.getResult()] = m.retType.defaultValue().eval(envx);
                    rr[Expression_1.Expression.getThis()] = vo;
                    rr[m.argName] = v;
                    if (!m.frmPre.eval(envx))
                        return null;
                    var AA = m.frmPre.gradual ? envx.A : m.frmPre.staticFormula.footprintDynamic({ H: envx.H, r: rr, A: envx.A });
                    StackEnv_1.topEnv(env).A = StackEnv_1.topEnv(env).A.filter(function (a) { return !AA.some(function (b) { return a.f == b.f && a.o == b.o; }); });
                    env.S.push({
                        r: rr,
                        A: AA,
                        ss: m.body
                    });
                }
                else {
                    env.S.pop();
                    if (env.S[env.S.length - 1].ss.shift() != this)
                        throw "dispatch failure";
                    if (!m.frmPost.eval(envx))
                        return null;
                    var vr = new Expression_1.ExpressionX(Expression_1.Expression.getResult()).eval(envx);
                    if (vr == null)
                        return null;
                    StackEnv_1.topEnv(env).r[this.x] = vr;
                    (_a = StackEnv_1.topEnv(env).A).push.apply(_a, envx.A);
                }
                return env;
            }
            else
                return null;
            var _a;
        };
        return StatementCall;
    }(Statement));
    exports.StatementCall = StatementCall;
    var StatementReturn = (function (_super) {
        __extends(StatementReturn, _super);
        function StatementReturn(x) {
            _super.call(this);
            this.x = x;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
        }
        StatementReturn.parse = function (source) {
            if (source.substr(0, 6) != "return")
                return null;
            return new StatementReturn(source.substr(6));
        };
        StatementReturn.prototype.toString = function () {
            return "return " + this.x + ";";
        };
        StatementReturn.prototype.smallStep = function (env, context) {
            var envx = StackEnv_1.topEnv(env);
            env = StackEnv_1.cloneStackEnv(env);
            if (env.S[env.S.length - 1].ss.shift() != this)
                throw "dispatch failure";
            var v = new Expression_1.ExpressionX(this.x).eval(envx);
            if (v == null)
                return null;
            StackEnv_1.topEnv(env).r[Expression_1.Expression.getResult()] = v;
            return env;
        };
        return StatementReturn;
    }(Statement));
    exports.StatementReturn = StatementReturn;
    var StatementAssert = (function (_super) {
        __extends(StatementAssert, _super);
        function StatementAssert(assertion) {
            _super.call(this);
            this.assertion = assertion;
        }
        StatementAssert.parse = function (source) {
            if (source.substr(0, 6) != "assert")
                return null;
            return new StatementAssert(new VerificationFormula_1.VerificationFormula(source.substr(6)));
        };
        StatementAssert.prototype.toString = function () {
            return "assert " + this.assertion.toString() + ";";
        };
        StatementAssert.prototype.smallStep = function (env, context) {
            var envx = StackEnv_1.topEnv(env);
            env = StackEnv_1.cloneStackEnv(env);
            if (env.S[env.S.length - 1].ss.shift() != this)
                throw "dispatch failure";
            if (!this.assertion.eval(envx))
                return null;
            return env;
        };
        return StatementAssert;
    }(Statement));
    exports.StatementAssert = StatementAssert;
    var StatementRelease = (function (_super) {
        __extends(StatementRelease, _super);
        function StatementRelease(assertion) {
            _super.call(this);
            this.assertion = assertion;
        }
        StatementRelease.parse = function (source) {
            if (source.substr(0, 7) != "release")
                return null;
            return new StatementRelease(new VerificationFormula_1.VerificationFormula(source.substr(7)));
        };
        StatementRelease.prototype.toString = function () {
            return "release " + this.assertion.toString() + ";";
        };
        StatementRelease.prototype.smallStep = function (env, context) {
            var envx = StackEnv_1.topEnv(env);
            env = StackEnv_1.cloneStackEnv(env);
            if (env.S[env.S.length - 1].ss.shift() != this)
                throw "dispatch failure";
            if (!this.assertion.eval(envx))
                return null;
            var AA = this.assertion.footprintDynamic(envx);
            StackEnv_1.topEnv(env).A = StackEnv_1.topEnv(env).A.filter(function (a) { return !AA.some(function (b) { return a.f == b.f && a.o == b.o; }); });
            return env;
        };
        return StatementRelease;
    }(Statement));
    exports.StatementRelease = StatementRelease;
    var StatementDeclare = (function (_super) {
        __extends(StatementDeclare, _super);
        function StatementDeclare(T, x) {
            _super.call(this);
            this.T = T;
            this.x = x;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
        }
        StatementDeclare.parse = function (source) {
            var srcParts = source.trim().split(" ");
            if (srcParts.length != 2)
                return null;
            var T = Type_1.Type.parse(srcParts[0]);
            if (T == null)
                return null;
            return new StatementDeclare(T, srcParts[1]);
        };
        StatementDeclare.prototype.toString = function () {
            return this.T.toString() + " " + this.x + ";";
        };
        StatementDeclare.prototype.smallStep = function (env, context) {
            var envx = StackEnv_1.topEnv(env);
            env = StackEnv_1.cloneStackEnv(env);
            if (env.S[env.S.length - 1].ss.shift() != this)
                throw "dispatch failure";
            StackEnv_1.topEnv(env).r[this.x] = this.T.defaultValue().eval(envx);
            return env;
        };
        return StatementDeclare;
    }(Statement));
    exports.StatementDeclare = StatementDeclare;
    // EXTENSIONS
    var StatementCast = (function (_super) {
        __extends(StatementCast, _super);
        function StatementCast(T) {
            _super.call(this);
            this.T = T;
        }
        StatementCast.parse = function (source) {
            source = source.trim();
            if (source.charAt(0) != '{')
                return null;
            if (source.charAt(source.length - 1) != '}')
                return null;
            source = source.slice(1, source.length - 1);
            return new StatementCast(new VerificationFormulaGradual_1.VerificationFormulaGradual(source));
        };
        StatementCast.prototype.toString = function () {
            return "{ " + this.T.toString() + " }";
        };
        StatementCast.prototype.smallStep = function (env, context) {
            env = StackEnv_1.cloneStackEnv(env);
            if (env.S[env.S.length - 1].ss.shift() != this)
                throw "dispatch failure";
            return env;
        };
        return StatementCast;
    }(Statement));
    exports.StatementCast = StatementCast;
    var StatementComment = (function (_super) {
        __extends(StatementComment, _super);
        function StatementComment(comment) {
            _super.call(this);
            this.comment = comment;
        }
        StatementComment.parse = function (source) {
            source = source.trim();
            if (source.charAt(0) != '/')
                return null;
            if (source.charAt(1) != '/')
                return null;
            source = source.slice(2);
            return new StatementComment(source);
        };
        StatementComment.prototype.toString = function () {
            return "//" + this.comment;
        };
        StatementComment.prototype.smallStep = function (env, context) {
            env = StackEnv_1.cloneStackEnv(env);
            if (env.S[env.S.length - 1].ss.shift() != this)
                throw "dispatch failure";
            return env;
        };
        return StatementComment;
    }(Statement));
    exports.StatementComment = StatementComment;
});
