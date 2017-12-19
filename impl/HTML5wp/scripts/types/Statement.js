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
define(["require", "exports", "./VerificationFormula", "./VerificationFormulaGradual", "./Type", "./Expression", "../runtime/StackEnv", "./ValueExpression"], function (require, exports, VerificationFormula_1, VerificationFormulaGradual_1, Type_1, Expression_1, StackEnv_1, ValueExpression_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    var Statement = /** @class */ (function () {
        function Statement() {
        }
        Statement.prototype.writesTo = function (x) {
            return false;
        };
        Statement.parse = function (source) {
            var fallBack = new StatementComment(source.trim() == ""
                ? " write a statement here"
                : " parse error: " + source);
            var result = null;
            source = source.replace(/;\s*$/, "");
            var sourceWS = source;
            try {
                if (!result)
                    result = StatementHold.parse(source);
                if (!result)
                    result = StatementUnhold.parse(source);
                if (!result)
                    result = StatementComment.parse(source);
                if (!result)
                    result = StatementCast.parse(source);
                source = source.replace(/\s/g, "");
                if (!result)
                    result = StatementCall.parse(source);
                if (!result)
                    result = StatementAlloc.parse(source);
                if (!result)
                    result = StatementAssert.parse(source);
                if (!result)
                    result = StatementRelease.parse(source);
                if (!result)
                    result = StatementReturn.parse(source);
                if (!result)
                    result = StatementMemberSet.parse(source);
                if (!result)
                    result = StatementAssign.parse(source);
                if (!result)
                    result = StatementDeclare.parse(sourceWS);
                if (!result)
                    result = fallBack;
            }
            catch (e) {
                console.error("parse error");
                result = fallBack;
            }
            return result;
        };
        return Statement;
    }());
    exports.Statement = Statement;
    var StatementMemberSet = /** @class */ (function (_super) {
        __extends(StatementMemberSet, _super);
        function StatementMemberSet(x, f, y) {
            var _this = _super.call(this) || this;
            _this.x = x;
            _this.f = f;
            _this.y = y;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(f))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(y))
                throw "null arg";
            return _this;
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
    var StatementAssign = /** @class */ (function (_super) {
        __extends(StatementAssign, _super);
        function StatementAssign(x, e) {
            var _this = _super.call(this) || this;
            _this.x = x;
            _this.e = e;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
            if (e == null)
                throw "null arg";
            return _this;
        }
        StatementAssign.prototype.writesTo = function (x) {
            return this.x == x;
        };
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
            var topIdx = env.S.length - 1;
            env.S[topIdx].r[this.x] = v;
            return env;
        };
        return StatementAssign;
    }(Statement));
    exports.StatementAssign = StatementAssign;
    var StatementAlloc = /** @class */ (function (_super) {
        __extends(StatementAlloc, _super);
        function StatementAlloc(x, C) {
            var _this = _super.call(this) || this;
            _this.x = x;
            _this.C = C;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(C))
                throw "null arg";
            return _this;
        }
        StatementAlloc.prototype.writesTo = function (x) {
            return this.x == x;
        };
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
            var topIdx = env.S.length - 1;
            env.H[o] = { C: this.C, fs: {} };
            env.S[topIdx].r[this.x] = vo;
            for (var _i = 0, fs_1 = fs; _i < fs_1.length; _i++) {
                var f = fs_1[_i];
                env.H[o].fs[f.name] = f.type.defaultValue().eval(envx);
                env.S[topIdx].A.push({ o: o, f: f.name });
            }
            return env;
        };
        return StatementAlloc;
    }(Statement));
    exports.StatementAlloc = StatementAlloc;
    var StatementCall = /** @class */ (function (_super) {
        __extends(StatementCall, _super);
        function StatementCall(x, y, m, z) {
            var _this = _super.call(this) || this;
            _this.x = x;
            _this.y = y;
            _this.m = m;
            _this.z = z;
            if (x !== null && !Expression_1.Expression.isValidX(x))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(y))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(m))
                throw "null arg";
            if (z.some(function (z) { return !Expression_1.Expression.isValidX(z); }))
                throw "null arg";
            return _this;
        }
        StatementCall.prototype.writesTo = function (x) {
            return this.x == x;
        };
        StatementCall.parse = function (source) {
            var eqIndex = source.indexOf(":=");
            if (eqIndex == -1)
                eqIndex = source.indexOf("=");
            var x;
            var b;
            if (eqIndex == -1) {
                // store result nowhere
                x = null;
                b = source;
            }
            else {
                x = source.substr(0, eqIndex);
                b = source.substr(eqIndex + 1).replace(/=/g, "");
            }
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
            return new StatementCall(x, y, m, z.split(",").filter(function (z) { return z; }));
        };
        StatementCall.prototype.toString = function () {
            return (this.x === null ? "" : this.x + " := ") + this.y + "." + this.m + "(" + this.z.join(", ") + ");";
        };
        StatementCall.prototype.smallStep = function (env, context) {
            var envx = StackEnv_1.topEnv(env);
            env = StackEnv_1.cloneStackEnv(env);
            var isEntry = env.S[env.S.length - 1].ss.length != 0;
            if (!isEntry)
                env.S.pop();
            var vo = new Expression_1.ExpressionX(this.y).eval(StackEnv_1.topEnv(env));
            if (vo instanceof ValueExpression_1.ValueObject) {
                var o = vo.UID;
                var Hentry = envx.H[o];
                if (Hentry == null)
                    return null;
                var m = context.mmethod(Hentry.C, this.m);
                if (m == null || m.name != this.m)
                    return null;
                if (isEntry) {
                    if (env.S[env.S.length - 1].ss[0] != this)
                        throw "dispatch failure";
                    var rr = {};
                    rr[Expression_1.Expression.getResult()] = m.retType.defaultValue().eval(envx);
                    rr[Expression_1.Expression.getThis()] = vo;
                    for (var i = 0; i < m.args.length; ++i) {
                        var v = new Expression_1.ExpressionX(this.z[i]).eval(envx);
                        if (v == null)
                            return null;
                        rr[m.args[i].name] = v;
                    }
                    if (!m.frmPre.eval({ H: envx.H, r: rr, A: envx.A }))
                        return null;
                    var AA = m.frmPre.gradual ? envx.A : m.frmPre.staticFormula.footprintDynamic({ H: envx.H, r: rr, A: envx.A });
                    var topIdx = env.S.length - 1;
                    env.S[topIdx].A = env.S[topIdx].A.filter(function (a) { return !AA.some(function (b) { return a.f == b.f && a.o == b.o; }); });
                    env.S.push({
                        r: rr,
                        A: AA,
                        ss: m.body
                    });
                }
                else {
                    if (env.S[env.S.length - 1].ss.shift() != this)
                        throw "dispatch failure";
                    if (!m.frmPost.eval(envx))
                        return null;
                    var vr = new Expression_1.ExpressionX(Expression_1.Expression.getResult()).eval(envx);
                    if (vr == null)
                        return null;
                    var topIdx = env.S.length - 1;
                    if (this.x !== null)
                        env.S[topIdx].r[this.x] = vr;
                    (_a = env.S[topIdx].A).push.apply(_a, envx.A);
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
    var StatementReturn = /** @class */ (function (_super) {
        __extends(StatementReturn, _super);
        function StatementReturn(x) {
            var _this = _super.call(this) || this;
            _this.x = x;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
            return _this;
        }
        StatementReturn.prototype.writesTo = function (x) {
            return Expression_1.Expression.getResult() == x;
        };
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
            var topIdx = env.S.length - 1;
            env.S[topIdx].r[Expression_1.Expression.getResult()] = v;
            return env;
        };
        return StatementReturn;
    }(Statement));
    exports.StatementReturn = StatementReturn;
    var StatementAssert = /** @class */ (function (_super) {
        __extends(StatementAssert, _super);
        function StatementAssert(assertion) {
            var _this = _super.call(this) || this;
            _this.assertion = assertion;
            return _this;
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
    var StatementRelease = /** @class */ (function (_super) {
        __extends(StatementRelease, _super);
        function StatementRelease(assertion) {
            var _this = _super.call(this) || this;
            _this.assertion = assertion;
            return _this;
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
            var topIdx = env.S.length - 1;
            env.S[topIdx].A = env.S[topIdx].A.filter(function (a) { return !AA.some(function (b) { return a.f == b.f && a.o == b.o; }); });
            return env;
        };
        return StatementRelease;
    }(Statement));
    exports.StatementRelease = StatementRelease;
    var StatementDeclare = /** @class */ (function (_super) {
        __extends(StatementDeclare, _super);
        function StatementDeclare(T, x) {
            var _this = _super.call(this) || this;
            _this.T = T;
            _this.x = x;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
            return _this;
        }
        StatementDeclare.prototype.writesTo = function (x) {
            return this.x == x;
        };
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
            var topIdx = env.S.length - 1;
            env.S[topIdx].r[this.x] = this.T.defaultValue().eval(envx);
            return env;
        };
        return StatementDeclare;
    }(Statement));
    exports.StatementDeclare = StatementDeclare;
    // EXTENSIONS
    var StatementCast = /** @class */ (function (_super) {
        __extends(StatementCast, _super);
        function StatementCast(T) {
            var _this = _super.call(this) || this;
            _this.T = T;
            return _this;
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
    var StatementComment = /** @class */ (function (_super) {
        __extends(StatementComment, _super);
        function StatementComment(comment) {
            var _this = _super.call(this) || this;
            _this.comment = comment;
            return _this;
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
    var StatementHold = /** @class */ (function (_super) {
        __extends(StatementHold, _super);
        function StatementHold(p) {
            var _this = _super.call(this) || this;
            _this.p = p;
            if (p == null)
                throw "null arg";
            return _this;
        }
        StatementHold.parse = function (source) {
            if (source.slice(0, 4) != "hold")
                return null;
            source = source.slice(4);
            if (source.charAt(source.length - 1) == "{")
                source = source.slice(0, source.length - 1);
            return new StatementHold(new VerificationFormula_1.VerificationFormula(source));
        };
        StatementHold.prototype.toString = function () {
            return "hold " + this.p + " {";
        };
        StatementHold.prototype.smallStep = function (env, context) {
            var envx = StackEnv_1.topEnv(env);
            env = StackEnv_1.cloneStackEnv(env);
            var isEntry = env.S[env.S.length - 1].ss.length != 0;
            if (!isEntry)
                env.S.pop();
            if (isEntry) {
                // ESHold
                if (env.S[env.S.length - 1].ss[0] != this)
                    throw "dispatch failure";
                if (!this.p.eval(envx))
                    return null;
                var AA = this.p.footprintDynamic(envx);
                var topIdx = env.S.length - 1;
                var Awo = env.S[topIdx].A.filter(function (a) { return !AA.some(function (b) { return a.f == b.f && a.o == b.o; }); });
                env.S[topIdx].A = AA;
                env.S.push({
                    r: envx.r,
                    A: Awo,
                    ss: env.S[topIdx].ss.slice(1)
                });
            }
            else {
                // exit handled by closing curly... so scope not closed if we get here
                return null;
            }
            return env;
        };
        return StatementHold;
    }(Statement));
    exports.StatementHold = StatementHold;
    var StatementUnhold = /** @class */ (function (_super) {
        __extends(StatementUnhold, _super);
        function StatementUnhold() {
            return _super.call(this) || this;
        }
        StatementUnhold.parse = function (source) {
            if (source != "}")
                return null;
            return new StatementUnhold();
        };
        StatementUnhold.prototype.toString = function () {
            return "}";
        };
        StatementUnhold.prototype.smallStep = function (env, context) {
            var envx = StackEnv_1.topEnv(env);
            env = StackEnv_1.cloneStackEnv(env);
            // ESHoldFinish
            var top = env.S.pop();
            if (top === undefined || top.ss.shift() != this)
                throw "dispatch failure";
            // reset next stack frame
            var ss = env.S[env.S.length - 1].ss;
            var entryStmt = ss[0];
            ss = ss.slice(ss.indexOf(this) + 1);
            env.S[env.S.length - 1].ss = ss;
            // update env
            var topIdx = env.S.length - 1;
            (_a = env.S[topIdx].A).push.apply(_a, envx.A);
            env.S[topIdx].r = envx.r;
            return env;
            var _a;
        };
        return StatementUnhold;
    }(Statement));
    exports.StatementUnhold = StatementUnhold;
});
// export class StatementSugar extends Statement
// {
//     public constructor(
//         public children: Statement[])
//     {
//         super();
//     }
//     public static parse(source: string): Statement
//     {
//         source = source.trim();
//         if (source.charAt(0) != '/')
//             return null;
//         if (source.charAt(1) != '/')
//             return null;
//         source = source.slice(2);
//         return new StatementComment(source);
//     }
//     public toString(): string
//     {
//         return "";
//     }
//     public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
//     {
//         env = cloneStackEnv(env);
//         if (env.S[env.S.length - 1].ss.shift() != this)
//             throw "dispatch failure";
//         return env;
//     }
// } 
