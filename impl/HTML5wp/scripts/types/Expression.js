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
define(["require", "exports", "./ValueExpression", "./Type"], function (require, exports, ValueExpression_1, Type_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    var Expression = /** @class */ (function () {
        function Expression() {
        }
        Expression.prototype.substs = function (m) {
            if (this instanceof ExpressionX)
                return new ExpressionX(m(this.x));
            var frm = this.necessaryFraming();
            if (frm.length > 0) {
                var x = frm.filter(function (x) { return x.e instanceof ExpressionX; })[0].e.x;
                return this.subste(new ExpressionX(x), new ExpressionX(m(x)));
            }
            return this;
        };
        Expression.prototype.subste = function (a, b) {
            if (Expression.eq(a, this))
                return b;
            else
                return this;
        };
        Expression.prototype.necessaryFraming = function () {
            return [];
        };
        Expression.eq = function (e1, e2) {
            return e1.toString() == e2.toString();
        };
        Expression.parse = function (source) {
            source = source.replace(/\s/g, "");
            var result = null;
            if (!result)
                result = ExpressionDot.parse(source);
            if (!result)
                result = ExpressionV.parse(source);
            if (!result)
                result = ExpressionX.parse(source);
            return result;
        };
        Expression.isValidX = function (source) {
            if (source == null)
                return false;
            return source.search(/^[A-Za-z_][A-Za-z_0-9]*$/) == 0;
        };
        Expression.getNull = function () {
            return new ExpressionV(ValueExpression_1.ValueExpression.getNull());
        };
        Expression.getZero = function () {
            return new ExpressionV(ValueExpression_1.ValueExpression.getZero());
        };
        Expression.getResult = function () { return "result"; };
        ;
        Expression.getThis = function () { return "this"; };
        ;
        return Expression;
    }());
    exports.Expression = Expression;
    var ExpressionV = /** @class */ (function (_super) {
        __extends(ExpressionV, _super);
        function ExpressionV(v) {
            var _this = _super.call(this) || this;
            _this.v = v;
            if (v == null)
                throw "null arg";
            return _this;
        }
        ExpressionV.parse = function (source) {
            var vex = ValueExpression_1.ValueExpression.parse(source);
            return vex != null
                ? new ExpressionV(vex)
                : null;
        };
        ExpressionV.prototype.toString = function () {
            return this.v.toString();
        };
        ExpressionV.prototype.sfrm = function (fp) {
            return true;
        };
        ExpressionV.prototype.depth = function () {
            return 0;
        };
        ExpressionV.prototype.FV = function () { return []; };
        ExpressionV.prototype.eval = function (env) {
            return this.v;
        };
        ExpressionV.prototype.getType = function (env, g) {
            return this.v.getType();
        };
        return ExpressionV;
    }(Expression));
    exports.ExpressionV = ExpressionV;
    var ExpressionX = /** @class */ (function (_super) {
        __extends(ExpressionX, _super);
        function ExpressionX(x) {
            var _this = _super.call(this) || this;
            _this.x = x;
            if (!Expression.isValidX(x))
                throw "null arg";
            return _this;
        }
        ExpressionX.parse = function (source) {
            return Expression.isValidX(source)
                ? new ExpressionX(source)
                : null;
        };
        ExpressionX.prototype.toString = function () {
            return this.x;
        };
        ExpressionX.prototype.sfrm = function (fp) {
            return true;
        };
        ExpressionX.prototype.depth = function () {
            return 1;
        };
        ExpressionX.prototype.FV = function () { return [this.x]; };
        ExpressionX.prototype.eval = function (env) {
            return env.r[this.x];
        };
        ExpressionX.prototype.getType = function (env, g) {
            return g(this.x);
        };
        return ExpressionX;
    }(Expression));
    exports.ExpressionX = ExpressionX;
    var ExpressionDot = /** @class */ (function (_super) {
        __extends(ExpressionDot, _super);
        function ExpressionDot(e, f) {
            var _this = _super.call(this) || this;
            _this.e = e;
            _this.f = f;
            if (e == null)
                throw "null arg";
            if (!Expression.isValidX(f))
                throw "null arg";
            return _this;
        }
        ExpressionDot.parse = function (source) {
            var dotIndex = source.lastIndexOf(".");
            if (dotIndex == -1)
                return null;
            var e = Expression.parse(source.substr(0, dotIndex));
            var f = source.substr(dotIndex + 1);
            return e != null && Expression.isValidX(f)
                ? new ExpressionDot(e, f)
                : null;
        };
        ExpressionDot.prototype.toString = function () {
            return this.e.toString() + "." + this.f;
        };
        ExpressionDot.prototype.sfrm = function (fp) {
            var _this = this;
            return this.e.sfrm(fp)
                && fp.some(function (fpx) { return Expression.eq(_this.e, fpx.e) && _this.f == fpx.f; });
        };
        ExpressionDot.prototype.depth = function () {
            return 1 + this.e.depth();
        };
        ExpressionDot.prototype.subste = function (a, b) {
            var ex = this.e.subste(a, b);
            var thisx = new ExpressionDot(ex, this.f);
            if (Expression.eq(a, thisx))
                return b;
            else
                return thisx;
        };
        ExpressionDot.prototype.FV = function () { return this.e.FV(); };
        ExpressionDot.prototype.eval = function (env) {
            var inner = this.e.eval(env);
            if (inner instanceof ValueExpression_1.ValueObject) {
                var HEntry = env.H[inner.UID];
                if (!HEntry)
                    return null;
                return HEntry.fs[this.f];
            }
            return null;
        };
        ExpressionDot.prototype.getType = function (env, g) {
            var inner = this.e.getType(env, g);
            if (inner instanceof Type_1.TypeClass) {
                var fieldType = env.fieldType(inner.C, this.f);
                if (!fieldType)
                    return undefined;
                return fieldType;
            }
            return undefined;
        };
        ExpressionDot.prototype.necessaryFraming = function () {
            var res = this.e.necessaryFraming();
            res.unshift({ e: this.e, f: this.f });
            return res;
        };
        return ExpressionDot;
    }(Expression));
    exports.ExpressionDot = ExpressionDot;
});
