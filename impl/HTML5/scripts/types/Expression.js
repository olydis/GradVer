var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports", "./ValueExpression"], function (require, exports, ValueExpression_1) {
    "use strict";
    var Expression = (function () {
        function Expression() {
        }
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
            return source.search(/^[A-Za-z]+$/) == 0;
        };
        return Expression;
    }());
    exports.Expression = Expression;
    var ExpressionV = (function (_super) {
        __extends(ExpressionV, _super);
        function ExpressionV(v) {
            _super.call(this);
            this.v = v;
            if (v == null)
                throw "null arg";
        }
        ExpressionV.parse = function (source) {
            var vex = ValueExpression_1.ValueExpression.parse(source);
            return vex != null
                ? new ExpressionV(vex)
                : null;
        };
        ExpressionV.prototype.createHTML = function () {
            return this.v.createHTML();
        };
        return ExpressionV;
    }(Expression));
    exports.ExpressionV = ExpressionV;
    var ExpressionX = (function (_super) {
        __extends(ExpressionX, _super);
        function ExpressionX(x) {
            _super.call(this);
            this.x = x;
            if (!Expression.isValidX(x))
                throw "null arg";
        }
        ExpressionX.parse = function (source) {
            return source != ""
                ? new ExpressionX(source)
                : null;
        };
        ExpressionX.prototype.createHTML = function () {
            return $("<span>").text(this.x);
        };
        return ExpressionX;
    }(Expression));
    exports.ExpressionX = ExpressionX;
    var ExpressionDot = (function (_super) {
        __extends(ExpressionDot, _super);
        function ExpressionDot(e, f) {
            _super.call(this);
            this.e = e;
            this.f = f;
            if (e == null)
                throw "null arg";
            if (!Expression.isValidX(f))
                throw "null arg";
        }
        ExpressionDot.parse = function (source) {
            var dotIndex = source.lastIndexOf(".");
            if (dotIndex == -1)
                return null;
            var e = Expression.parse(source.substr(0, dotIndex));
            var f = source.substr(dotIndex + 1);
            return e != null
                ? new ExpressionDot(e, f)
                : null;
        };
        ExpressionDot.prototype.createHTML = function () {
            return $("<span>")
                .append(this.e.createHTML())
                .append($("<span>").text("." + this.f));
        };
        return ExpressionDot;
    }(Expression));
    exports.ExpressionDot = ExpressionDot;
});
