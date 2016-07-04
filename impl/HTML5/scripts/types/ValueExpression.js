var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports", "./Type"], function (require, exports, Type_1) {
    "use strict";
    var ValueExpression = (function () {
        function ValueExpression() {
        }
        ValueExpression.parse = function (source) {
            source = source.replace(/\s/g, "");
            var result = null;
            if (!result)
                result = ValueExpressionNull.parse(source);
            if (!result)
                result = ValueExpressionN.parse(source);
            return result;
        };
        ValueExpression.getNull = function () {
            return new ValueExpressionNull();
        };
        ValueExpression.getZero = function () {
            return new ValueExpressionN(0);
        };
        return ValueExpression;
    }());
    exports.ValueExpression = ValueExpression;
    var ValueExpressionN = (function (_super) {
        __extends(ValueExpressionN, _super);
        function ValueExpressionN(n) {
            _super.call(this);
            this.n = n;
            if (n == null)
                throw "null arg";
            this.n = Math.max(0, Math.round(this.n));
        }
        ValueExpressionN.parse = function (source) {
            var n = parseInt(source);
            return !isNaN(n)
                ? new ValueExpressionN(n)
                : null;
        };
        ValueExpressionN.prototype.createHTML = function () {
            return $("<span>").text(this.n.toString());
        };
        ValueExpressionN.prototype.getType = function () {
            return Type_1.Type.getPrimitiveInt();
        };
        return ValueExpressionN;
    }(ValueExpression));
    exports.ValueExpressionN = ValueExpressionN;
    var ValueExpressionNull = (function (_super) {
        __extends(ValueExpressionNull, _super);
        function ValueExpressionNull() {
            _super.apply(this, arguments);
        }
        ValueExpressionNull.parse = function (source) {
            return source.toLocaleLowerCase() == "null"
                ? new ValueExpressionNull()
                : null;
        };
        ValueExpressionNull.prototype.createHTML = function () {
            return $("<span>").text("null");
        };
        ValueExpressionNull.prototype.getType = function () {
            return null;
        };
        return ValueExpressionNull;
    }(ValueExpression));
    exports.ValueExpressionNull = ValueExpressionNull;
});
