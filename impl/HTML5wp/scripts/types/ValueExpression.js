var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports", "./Type"], function (require, exports, Type_1) {
    "use strict";
    var Value = (function () {
        function Value() {
        }
        return Value;
    }());
    exports.Value = Value;
    var ValueObject = (function (_super) {
        __extends(ValueObject, _super);
        function ValueObject(uid) {
            if (uid === void 0) { uid = null; }
            var _this = _super.call(this) || this;
            _this.uid = uid;
            if (uid === null)
                _this.uid = ValueObject._uid++;
            return _this;
        }
        ValueObject.reset = function () { ValueObject._uid = 0; };
        ValueObject.prototype.equalTo = function (other) {
            return other instanceof ValueObject && this.uid == other.uid;
        };
        Object.defineProperty(ValueObject.prototype, "UID", {
            get: function () { return this.uid; },
            enumerable: true,
            configurable: true
        });
        ValueObject.prototype.toString = function () {
            return "<" + this.uid + ">";
        };
        return ValueObject;
    }(Value));
    ValueObject._uid = 0;
    exports.ValueObject = ValueObject;
    var ValueExpression = (function (_super) {
        __extends(ValueExpression, _super);
        function ValueExpression() {
            return _super.apply(this, arguments) || this;
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
    }(Value));
    exports.ValueExpression = ValueExpression;
    var ValueExpressionN = (function (_super) {
        __extends(ValueExpressionN, _super);
        function ValueExpressionN(n) {
            var _this = _super.call(this) || this;
            _this.n = n;
            if (n == null)
                throw "null arg";
            _this.n = Math.round(_this.n);
            return _this;
        }
        ValueExpressionN.parse = function (source) {
            var n = parseInt(source);
            return !isNaN(n)
                ? new ValueExpressionN(n)
                : null;
        };
        ValueExpressionN.prototype.equalTo = function (other) {
            return other instanceof ValueExpressionN && other.n == this.n;
        };
        ValueExpressionN.prototype.toString = function () {
            return this.n.toString();
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
            return _super.apply(this, arguments) || this;
        }
        ValueExpressionNull.parse = function (source) {
            return source.toLocaleLowerCase() == "null"
                ? new ValueExpressionNull()
                : null;
        };
        ValueExpressionNull.prototype.equalTo = function (other) {
            return other instanceof ValueExpressionNull;
        };
        ValueExpressionNull.prototype.toString = function () {
            return "null";
        };
        ValueExpressionNull.prototype.getType = function () {
            return null;
        };
        return ValueExpressionNull;
    }(ValueExpression));
    exports.ValueExpressionNull = ValueExpressionNull;
});
