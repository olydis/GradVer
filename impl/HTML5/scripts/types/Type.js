var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports", "./Expression"], function (require, exports, Expression_1) {
    "use strict";
    var Type = (function () {
        function Type() {
        }
        Type.prototype.toString = function () {
            return this.createHTML().text();
        };
        Type.parse = function (source) {
            source = source.replace(/\s/g, "");
            var result = null;
            if (!result)
                result = TypePrimitiveInt.parse(source);
            if (!result)
                result = TypeClass.parse(source);
            return result;
        };
        Type.getPrimitiveInt = function () {
            return new TypePrimitiveInt();
        };
        Type.intersect = function (t1, t2) {
            var resImpossible = { t: null, impossible: true };
            var t1Primitive = !(t1 instanceof TypeClass) && t1 != null;
            var t2Primitive = !(t2 instanceof TypeClass) && t2 != null;
            // compatible primitiveness?
            if (t1Primitive != t2Primitive)
                return resImpossible;
            // class wildcard case (note that we then also KNOW that the other thing is a class)
            if (t1 == null)
                return { t: t2, impossible: false };
            if (t2 == null)
                return { t: t1, impossible: false };
            // types compatible? works for primitive and class
            return t1.toString() == t2.toString() ? { t: t1, impossible: false } : resImpossible;
        };
        Type.implies = function (t1, t2) {
            if (t1 == t2)
                return true; // also covers nulls!
            var t1Primitive = !(t1 instanceof TypeClass) && t1 != null;
            var t2Primitive = !(t2 instanceof TypeClass) && t2 != null;
            // compatible primitiveness?
            if (t1Primitive != t2Primitive)
                return false;
            // class wildcard case (note that we then also KNOW that the other thing is a class)
            if (t1 == null)
                return false;
            if (t2 == null)
                return true;
            // types compatible? works for primitive and class
            return t1.toString() == t2.toString();
        };
        Type.eq = function (t1, t2) {
            return Type.implies(t1, t2) && Type.implies(t2, t1);
        };
        return Type;
    }());
    exports.Type = Type;
    var TypePrimitiveInt = (function (_super) {
        __extends(TypePrimitiveInt, _super);
        function TypePrimitiveInt() {
            _super.apply(this, arguments);
        }
        TypePrimitiveInt.parse = function (source) {
            return source.toLocaleLowerCase() == "int"
                ? new TypePrimitiveInt()
                : null;
        };
        TypePrimitiveInt.prototype.createHTML = function () {
            return $("<span>").text("int");
        };
        TypePrimitiveInt.prototype.defaultValue = function () {
            return Expression_1.Expression.getZero();
        };
        return TypePrimitiveInt;
    }(Type));
    exports.TypePrimitiveInt = TypePrimitiveInt;
    var TypeClass = (function (_super) {
        __extends(TypeClass, _super);
        function TypeClass(C) {
            _super.call(this);
            this.C = C;
            if (!Expression_1.Expression.isValidX(C))
                throw "null arg";
        }
        TypeClass.parse = function (source) {
            if (source == "")
                return null;
            return new TypeClass(source);
        };
        TypeClass.prototype.createHTML = function () {
            return $("<span>").text(this.C);
        };
        TypeClass.prototype.defaultValue = function () {
            return Expression_1.Expression.getNull();
        };
        return TypeClass;
    }(Type));
    exports.TypeClass = TypeClass;
});
