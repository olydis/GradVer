var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports", "./Expression"], function (require, exports, Expression_1) {
    "use strict";
    var FormulaPart = (function () {
        function FormulaPart() {
        }
        FormulaPart.parse = function (source) {
            source = source.replace(/\s/g, "");
            source = source.replace(/\(/g, "");
            source = source.replace(/\)/g, "");
            var result = null;
            if (!result)
                result = FormulaPartType.parse(source);
            if (!result)
                result = FormulaPartAcc.parse(source);
            if (!result)
                result = FormulaPartTrue.parse(source);
            if (!result)
                result = FormulaPartNeq.parse(source);
            if (!result)
                result = FormulaPartEq.parse(source);
            return result;
        };
        return FormulaPart;
    }());
    var FormulaPartTrue = (function (_super) {
        __extends(FormulaPartTrue, _super);
        function FormulaPartTrue() {
            _super.apply(this, arguments);
        }
        FormulaPartTrue.parse = function (source) {
            return source.toLowerCase() == "true"
                ? new FormulaPartTrue()
                : null;
        };
        FormulaPartTrue.prototype.createHTML = function () {
            return $("<span>").text("true");
        };
        return FormulaPartTrue;
    }(FormulaPart));
    var FormulaPartEq = (function (_super) {
        __extends(FormulaPartEq, _super);
        function FormulaPartEq(e1, e2) {
            _super.call(this);
            this.e1 = e1;
            this.e2 = e2;
            if (e1 == null)
                throw "null arg";
            if (e2 == null)
                throw "null arg";
        }
        FormulaPartEq.parse = function (source) {
            var eqIndex = source.indexOf("=");
            if (eqIndex == -1)
                return null;
            var a = source.substr(0, eqIndex);
            var b = source.substr(eqIndex + 1).replace(/=/g, "");
            var ea = Expression_1.Expression.parse(a);
            var eb = Expression_1.Expression.parse(b);
            return ea != null && eb != null
                ? new FormulaPartEq(ea, eb)
                : null;
        };
        FormulaPartEq.prototype.createHTML = function () {
            return $("<span>")
                .append($("<span>").text("("))
                .append(this.e1.createHTML())
                .append($("<span>").text(" = "))
                .append(this.e2.createHTML())
                .append($("<span>").text(")"));
        };
        return FormulaPartEq;
    }(FormulaPart));
    var FormulaPartNeq = (function (_super) {
        __extends(FormulaPartNeq, _super);
        function FormulaPartNeq(e1, e2) {
            _super.call(this);
            this.e1 = e1;
            this.e2 = e2;
            if (e1 == null)
                throw "null arg";
            if (e2 == null)
                throw "null arg";
        }
        FormulaPartNeq.parse = function (source) {
            var eqIndex = source.indexOf("!=");
            if (eqIndex == -1)
                eqIndex = source.indexOf("<>");
            if (eqIndex == -1)
                eqIndex = source.indexOf("≠");
            if (eqIndex == -1)
                return null;
            var a = source.substr(0, eqIndex);
            var b = source.substr(eqIndex + 1).replace(/=/g, "").replace(/>/g, "");
            var ea = Expression_1.Expression.parse(a);
            var eb = Expression_1.Expression.parse(b);
            return ea != null && eb != null
                ? new FormulaPartNeq(ea, eb)
                : null;
        };
        FormulaPartNeq.prototype.createHTML = function () {
            return $("<span>")
                .append($("<span>").text("("))
                .append(this.e1.createHTML())
                .append($("<span>").text(" ≠ "))
                .append(this.e2.createHTML())
                .append($("<span>").text(")"));
        };
        return FormulaPartNeq;
    }(FormulaPart));
    var FormulaPartAcc = (function (_super) {
        __extends(FormulaPartAcc, _super);
        function FormulaPartAcc(e, f) {
            _super.call(this);
            this.e = e;
            this.f = f;
            if (e == null)
                throw "null arg";
            if (!Expression_1.Expression.isValidX(f))
                throw "null arg";
        }
        FormulaPartAcc.parse = function (source) {
            if (source.substr(0, 3) != "acc")
                return null;
            source = source.substr(3);
            var dotIndex = source.lastIndexOf(".");
            if (dotIndex == -1)
                dotIndex = source.lastIndexOf(",");
            if (dotIndex == -1)
                return null;
            var e = Expression_1.Expression.parse(source.substr(0, dotIndex));
            var f = source.substr(dotIndex + 1);
            return e != null
                ? new FormulaPartAcc(e, f)
                : null;
        };
        FormulaPartAcc.prototype.createHTML = function () {
            return $("<span>")
                .append($("<span>").text("acc("))
                .append(this.e.createHTML())
                .append($("<span>").text("." + this.f))
                .append($("<span>").text(")"));
        };
        return FormulaPartAcc;
    }(FormulaPart));
    var FormulaPartType = (function (_super) {
        __extends(FormulaPartType, _super);
        function FormulaPartType(x, T) {
            _super.call(this);
            this.x = x;
            this.T = T;
            if (!Expression_1.Expression.isValidX(x))
                throw "null arg";
            if (!Expression_1.Expression.isValidX(T))
                throw "null arg";
        }
        FormulaPartType.parse = function (source) {
            var dotIndex = source.lastIndexOf(":");
            if (dotIndex == -1)
                return null;
            var x = source.substr(0, dotIndex);
            var T = source.substr(dotIndex + 1);
            return new FormulaPartType(x, T);
        };
        FormulaPartType.prototype.createHTML = function () {
            return $("<span>")
                .append($("<span>").text("("))
                .append($("<span>").text(this.x))
                .append($("<span>").text(" : "))
                .append($("<span>").text(this.T))
                .append($("<span>").text(")"));
        };
        return FormulaPartType;
    }(FormulaPart));
    var VerificationFormula = (function () {
        function VerificationFormula(source) {
            if (source === void 0) { source = ""; }
            this.html = $("<span>");
            this.parts = [];
            source = source.trim();
            if (source != "")
                this.parts = source.split("*").map(FormulaPart.parse).filter(function (part) { return part != null; });
            this.updateHTML();
        }
        VerificationFormula.prototype.isEmpty = function () {
            return this.parts.length == 0;
        };
        VerificationFormula.prototype.updateHTML = function () {
            var parts = this.isEmpty() ? [new FormulaPartTrue()] : this.parts;
            this.html.text("");
            for (var i = 0; i < parts.length; ++i) {
                if (i > 0)
                    this.html.append($("<span>").addClass("sepConj").text(" * "));
                this.html.append(parts[i].createHTML());
            }
        };
        VerificationFormula.prototype.createHTML = function () {
            return this.html;
        };
        return VerificationFormula;
    }());
    exports.VerificationFormula = VerificationFormula;
});
