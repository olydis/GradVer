var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports", "./VerificationFormula", "./Type", "./Expression"], function (require, exports, VerificationFormula_1, Type_1, Expression_1) {
    "use strict";
    var Statement = (function () {
        function Statement() {
        }
        Statement.parse = function (source) {
            var result = null;
            source = source.replace(/;$/, "");
            var sourceWS = source;
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
                result = StatementMemberSet.parse(source);
            if (!result)
                result = StatementAssign.parse(source);
            if (!result)
                result = StatementDeclare.parse(sourceWS);
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
        StatementMemberSet.prototype.createHTML = function () {
            return $("<span>")
                .append(this.x + "." + this.f)
                .append($("<span>").text(" := "))
                .append(this.y)
                .append($("<span>").text(";"));
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
        StatementAssign.prototype.createHTML = function () {
            return $("<span>")
                .append(this.x)
                .append($("<span>").text(" := "))
                .append(this.e.createHTML())
                .append($("<span>").text(";"));
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
        StatementAlloc.prototype.createHTML = function () {
            return $("<span>")
                .append(this.x)
                .append($("<span>").text(" := new "))
                .append(this.C)
                .append($("<span>").text(";"));
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
        StatementCall.prototype.createHTML = function () {
            return $("<span>")
                .append(this.x)
                .append($("<span>").text(" := "))
                .append(this.y + "." + this.m + "(" + this.z + ")")
                .append($("<span>").text(";"));
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
        StatementReturn.prototype.createHTML = function () {
            return $("<span>")
                .append($("<span>").text("return "))
                .append(this.x)
                .append($("<span>").text(";"));
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
        StatementAssert.prototype.createHTML = function () {
            return $("<span>")
                .append($("<span>").text("assert "))
                .append(this.assertion.createHTML())
                .append($("<span>").text(";"));
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
        StatementRelease.prototype.createHTML = function () {
            return $("<span>")
                .append($("<span>").text("release "))
                .append(this.assertion.createHTML())
                .append($("<span>").text(";"));
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
        StatementDeclare.prototype.createHTML = function () {
            return $("<span>")
                .append(this.T.createHTML())
                .append($("<span>").text(" "))
                .append(this.x)
                .append($("<span>").text(";"));
        };
        return StatementDeclare;
    }(Statement));
    exports.StatementDeclare = StatementDeclare;
});
