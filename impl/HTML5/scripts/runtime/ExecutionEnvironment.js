define(["require", "exports", "../types/Type", "./../types/Expression"], function (require, exports, Type_1, Expression_1) {
    "use strict";
    var ExecutionEnvironment = (function () {
        function ExecutionEnvironment(program) {
            this.program = program;
        }
        ExecutionEnvironment.prototype.tryGetType = function (p, e) {
            if (e instanceof Expression_1.ExpressionV)
                return e.v.getType();
            if (e instanceof Expression_1.ExpressionX)
                return p.tryGetType(e.x);
            if (e instanceof Expression_1.ExpressionDot) {
                var inner = this.tryGetType(p, e.e);
                if (inner instanceof Type_1.TypeClass)
                    return this.fieldType(inner.C, e.f);
                return null;
            }
            return null;
        };
        ExecutionEnvironment.prototype.tryGetCoreType = function (p, e) {
            if (e instanceof Expression_1.ExpressionV)
                return e.v.getType();
            if (e instanceof Expression_1.ExpressionX)
                return p.tryGetType(e.x);
            if (e instanceof Expression_1.ExpressionDot)
                return this.tryGetCoreType(p, e.e);
            return null;
        };
        ExecutionEnvironment.prototype.getMain = function () {
            return this.program.main;
        };
        ExecutionEnvironment.prototype.getClasses = function () {
            return this.program.classes;
        };
        ExecutionEnvironment.prototype.getClass = function (C) {
            var res = this.getClasses().filter(function (c) { return c.name == C; });
            return res.length == 0 ? null : res[0];
        };
        ExecutionEnvironment.prototype.fields = function (C) {
            var cls = this.getClass(C);
            return cls == null
                ? null
                : cls.fields;
        };
        ExecutionEnvironment.prototype.fieldType = function (C, f) {
            var res = this.fields(C);
            if (res == null)
                return null;
            res = res.filter(function (c) { return c.name == f; });
            return res.length == 0 ? null : res[0].type;
        };
        ExecutionEnvironment.prototype.mmethod = function (C, m) {
            var res = this.getClass(C);
            if (res == null)
                return null;
            var mm = res.methods.filter(function (c) { return c.name == m; });
            return mm.length == 0 ? null : mm[0];
        };
        return ExecutionEnvironment;
    }());
    exports.ExecutionEnvironment = ExecutionEnvironment;
});
