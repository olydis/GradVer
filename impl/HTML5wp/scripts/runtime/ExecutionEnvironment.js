define(["require", "exports"], function (require, exports) {
    "use strict";
    var ExecutionEnvironment = (function () {
        function ExecutionEnvironment(program) {
            this.program = program;
        }
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
