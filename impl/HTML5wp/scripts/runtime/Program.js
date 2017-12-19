define(["require", "exports"], function (require, exports) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    function indent(amount) {
        var prefix = "";
        for (var i = 0; i < amount; ++i)
            prefix += " ";
        return function (s) {
            var lines = s.split("\n");
            lines = lines.map(function (l) { return prefix + l; });
            return lines.join("\n");
        };
    }
    function printField(f) {
        return f.type + " " + f.name + ";";
    }
    function printMethod(m) {
        var res = m.retType + " " + m.name + "(" + m.args.map(function (a) { return a.type + " " + a.name; }).join(", ") + ")";
        res += "\n    requires " + m.frmPre + ";";
        res += "\n    ensures  " + m.frmPost + ";";
        res += "\n{\n";
        res += m.body.map(function (x) { return x.toString(); }).map(indent(4)).join("\n");
        res += "\n}\n";
        return res;
    }
    function printClass(c) {
        var res = "class " + c.name;
        res += "\n{\n";
        res += c.fields.map(printField).map(indent(4)).join("\n");
        if (c.fields.length > 0 && c.methods.length > 0)
            res += "\n\n";
        res += c.methods.map(printMethod).map(indent(4)).join("\n");
        res += "\n}\n";
        return res;
    }
    function printProgram(p) {
        return p.classes.map(printClass).join("\n");
    }
    exports.printProgram = printProgram;
});
