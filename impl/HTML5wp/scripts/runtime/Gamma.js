define(["require", "exports"], function (require, exports) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    exports.GammaNew = function (x) { return undefined; };
    function GammaAdd(x, T, g) {
        return function (y) { return x == y
            ? T
            : g(y); };
    }
    exports.GammaAdd = GammaAdd;
});
