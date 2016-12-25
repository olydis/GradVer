define(["require", "exports"], function (require, exports) {
    "use strict";
    exports.GammaNew = function (x) { return undefined; };
    function GammaAdd(x, T, g) {
        return function (y) { return x == y
            ? T
            : g(y); };
    }
    exports.GammaAdd = GammaAdd;
});
