define(["require", "exports"], function (require, exports) {
    "use strict";
    function rand() {
        return Math.floor(Math.random() * 9007199254740991); // Number.MAX_SAFE_INTEGER;
    }
    exports.rand = rand;
});
