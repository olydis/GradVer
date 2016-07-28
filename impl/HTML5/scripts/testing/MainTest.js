define(["require", "exports", "./TestImplies"], function (require, exports, TestImplies_1) {
    "use strict";
    function test() {
        for (var i = 0; i < 1000; ++i)
            TestImplies_1.testImpliesTransitivity();
    }
    exports.test = test;
});
