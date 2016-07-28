define(["require", "exports", "./TestWoVar", "./TestWoVar", "./TestWoVar", "./TestWoAcc", "./TestWoAcc", "./TestWoAcc", "./TestWoAcc"], function (require, exports, TestWoVar_1, TestWoVar_2, TestWoVar_3, TestWoAcc_1, TestWoAcc_2, TestWoAcc_3, TestWoAcc_4) {
    "use strict";
    var testProcs = [TestWoVar_2.testWoVarPreserveSat,
        TestWoVar_1.testWoVarMonotonic,
        TestWoVar_2.testWoVarPreserveSat,
        TestWoVar_3.testWoVarPreserveSfrm,
        TestWoAcc_1.testWoAccWorks,
        TestWoAcc_2.testWoAccMonotonic,
        TestWoAcc_3.testWoAccPreserveSat,
        TestWoAcc_4.testWoAccPreserveSfrm
    ];
    function test(iters, testProc) {
        if (iters === void 0) { iters = 1000; }
        testX(iters, testProcs[testProc % testProcs.length]);
    }
    exports.test = test;
    function testX(iters, testProc) {
        if (iters > 0)
            setTimeout(function () {
                console.log(testProc.name);
                testProc();
                testX(iters - 1, testProc);
            }, 10);
    }
});
