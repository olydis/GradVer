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
    function testAll(iters) {
        if (iters === void 0) { iters = 10000; }
        for (var i = 0; i < testProcs.length; ++i)
            test(iters, i);
    }
    exports.testAll = testAll;
    function test(iters, testProc) {
        testX(iters, testProcs[testProc % testProcs.length]);
    }
    exports.test = test;
    function testX(iters, testProc) {
        if (iters > 0)
            setTimeout(function () {
                document.title = iters + " - " + testProc.name;
                if (iters % 100 == 0)
                    console.log(testProc.name, iters);
                testProc();
                testX(iters - 1, testProc);
            }, 10);
    }
});
