define(["require", "exports", "./TestWoAcc", "./TestWoAcc", "./TestWoAcc"], function (require, exports, TestWoAcc_1, TestWoAcc_2, TestWoAcc_3) {
    "use strict";
    var testProcs = [null,
        TestWoAcc_1.testWoAccWorks,
        TestWoAcc_2.testWoAccPreserveSat,
        TestWoAcc_3.testWoAccPreserveSfrm
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
        if (testProc == null)
            return;
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
