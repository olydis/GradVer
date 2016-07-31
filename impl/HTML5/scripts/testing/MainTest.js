define(["require", "exports", "./TestSup", "./TestSup", "./TestSup"], function (require, exports, TestSup_1, TestSup_2, TestSup_3) {
    "use strict";
    var testProcs = [null,
        TestSup_1.testSupImplies,
        TestSup_2.testSupComm,
        TestSup_3.testSupAssoc
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
