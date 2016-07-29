import { testImpliesTransitivity } from "./TestImplies";
import { testWoVarMonotonic } from "./TestWoVar";
import { testWoVarPreserveSat } from "./TestWoVar";
import { testWoVarPreserveSfrm } from "./TestWoVar";
import { testWoAccWorks } from "./TestWoAcc";
import { testWoAccMonotonic } from "./TestWoAcc";
import { testWoAccPreserveSat } from "./TestWoAcc";
import { testWoAccPreserveSfrm } from "./TestWoAcc";

var testProcs: (() => void)[] = 
    [ testWoVarPreserveSat

    , testWoVarMonotonic
    , testWoVarPreserveSat
    , testWoVarPreserveSfrm

    , testWoAccWorks
    , testWoAccMonotonic
    , testWoAccPreserveSat
    , testWoAccPreserveSfrm
    ];

export function testAll(iters: number = 10000)
{
    for (var i = 0; i < testProcs.length; ++i)
        test(iters, i);
}

export function test(iters: number, testProc: number)
{
    testX(iters, testProcs[testProc % testProcs.length]);
}

function testX(iters: number, testProc: () => void)
{
    if (iters > 0)
        setTimeout(() => {
            document.title = iters + " - " + (<any>testProc).name;
            if (iters % 100 == 0)
                console.log((<any>testProc).name, iters);
            testProc();
            testX(iters - 1, testProc);
        }, 10);
}