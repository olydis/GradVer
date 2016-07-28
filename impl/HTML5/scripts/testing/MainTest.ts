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

export function test(iters: number = 1000, testProc: number)
{
    testX(iters, testProcs[testProc % testProcs.length]);
}

function testX(iters: number, testProc: () => void)
{
    if (iters > 0)
        setTimeout(() => {
            console.log((<any>testProc).name);
            testProc();
            testX(iters - 1, testProc);
        }, 10);
}