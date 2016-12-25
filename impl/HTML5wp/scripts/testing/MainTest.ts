import { testImpliesTransitivity } from "./TestImplies";
import { testWoVarMonotonic } from "./TestWoVar";
import { testWoVarPreserveSat } from "./TestWoVar";
import { testWoVarPreserveSfrm } from "./TestWoVar";
import { testWoAccWorks } from "./TestWoAcc";
import { testWoAccMonotonic } from "./TestWoAcc";
import { testWoAccPreserveSat } from "./TestWoAcc";
import { testWoAccPreserveSfrm } from "./TestWoAcc";
import { testSupImplies } from "./TestSup";
import { testSupComm } from "./TestSup";
import { testSupAssoc } from "./TestSup";

var testProcs: (() => void)[] = 
    [ null

    // , testWoVarPreserveSat
    // , testWoVarMonotonic
    // , testWoVarPreserveSat
    // , testWoVarPreserveSfrm

     , testWoAccWorks
    // , testWoAccMonotonic
     , testWoAccPreserveSat
     , testWoAccPreserveSfrm

    // , testSupImplies
    // , testSupComm
    // , testSupAssoc
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
    if (testProc == null)
        return;
    if (iters > 0)
        setTimeout(() => {
            document.title = iters + " - " + (<any>testProc).name;
            if (iters % 100 == 0)
                console.log((<any>testProc).name, iters);
            testProc();
            testX(iters - 1, testProc);
        }, 10);
}