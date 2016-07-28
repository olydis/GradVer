import { testImpliesTransitivity } from "./TestImplies";

export function test()
{
    for (var i = 0; i < 1000; ++i)
        testImpliesTransitivity();
}