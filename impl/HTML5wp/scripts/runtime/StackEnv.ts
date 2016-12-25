import { Heap, Rho, EvalEnv, cloneHeap, cloneRho, cloneAccess } from "./EvalEnv";
import { FootprintDynamic } from "../types/Footprint";
import { Statement } from "../types/Statement";

export type StackEntry = { r: Rho, A: FootprintDynamic, ss: Statement[] };
export type StackEnv = { H: Heap, S: StackEntry[] };

function cloneStackEntry(se: StackEntry): StackEntry
{
    return {
        r: cloneRho(se.r),
        A: cloneAccess(se.A),
        ss: se.ss.slice()
    };
}
export function cloneStackEnv(env: StackEnv): StackEnv
{
    return {
        H: cloneHeap(env.H),
        S: env.S.map(cloneStackEntry)
    };
}
export function topEnv(env: StackEnv): EvalEnv
{
    var top = env.S[env.S.length - 1];

    return {
        H: env.H,
        r: top.r,
        A: top.A
    };
}