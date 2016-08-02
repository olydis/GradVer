import { Type } from "../types/Type";

export type Gamma = (x: string) => Type;

export var GammaNew : Gamma = x => undefined;
export function GammaAdd(x: string, T: Type, g: Gamma): Gamma
{
    return y => x == y
        ? T
        : g(y);
}