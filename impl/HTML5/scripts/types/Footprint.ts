import { Expression } from "./Expression";

export interface FootprintStaticItem
{
    e: Expression;
    f: string;
}

export type FootprintStatic = FootprintStaticItem[];

export interface FootprintDynamicItem
{
    o: number;
    f: string;
}

export type FootprintDynamic = FootprintDynamicItem[];