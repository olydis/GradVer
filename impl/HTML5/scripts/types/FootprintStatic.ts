import { Expression } from "./Expression";

export interface FootprintStaticItem
{
    e: Expression;
    f: string;
}

export type FootprintStatic = FootprintStaticItem[];