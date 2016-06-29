import { Editable } from "./Editable";

export abstract class Statement implements Editable
{
    abstract createHTML(): JQuery;

    public static get factories(): (() => Statement)[]
    {
        var result: (() => Statement)[] = [];
        result.push(() => new StatementMemberSet());
        return result;
    }
}

export class StatementMemberSet extends Statement
{
    public createHTML(): JQuery
    {
        return $("<span>").text("stmt");
    }
}