import { EditableElement } from "./EditableElement";
import { Statement, StatementComment } from "../types/Statement";
import { GUIHelpers } from "./GUIHelpers"

export class EditStatement extends EditableElement
{
    public stmtContainer: JQuery;
    private stmt: Statement;

    public constructor(
        initialSource: string = "",
        onChange: () => void
    ) 
    {
        var stmtContainer = $("<span>");

        super(
            stmtContainer,
            initialSource,
            (source: string) => {
                var parsed = Statement.parse(source);
                this.stmt = parsed;
                var src = this.stmt instanceof StatementComment ? source : this.stmt.toString();
                var html = $("<span>").text(this.stmt.toString());
                return {
                    source: src,
                    html: html
                };
            },
            () => onChange()
        );

        this.stmtContainer = stmtContainer;
    }

    public createHTML(): JQuery
    {
        return $("<p>")
            .addClass("clickable")
            .addClass("instructionStatement")
            .append(this.stmtContainer)
            .click(eo => { 
                this.editBegin();
                eo.stopPropagation();
            });
    }

    public getStatement(): Statement { return this.stmt; }
    public setStatementX(s: string): void
    {
        this.source = s;
        this.rerender();
    }
}