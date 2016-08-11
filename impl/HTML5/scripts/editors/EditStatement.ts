import { EditableElement } from "./EditableElement";
import { Statement } from "../types/Statement";
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
                this.stmt = Statement.parse(source) || Statement.getNop();
                var src = this.stmt.toString();
                var html = $("<span>").text(src);
                onChange();
                return {
                    source: src,
                    html: html
                };
            }
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
    public setStatement(stmt: Statement): void
    {
        this.stmt = stmt;
        this.source = stmt.toString();
        this.rerender();
    }
    public setStatementX(s: string): void
    {
        this.setStatement(Statement.parse(s));
    }
}