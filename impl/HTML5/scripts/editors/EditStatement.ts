import { EditableElement } from "./EditableElement";
import { Statement } from "../types/Statement";
import { GUIHelpers } from "./GUIHelpers"

export class EditStatement extends EditableElement
{
    private stmtContainer: JQuery;
    private stmt: Statement;

    public constructor(
        initialSource: string = ""
    ) 
    {
        var stmtContainer = $("<span>");

        super(
            stmtContainer,
            initialSource,
            (source: string) => {
                this.stmt = Statement.parse(source) || Statement.getNop();
                var html = this.stmt.createHTML();
                return {
                    source: html.text(),
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
}