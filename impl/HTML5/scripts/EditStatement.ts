import { Editable } from "./Editable";
import { Statement } from "./Statement";
import { GUIHelpers } from "./GUIHelpers"

export class EditStatement implements Editable
{
    private html: JQuery;

    public constructor(
        private statement: Statement = null
    )
    {
        this.html = $("<p>")
            .addClass("clickable")
            .addClass("instructionStatement")
            .click(() => {
                var selectionList: JQuery[] = [];
                selectionList.push($("<p>").addClass("clickable")
                    .text("clear")
                    .click(() => {
                        this.statement = null;
                        this.updateHTML();
                    }));
                for (var stmt of Statement.factories)
                    selectionList.push($("<p>").addClass("clickable")
                        .append(stmt().createHTML())
                        .click(() => {
                            this.statement = stmt();
                            this.updateHTML();
                        }));
                var list = GUIHelpers.createList(selectionList);

                var overlayContainer = GUIHelpers.createRoundedContainer();
                overlayContainer.append(list);
                GUIHelpers.showOverlay(overlayContainer);
            });
        this.updateHTML();
    }

    private updateHTML()
    {
        this.html.text(" ");
        if (this.statement)
            this.html.append(this.statement.createHTML());
    }

    public createHTML(): JQuery
    {
        return this.html;
    }
}