export class EditableElement
{
    static elems: EditableElement[] = [];
    public static editEndAll(): void
    {
        EditableElement.elems = EditableElement.elems.filter(elem => $.contains(document.documentElement, elem.container.get(0)));
        EditableElement.elems.forEach(elem => elem.editEnd());
    }

    public constructor(
        private container: JQuery, 
        protected source: string,
        private render: (source: string) => { source: string, html: JQuery },
        private editMode: boolean = false
    )
    {
        EditableElement.elems.push(this);
        this.editedSource = null;

        if (editMode)
            this.editBegin();
        else
            this.rerender();
    }

    private editedSource: string;
    public editBegin(): void
    {
        if (this.editedSource != null)
            return;
        EditableElement.editEndAll();

        this.editedSource = this.source;
        
        var input = $("<input>");
        input.val(this.source);
        input.on("change keyup keydown", () => this.editedSource = input.val());
        input.keydown(eo => { if (eo.which == 13) this.editEnd(true); });
        input.keydown(eo => { if (eo.which == 27) this.editEnd(false); });

        this.container.text("").append(input);
        input.focus();
    }

    public editEnd(accept: boolean = true): void
    {
        if (accept && this.editedSource != null)
        {
            this.source = this.editedSource;
            this.editedSource = null;
            this.rerender();
        }
    }

    public rerender(): void
    {
        var rendered = this.render(this.source);
        this.source = rendered.source;
        this.container.text("").append(rendered.html);
    }
}