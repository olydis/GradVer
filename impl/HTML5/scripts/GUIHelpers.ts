export class GUIHelpers
{
    public static createList(items: JQuery[]): JQuery
    {
        var result = $("<div>").addClass("list");
        for (var item of items)
            result.append(item);
        return result;
    }

    public static createRoundedContainer(): JQuery
    {
        return $("<span>").addClass("roundedContainer");
    }

    public static showOverlay(html: JQuery): void
    {
        var overlay = $("<div>").addClass("overlay");
        var hide = () => overlay.remove();
        overlay.append(html);
        overlay.click(() => hide());
        html.click(eo => { eo.stopPropagation(); hide(); });

        $("body").append(overlay);
    }

    private static flash(html: JQuery, color: string, timeMS: number = 500): void
    {
        html.css("box-shadow", "0px 0px 3px 2px " + color);
        html.css("background", color);

        var handle: number;
        var reset = () => {
            clearTimeout(handle);
            html.css("box-shadow", "none");
            html.css("background", "none");
        };
        handle = setTimeout(() => reset(), timeMS);
    }

    public static flashCorrect(html: JQuery, msg: string = ""): void
    {
        GUIHelpers.flash(html, "#8F8");

        html.children(".err").remove();
        html.children(".succ").remove();
        var succHtml = $("<span>").addClass("succ").text(msg);
        html.append(succHtml);
        succHtml.mouseenter(() => succHtml.remove());
    }

    public static flashError(html: JQuery, err: string): void
    {
        GUIHelpers.flash(html, "#F88");

        html.children(".err").remove();
        html.children(".succ").remove();
        var errHtml = $("<span>").addClass("err").text(err);
        html.append(errHtml);
        errHtml.mouseenter(() => errHtml.remove());
    }
}