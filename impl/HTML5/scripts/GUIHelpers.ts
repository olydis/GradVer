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
}