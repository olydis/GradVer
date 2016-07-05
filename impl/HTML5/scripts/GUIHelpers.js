define(["require", "exports"], function (require, exports) {
    "use strict";
    var GUIHelpers = (function () {
        function GUIHelpers() {
        }
        GUIHelpers.createList = function (items) {
            var result = $("<div>").addClass("list");
            for (var _i = 0, items_1 = items; _i < items_1.length; _i++) {
                var item = items_1[_i];
                result.append(item);
            }
            return result;
        };
        GUIHelpers.createRoundedContainer = function () {
            return $("<span>").addClass("roundedContainer");
        };
        GUIHelpers.showOverlay = function (html) {
            var overlay = $("<div>").addClass("overlay");
            var hide = function () { return overlay.remove(); };
            overlay.append(html);
            overlay.click(function () { return hide(); });
            html.click(function (eo) { eo.stopPropagation(); hide(); });
            $("body").append(overlay);
        };
        GUIHelpers.flash = function (html, color, timeMS) {
            if (timeMS === void 0) { timeMS = 500; }
            html.css("box-shadow", "0px 0px 3px 2px " + color);
            html.css("background", color);
            var handle;
            var reset = function () {
                clearTimeout(handle);
                html.css("box-shadow", "none");
                html.css("background", "none");
            };
            handle = setTimeout(function () { return reset(); }, timeMS);
        };
        GUIHelpers.flashCorrect = function (html) {
            GUIHelpers.flash(html, "#8F8");
            html.children(".err").remove();
        };
        GUIHelpers.flashError = function (html, err) {
            GUIHelpers.flash(html, "#F88");
            html.children(".err").remove();
            var errHtml = $("<span>").addClass("err").text(err);
            html.append(errHtml);
            errHtml.mouseenter(function () { return errHtml.remove(); });
        };
        return GUIHelpers;
    }());
    exports.GUIHelpers = GUIHelpers;
});
