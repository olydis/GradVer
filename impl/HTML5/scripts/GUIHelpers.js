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
        return GUIHelpers;
    }());
    exports.GUIHelpers = GUIHelpers;
});
