define(["require", "exports", "./Statement", "./GUIHelpers"], function (require, exports, Statement_1, GUIHelpers_1) {
    "use strict";
    var EditStatement = (function () {
        function EditStatement(statement) {
            var _this = this;
            if (statement === void 0) { statement = null; }
            this.statement = statement;
            this.html = $("<p>")
                .addClass("clickable")
                .addClass("instructionStatement")
                .click(function () {
                var selectionList = [];
                selectionList.push($("<p>").addClass("clickable")
                    .text("clear")
                    .click(function () {
                    _this.statement = null;
                    _this.updateHTML();
                }));
                for (var _i = 0, _a = Statement_1.Statement.factories; _i < _a.length; _i++) {
                    var stmt = _a[_i];
                    selectionList.push($("<p>").addClass("clickable")
                        .append(stmt().createHTML())
                        .click(function () {
                        _this.statement = stmt();
                        _this.updateHTML();
                    }));
                }
                var list = GUIHelpers_1.GUIHelpers.createList(selectionList);
                var overlayContainer = GUIHelpers_1.GUIHelpers.createRoundedContainer();
                overlayContainer.append(list);
                GUIHelpers_1.GUIHelpers.showOverlay(overlayContainer);
            });
            this.updateHTML();
        }
        EditStatement.prototype.updateHTML = function () {
            this.html.text(" ");
            if (this.statement)
                this.html.append(this.statement.createHTML());
        };
        EditStatement.prototype.createHTML = function () {
            return this.html;
        };
        return EditStatement;
    }());
    exports.EditStatement = EditStatement;
});
