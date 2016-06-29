var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports", "./EditableElement", "../types/Statement"], function (require, exports, EditableElement_1, Statement_1) {
    "use strict";
    var EditStatement = (function (_super) {
        __extends(EditStatement, _super);
        function EditStatement(initialSource) {
            var _this = this;
            if (initialSource === void 0) { initialSource = ""; }
            var stmtContainer = $("<span>");
            _super.call(this, stmtContainer, initialSource, function (source) {
                _this.stmt = Statement_1.Statement.parse(source) || Statement_1.Statement.getNop();
                var html = _this.stmt.createHTML();
                return {
                    source: html.text(),
                    html: html
                };
            });
            this.stmtContainer = stmtContainer;
        }
        EditStatement.prototype.createHTML = function () {
            var _this = this;
            return $("<p>")
                .addClass("clickable")
                .addClass("instructionStatement")
                .append(this.stmtContainer)
                .click(function (eo) {
                _this.editBegin();
                eo.stopPropagation();
            });
        };
        return EditStatement;
    }(EditableElement_1.EditableElement));
    exports.EditStatement = EditStatement;
});
