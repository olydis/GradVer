var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports", "./EditableElement", "../types/Statement"], function (require, exports, EditableElement_1, Statement_1) {
    "use strict";
    var EditStatement = (function (_super) {
        __extends(EditStatement, _super);
        function EditStatement(initialSource, onChange) {
            var _this = this;
            if (initialSource === void 0) { initialSource = ""; }
            var stmtContainer = $("<span>");
            _super.call(this, stmtContainer, initialSource, function (source) {
                var parsed = Statement_1.Statement.parse(source);
                _this.stmt = parsed;
                var src = _this.stmt instanceof Statement_1.StatementComment ? source : _this.stmt.toString();
                var html = $("<span>").text(_this.stmt.toString());
                return {
                    source: src,
                    html: html
                };
            }, function () { return onChange(); });
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
        EditStatement.prototype.getStatement = function () { return this.stmt; };
        EditStatement.prototype.setStatement = function (stmt) {
            this.stmt = stmt;
            this.source = stmt.toString();
            this.rerender();
        };
        EditStatement.prototype.setStatementX = function (s) {
            this.setStatement(Statement_1.Statement.parse(s));
        };
        return EditStatement;
    }(EditableElement_1.EditableElement));
    exports.EditStatement = EditStatement;
});
