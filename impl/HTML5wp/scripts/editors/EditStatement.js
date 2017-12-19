var __extends = (this && this.__extends) || (function () {
    var extendStatics = Object.setPrototypeOf ||
        ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||
        function (d, b) { for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p]; };
    return function (d, b) {
        extendStatics(d, b);
        function __() { this.constructor = d; }
        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
    };
})();
define(["require", "exports", "./EditableElement", "../types/Statement"], function (require, exports, EditableElement_1, Statement_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    var EditStatement = /** @class */ (function (_super) {
        __extends(EditStatement, _super);
        function EditStatement(initialSource, onChange) {
            if (initialSource === void 0) { initialSource = ""; }
            var _this = this;
            var stmtContainer = $("<span>");
            _this = _super.call(this, stmtContainer, initialSource, function (source, tthis) {
                var parsed = Statement_1.Statement.parse(source);
                tthis.stmt = parsed;
                var src = tthis.stmt instanceof Statement_1.StatementComment ? source : tthis.stmt.toString();
                var html = $("<span>").text(tthis.stmt.toString());
                return {
                    source: src,
                    html: html
                };
            }, function () { return onChange(); }) || this;
            _this.stmtContainer = stmtContainer;
            return _this;
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
        EditStatement.prototype.setStatementX = function (s) {
            this.source = s;
            this.rerender();
        };
        return EditStatement;
    }(EditableElement_1.EditableElement));
    exports.EditStatement = EditStatement;
});
