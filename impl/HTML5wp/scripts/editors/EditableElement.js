define(["require", "exports"], function (require, exports) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    var EditableElement = /** @class */ (function () {
        function EditableElement(container, source, render, onChange, editMode) {
            if (editMode === void 0) { editMode = false; }
            this.container = container;
            this.source = source;
            this.render = render;
            this.onChange = onChange;
            this.editMode = editMode;
            EditableElement.elems.push(this);
            this.editedSource = null;
            if (editMode)
                this.editBegin();
            else
                this.rerender();
        }
        EditableElement.editEndAll = function () {
            EditableElement.elems = EditableElement.elems.filter(function (elem) { return $.contains(document.documentElement, elem.container.get(0)); });
            EditableElement.elems.forEach(function (elem) { return elem.editEnd(); });
        };
        EditableElement.prototype.editBegin = function () {
            var _this = this;
            if (this.editedSource != null)
                return;
            EditableElement.editEndAll();
            this.editedSource = this.source;
            var input = $("<input>");
            input.val(this.source);
            input.on("change keyup keydown", function () { return _this.editedSource = input.val(); });
            input.keydown(function (eo) { if (eo.which == 13)
                _this.editEnd(true); });
            input.keydown(function (eo) { if (eo.which == 27)
                _this.editEnd(false); });
            this.container.text("").append(input);
            input.focus();
        };
        EditableElement.prototype.editEnd = function (accept) {
            if (accept === void 0) { accept = true; }
            if (this.editedSource != null) {
                if (accept)
                    this.source = this.editedSource;
                this.editedSource = null;
                this.rerender();
            }
        };
        EditableElement.prototype.rerender = function () {
            var rendered = this.render(this.source, this);
            this.source = rendered.source;
            this.container.text("").append(rendered.html);
            this.onChange(this);
        };
        EditableElement.elems = [];
        return EditableElement;
    }());
    exports.EditableElement = EditableElement;
});
