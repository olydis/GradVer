var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
define(["require", "exports"], function (require, exports) {
    "use strict";
    var Statement = (function () {
        function Statement() {
        }
        Object.defineProperty(Statement, "factories", {
            get: function () {
                var result = [];
                result.push(function () { return new StatementMemberSet(); });
                return result;
            },
            enumerable: true,
            configurable: true
        });
        return Statement;
    }());
    exports.Statement = Statement;
    var StatementMemberSet = (function (_super) {
        __extends(StatementMemberSet, _super);
        function StatementMemberSet() {
            _super.apply(this, arguments);
        }
        StatementMemberSet.prototype.createHTML = function () {
            return $("<span>").text("stmt");
        };
        return StatementMemberSet;
    }(Statement));
    exports.StatementMemberSet = StatementMemberSet;
});
