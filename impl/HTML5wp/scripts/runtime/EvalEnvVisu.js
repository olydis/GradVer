define(["require", "exports", "../types/ValueExpression"], function (require, exports, ValueExpression_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    var container = null;
    function ensure() {
        if (!container)
            container = $("<div>").addClass("evalEnvVisuContainer").hide().appendTo($("body"));
    }
    function showAt(pos, env, g) {
        ensure();
        container.text("");
        // container.css("left", pos.x + "px");
        // container.css("top", pos.y + "px");
        container.css("right", "0px");
        container.css("top", "64px");
        container.append(createVisu(env, g));
        container.stop().fadeIn(0);
    }
    exports.showAt = showAt;
    function hide() {
        ensure();
        container.stop().fadeOut(1000);
    }
    exports.hide = hide;
    function createVisu(env, g) {
        // create graph
        var graph = [];
        var reachableObjects = {};
        var nextObjects = [];
        var layers = [[]];
        var createValueView = function (v) {
            var result = $("<span>").addClass("evalEnvVisuVal");
            if (v instanceof ValueExpression_1.ValueExpression)
                result.text(v.toString());
            if (v instanceof ValueExpression_1.ValueObject) {
                var o = v.UID;
                graph.push({ src: result, o: o });
                if (!reachableObjects[o]) {
                    reachableObjects[o] = $("<table>").addClass("evalEnvVisuObj");
                    nextObjects.push(o);
                }
            }
            return result;
        };
        // stack
        for (var x in env.r) {
            var view = $("<table>").addClass("evalEnvVisuObj");
            var hasType = g(x) != null;
            if (hasType)
                view.append($("<tr>")
                    .append($("<td>").attr("colspan", 2).text(g(x).toString())));
            view.append($("<tr>").addClass(hasType ? "evalEnvVisuAcc1" : "evalEnvVisuAcc0")
                .append($("<td>").text(x))
                .append($("<td>").append(createValueView(env.r[x]))));
            layers[0].push(view);
        }
        // heap
        while (nextObjects.length > 0) {
            layers.push(nextObjects.map(function (o) { return reachableObjects[o]; }));
            var no = nextObjects;
            nextObjects = [];
            for (var _i = 0, no_1 = no; _i < no_1.length; _i++) {
                var o = no_1[_i];
                var view = reachableObjects[o];
                var he = env.H[o];
                view.append($("<tr>")
                    .append($("<td>").attr("colspan", 2).text(he.C)));
                for (var f in he.fs)
                    view.append($("<tr>").addClass(env.A.some(function (a) { return a.o == o && a.f == f; }) ? "evalEnvVisuAcc1" : "evalEnvVisuAcc0")
                        .append($("<td>").text(f))
                        .append($("<td>").append(createValueView(he.fs[f]))));
            }
        }
        // build view
        var stackContainer = $("<td>");
        var heapContainer = $("<td>");
        var resultTable = $("<table>");
        resultTable.append($("<tr>")
            .append($("<td>").text("Stack"))
            .append($("<td>").attr("colspan", 0).text("Heap")));
        var contentRow = $("<tr>").appendTo(resultTable);
        for (var _a = 0, layers_1 = layers; _a < layers_1.length; _a++) {
            var layer = layers_1[_a];
            var layerView = $("<td>").appendTo(contentRow);
            for (var _b = 0, layer_1 = layer; _b < layer_1.length; _b++) {
                var item = layer_1[_b];
                layerView.append(item);
            }
        }
        var resultCanvasNative = document.createElement("canvas");
        var resultCanvas = $(resultCanvasNative);
        setTimeout(function () {
            resultCanvas.attr("width", resultCanvas.width());
            resultCanvas.attr("height", resultCanvas.height());
            var ctx = resultCanvasNative.getContext("2d");
            var pos = function (e) {
                var cp = resultCanvas.offset();
                var p = e.offset();
                return { x: p.left - cp.left, y: p.top - cp.top };
            };
            var connect = function (e1, e2) {
                var p1 = pos(e1);
                p1.x += e1.width() / 2;
                p1.y += e1.height() / 2;
                var p2 = pos(e2);
                p2.y += 16;
                ctx.beginPath();
                ctx.moveTo(p1.x, p1.y);
                ctx.bezierCurveTo(p2.x, p1.y, p1.x, p2.y, p2.x, p2.y);
                ctx.stroke();
                ctx.beginPath();
                ctx.arc(p1.x, p1.y, 3, 0, Math.PI * 2);
                ctx.fill();
                ctx.beginPath();
                ctx.arc(p2.x, p2.y, 3, Math.PI / 2, Math.PI * 3 / 2);
                ctx.fill();
            };
            for (var _i = 0, graph_1 = graph; _i < graph_1.length; _i++) {
                var edge = graph_1[_i];
                connect(edge.src, reachableObjects[edge.o]);
            }
        }, 0);
        return [resultTable, resultCanvas];
    }
});
