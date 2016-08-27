import { EvalEnv } from "./EvalEnv";
import { Value, ValueObject, ValueExpression } from "../types/ValueExpression";

var container: JQuery = null;

function ensure()
{
    if (!container)
        container = $("<div>").addClass("evalEnvVisuContainer").hide().appendTo($("body"));
}

export function showAt(pos: {x: number, y: number}, env: EvalEnv): void
{
    ensure();
    container.text("");
    // container.css("left", pos.x + "px");
    // container.css("top", pos.y + "px");
    container.css("right", "0px");
    container.css("top", "64px");
    container.append(createVisu(env));
    container.show();
}

export function hide(): void
{
    ensure();
    //container.hide();
}

function createVisu(env: EvalEnv): JQuery[]
{
    // create graph
    var graph: { src: JQuery, o: number }[] = [];
    var reachableObjects: { [o: number]: JQuery } = { };
    var nextObjects: number[] = [];
    var layers: JQuery[][] = [[]];

    var createValueView: (v: Value) => JQuery = v =>
    {
        var result = $("<span>").addClass("evalEnvVisuVal");
        if (v instanceof ValueExpression)
            result.text(v.toString());
        if (v instanceof ValueObject)
        {
            var o = v.UID;
            graph.push({ src: result, o: o });
            if (!reachableObjects[o])
            {
                reachableObjects[o] = $("<table>").addClass("evalEnvVisuObj");
                nextObjects.push(o);
            }
        }
        return result;
    };

    // stack
    for (var x in env.r)
    {
        var view = $("<table>").addClass("evalEnvVisuObj");
        view.append($("<tr>")
            .append($("<td>").text(x))
            .append($("<td>").append(createValueView(env.r[x]))));
        layers[0].push(view);
    }

    // heap
    while (nextObjects.length > 0)
    {
        layers.push(nextObjects.map(o => reachableObjects[o]));
        var no = nextObjects;
        nextObjects = [];
        for (var o of no)
        {
            var view = reachableObjects[o];
            var he = env.H[o];
            view.append($("<tr>")
                .append($("<td>").attr("colspan", 2).text(he.C)));
            for (var f in he.fs)
                view.append($("<tr>").addClass(env.A.some(a => a.o == o && a.f == f) ? "evalEnvVisuAcc1" : "evalEnvVisuAcc0")
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
    for (var layer of layers)
    {
        var layerView = $("<td>").appendTo(contentRow);
        for (var item of layer)
            layerView.append(item);
    }

    var resultCanvasNative = document.createElement("canvas");
    var resultCanvas = $(resultCanvasNative);
    setTimeout(() => {
        resultCanvas.attr("width", resultCanvas.width());
        resultCanvas.attr("height", resultCanvas.height());
        var ctx = resultCanvasNative.getContext("2d");
        
        var pos: (e: JQuery) => {x:number, y:number} = e =>
        {
            var cp = resultCanvas.offset();
            var p = e.offset();
            return { x: p.left - cp.left, y: p.top - cp.top };
        };
        var connect: (e1: JQuery, e2: JQuery) => void = (e1, e2) =>
        {
            var p1 = pos(e1);
            p1.x += e1.width() / 2;
            p1.y += e1.height() / 2;
            var p2 = pos(e2);
            p2.y += 16;

            ctx.beginPath();
            ctx.moveTo(p1.x, p1.y);
            ctx.bezierCurveTo(
                p2.x, p1.y,
                p1.x, p2.y,
                p2.x, p2.y);
            ctx.stroke();

            ctx.beginPath();
            ctx.arc(p1.x, p1.y, 3, 0, Math.PI * 2);
            ctx.fill();

            ctx.beginPath();
            ctx.arc(p2.x, p2.y, 3, Math.PI / 2, Math.PI * 3 / 2);
            ctx.fill();
        };

        for (var edge of graph)
            connect(edge.src, reachableObjects[edge.o]);
    }, 0);

    return [resultTable, resultCanvas];
}