import { EditInstructions } from "./editors/EditInstructions";
import { EditVerificationFormula } from "./editors/EditVerificationFormula";
import { EditableElement } from "./editors/EditableElement";
import { ExecutionEnvironment } from "./runtime/ExecutionEnvironment";
import { Expression, ExpressionDot } from "./types/Expression";
import { Hoare } from "./runtime/Hoare";
import { Program, printProgram } from "./runtime/Program";
import { testAll } from "./testing/MainTest";
import { VerificationFormulaGradual } from "./types/VerificationFormulaGradual";
import { Type, TypeClass } from "./types/Type";
import { Statement } from "./types/Statement";
import { VerificationFormula, FormulaPart, FormulaPartEq, FormulaPartNeq } from "./types/VerificationFormula";

$(() =>
{
    $(window).click(() => EditableElement.editEndAll());

    var program: Program = {
        classes: [
        {
            name: "void",
            fields: [],
            methods: []
        },
        {
            name: "Point",
            fields: [
                {
                    name: "x",
                    type: Type.getPrimitiveInt()
                },
                {
                    name: "y",
                    type: Type.getPrimitiveInt()
                }
            ],
            methods: [
                // {
                //     name: "exchange",
                //     retType: new TypeClass("Point"),
                //     argType: new TypeClass("Point"),
                //     argName: "p",
                //     frmPre: new VerificationFormulaGradual("acc(this.x) * acc(this.y) * acc(p.x) * acc(p.y)"),
                //     frmPost: new VerificationFormulaGradual("acc(this.x) * acc(this.y) * acc(p.x) * acc(p.y) * acc(result.x) * acc(result.y) * this.x = p.x * this.y = p.y"),
                //     body: [
                //         Statement.parse("int t;"),
                //         Statement.parse("Point res;"),
                //         Statement.parse("res = new Point;"),
                //         Statement.parse("t = this.x;"),
                //         Statement.parse("res.x = t;"),
                //         Statement.parse("t = this.y;"),
                //         Statement.parse("res.y = t;"),
                //         Statement.parse("t = p.x;"),
                //         Statement.parse("this.x = t;"),
                //         Statement.parse("t = p.y;"),
                //         Statement.parse("this.y = t;"),
                //         Statement.parse("return res;"),

                //         // Statement.parse("Point res;"),
                //         // Statement.parse("res = new Point;"),
                //         // Statement.parse("res.x = this.x;"),
                //         // Statement.parse("res.y = this.y;"),
                //         // Statement.parse("this.x = p.x;"),
                //         // Statement.parse("this.y = p.y;"),
                //         // Statement.parse("return res;"),
                //     ]
                // },
                {
                    name: "swapXYweak",
                    retType: new TypeClass("Point"),
                    argType: new TypeClass("void"),
                    argName: "_",
                    frmPre: new VerificationFormulaGradual("acc(this.x) * acc(this.y)"),
                    frmPost: new VerificationFormulaGradual("acc(this.x) * acc(this.y) * acc(result.x) * acc(result.y) * this.x = result.y * this.y = result.x"),
                    body: [
                        Statement.parse("int t;"),
                        Statement.parse("Point res;"),
                        Statement.parse("res = new Point;"),
                        Statement.parse("t = this.y;"),
                        Statement.parse("res.x = t;"),
                        Statement.parse("t = this.x;"),
                        Statement.parse("res.y = t;"),
                        Statement.parse("return res;"),

                        // Statement.parse("Point res;"),
                        // Statement.parse("res = new Point;"),
                        // Statement.parse("res.x = this.y;"),
                        // Statement.parse("res.y = this.x;"),
                        // Statement.parse("return res;"),
                    ]
                },
                {
                    name: "swapXYstrong",
                    retType: new TypeClass("Point"),
                    argType: new TypeClass("void"),
                    argName: "_",
                    frmPre: new VerificationFormulaGradual("acc(this.x) * acc(this.y)"),
                    frmPost: new VerificationFormulaGradual("? * acc(this.x) * acc(this.y) * acc(result.x) * acc(result.y) * this.x = result.y * this.y = result.x"),
                    body: [
                        Statement.parse("int t;"),
                        Statement.parse("Point res;"),
                        Statement.parse("res = new Point;"),
                        Statement.parse("t = this.y;"),
                        Statement.parse("res.x = t;"),
                        Statement.parse("t = this.x;"),
                        Statement.parse("res.y = t;"),
                        Statement.parse("return res;"),

                        // Statement.parse("Point res;"),
                        // Statement.parse("res = new Point;"),
                        // Statement.parse("res.x = this.y;"),
                        // Statement.parse("res.y = this.x;"),
                        // Statement.parse("return res;"),
                    ]
                }
            ]
        },
        {
            name: "Points",
            fields: [
                {
                    name: "h",
                    type: new TypeClass("Point")
                },
                {
                    name: "t",
                    type: new TypeClass("Points")
                }
            ],
            methods: []
        }],
        main: []
    };
    var env = new ExecutionEnvironment(program);
    var hoare = new Hoare(env);

    // containerHoare
    (() => {
        var code = new EditInstructions($("#containerHoareCode"), hoare);
        var update = () => {};
        var inputPre = new EditVerificationFormula("true", () => update());
        var inputPost = new EditVerificationFormula("true", () => update());
        update = () =>
        {
            var pPre = inputPre.getFormula();
            var pPost = inputPost.getFormula();
            code.updateConditions(pPre, pPost);
        };
        update();
        $("#containerHoarePre").append(inputPre.createHTML());
        $("#containerHoarePost").append(inputPost.createHTML());

        $("#btnEx1").click(() => code.loadEx1());
        $("#btnEx2").click(() => code.loadEx2());
        $("#btnEx3").click(() => code.loadEx3());
        $("#btnEx4").click(() => code.loadEx4());

        $("#btnToggleDyn").click(x => $("#containerHoare").toggleClass("showDynamic"));
        $("#btnToggleDyn").mouseenter(x => $("#containerHoare").addClass("showSem"));
        $("#btnToggleDyn").mouseleave(x => $("#containerHoare").removeClass("showSem"));

        $("#containerHoareContext").text(printProgram(program));
    })();

    // containerProps
    (() => {
        var input = new EditVerificationFormula("", phi => {
            $("#containerPropsOutSat").text(phi.satisfiable() ? "yes" : "no");
            $("#containerPropsOutSfrm").text(phi.sfrm() ? "yes" : "no");
            $("#containerPropsOutNorm").text(phi.norm().toString());
        });
        $("#containerPropsInput").append(input.createHTML());
    })();

    // containerWoVar
    (() => {
        var update = () => {};
        var input = new EditVerificationFormula("", () => update());
        var inputVar = $("#containerWoVarInputVar");
        inputVar.on("input", () => update());
        update = () =>
        {
            var phi = input.getFormula();
            var x = inputVar.val();
            $("#containerWoVarOutput").text(phi.woVar(x).toString());
        };
        update();
        $("#containerWoVarInput").append(input.createHTML());
    })();
    
    // containerWoAcc
    (() => {
        var update = () => {};
        var input = new EditVerificationFormula("", () => update());
        var inputAcc = $("#containerWoAccInputAcc");
        inputAcc.on("input", () => update());
        update = () =>
        {
            var phi = input.getFormula();
            var accText = inputAcc.val();
            var accE = Expression.parse(accText);
            if (accE instanceof ExpressionDot)
                $("#containerWoAccOutput").text(phi.woAcc(accE.e, accE.f).toString());
            else
                $("#containerWoAccOutput").text("format error");
        };
        update();
        $("#containerWoAccInput").append(input.createHTML());
    })();
    
    // containerImplies
    (() => {
        var update = () => {};
        var inputA = new EditVerificationFormula("", () => update());
        var inputB = new EditVerificationFormula("", () => update());
        update = () =>
        {
            var pA = inputA.getFormula();
            var pB = inputB.getFormula();
            $("#containerImpliesOutput").text(pA.implies(pB.staticFormula) + "");
        };
        update();
        $("#containerImpliesInputA").append(inputA.createHTML());
        $("#containerImpliesInputB").append(inputB.createHTML());
    })();
    
    // containerSup
    (() => {
        var update = () => {};
        var inputA = new EditVerificationFormula("", () => update());
        var inputB = new EditVerificationFormula("", () => update());
        update = () =>
        {
            var pA = inputA.getFormula();
            var pB = inputB.getFormula();
            if (!pA.gradual)
            {
                inputA.setFormula(VerificationFormulaGradual.create(true, pA.staticFormula));
                return;
            }
            if (!pB.gradual)
            {
                inputB.setFormula(VerificationFormulaGradual.create(true, pB.staticFormula));
                return;
            }

            $("#containerSupOutput").text(VerificationFormulaGradual.supremum(pA, pB).toString());
        };
        update();
        $("#containerSupInputA").append(inputA.createHTML());
        $("#containerSupInputB").append(inputB.createHTML());
    })();

    $("#btnTESTS").click(() => testAll());

    // var editor = new EditInstructions(
    //     $("#codeContainer")
    //     //, hoare
    // );
    // $("#btnVerify").click(() => editor.btnCheckAll());
    // $("#btnHammer").click(() => editor.btnPropDownAll());
    // $("#btnReset").click(() => editor.btnResetAssertionsAll(false));
    // $("#btnResetQ").click(() => editor.btnResetAssertionsAll(true));
    // editor.loadEx1();
});