import { EditInstructions } from "./editors/EditInstructions";
import { EditVerificationFormula } from "./editors/EditVerificationFormula";
import { EditableElement } from "./editors/EditableElement";
import { ExecutionEnvironment } from "./runtime/ExecutionEnvironment";
import { Expression, ExpressionDot, ExpressionX } from "./types/Expression";
import { Hoare } from "./runtime/Hoare";
import { GammaNew, GammaAdd } from "./runtime/Gamma";
import { Program, printProgram, Class, Method } from "./runtime/Program";
import { testAll } from "./testing/MainTest";
import { VerificationFormulaGradual } from "./types/VerificationFormulaGradual";
import { Type, TypeClass } from "./types/Type";
import { Statement } from "./types/Statement";
import { VerificationFormula, FormulaPart, FormulaPartEq, FormulaPartNeq } from "./types/VerificationFormula";

function unique<T>(list: T[]): boolean
{
    for (var i = 0; i < list.length; ++i)
        if (list.indexOf(list[i], i + 1) != -1)
            return false;
    return true;
}

function wellFormedProgram(p: Program, hoare: Hoare): string
{
    var res: string = null;
    if (res == null) res = hoare.checkMethod(GammaNew, p.main, new VerificationFormulaGradual("true"), new VerificationFormulaGradual("true"));
    if (res == null) res = p.classes.map(c => wellFormedClass(c, hoare)).filter(x => x != null)[0];
    return res;
}
function wellFormedClass(c: Class, hoare: Hoare): string
{
    var res: string = null;
    if (res == null) res = unique(c.fields.map(x => x.name)) ? null : "fields not unique";
    if (res == null) res = unique(c.methods.map(x => x.name)) ? null : "methods not unique";
    if (res == null) res = c.methods.map(m => wellFormedMethod(c, m, hoare)).filter(x => x != null)[0];
    return res;
}
function wellFormedMethod(c: Class, m: Method, hoare: Hoare): string
{
    var augmentPre = new FormulaPartNeq(new ExpressionX(Expression.getThis()), Expression.getNull());

    var res: string = null;
    if (res == null) res = m.frmPre.staticFormula.FV().every(x => x == m.argName || x == Expression.getThis())
                                ? null : "precodiction contains unknown variables: " + m.frmPre;
    if (res == null) res = m.frmPost.staticFormula.FV().every(x => x == m.argName || x == Expression.getThis() || x == Expression.getResult())
                                ? null : "postcodiction contains unknown variables: " + m.frmPost;
    if (res == null) res = hoare.checkMethod(
        GammaAdd(m.argName, m.argType, 
        GammaAdd(Expression.getThis(), new TypeClass(c.name), 
        GammaAdd(Expression.getResult(), m.retType, GammaNew))), m.body, m.frmPre.append(augmentPre), m.frmPost);
    if (res == null) res = m.frmPre.sfrm() ? null : "precondition not self-framed: " + m.frmPre;
    if (res == null) res = m.frmPost.sfrm() ? null : "postcondition not self-framed: " + m.frmPost;
    if (res == null) res = m.body.filter(s => s.writesTo(m.argName)).map(s => s + " writes to " + m.argName)[0];
    return res;
}

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
            methods: [
                {
                    name: "insertAfter",
                    retType: new TypeClass("void"),
                    argType: new TypeClass("Point"),
                    argName: "p",
                    frmPre: new VerificationFormulaGradual("acc(this.t)"),
                    frmPost: new VerificationFormulaGradual("acc(this.t) * acc(this.t.h) * acc(this.t.t)"),
                    body: [
                        Statement.parse("Points t;"),
                        Statement.parse("t = new Points;"),
                        Statement.parse("t.h = p;"),
                        Statement.parse("Points temp;"),
                        Statement.parse("temp = this.t;"),
                        Statement.parse("t.t = temp;"),
                        Statement.parse("this.t = t;")
                    ]
                },
                {
                    name: "insertHere",
                    retType: new TypeClass("void"),
                    argType: new TypeClass("Point"),
                    argName: "p",
                    frmPre: new VerificationFormulaGradual("acc(this.h) * acc(this.t)"),
                    frmPost: new VerificationFormulaGradual("acc(this.h) * acc(this.t)"),
                    body: [
                        Statement.parse("Points t;"),
                        Statement.parse("t = new Points;"),
                        Statement.parse("Point temp1;"),
                        Statement.parse("temp1 = this.h;"),
                        Statement.parse("t.h = temp1;"),
                        Statement.parse("Points temp2;"),
                        Statement.parse("temp2 = this.t;"),
                        Statement.parse("t.t = temp2;"),
                        Statement.parse("this.t = t;"),
                        Statement.parse("this.h = p;")
                    ]
                }
            ]
        },
        {
            name: "FramingChallenge",
            fields: [],
            methods: [
                {
                    name: "baz",
                    retType: new TypeClass("void"),
                    argType: new TypeClass("Point"),
                    argName: "p",
                    frmPre: new VerificationFormulaGradual("?"),
                    frmPost: new VerificationFormulaGradual("?"),
                    body: [
                        Statement.parse("int i;"),
                        Statement.parse("i = -1;"),
                        Statement.parse("p.x = i;"),
                        Statement.parse("p.y = i;")
                    ]
                },
                {
                    name: "bar",
                    retType: new TypeClass("void"),
                    argType: new TypeClass("Point"),
                    argName: "p",
                    frmPre: new VerificationFormulaGradual("acc(p.x) * (p.x != -1)"),
                    frmPost: new VerificationFormulaGradual("acc(p.x) * (p.x == -1)"),
                    body: [
                        Statement.parse("void _;"),
                        Statement.parse("_ = this.baz(p);")
                    ]
                },
                {
                    name: "barg",
                    retType: new TypeClass("void"),
                    argType: new TypeClass("Point"),
                    argName: "p",
                    frmPre: new VerificationFormulaGradual("? * acc(p.x) * (p.x != -1)"),
                    frmPost: new VerificationFormulaGradual("acc(p.x) * (p.x == -1)"),
                    body: [
                        Statement.parse("void _;"),
                        Statement.parse("_ = this.baz(p);")
                    ]
                },
                {
                    name: "foo",
                    retType: new TypeClass("void"),
                    argType: new TypeClass("void"),
                    argName: "__",
                    frmPre: new VerificationFormulaGradual("true"),
                    frmPost: new VerificationFormulaGradual("true"),
                    body: [
                        Statement.parse("void _;"),
                        Statement.parse("int i0;"),
                        Statement.parse("Point p;"),
                        Statement.parse("p = new Point;"),
                        Statement.parse("p.x = i0;"),
                        Statement.parse("p.y = i0;"),
                        Statement.parse("assert acc(p.y) * (p.y = 0) * acc(p.x) * (p.x = 0)"),
                        Statement.parse("_ = this.bar(p);"),
                        Statement.parse("assert acc(p.y) * (p.y = 0)"),
                    ]
                }
            ]
        }],
        main: []
    };
    var env = new ExecutionEnvironment(program);
    var hoare = new Hoare(env);
    // var wellFormedMessage = wellFormedProgram(program, hoare);
    // if (wellFormedMessage != null)
    //     window.alert("program not well formed: " + wellFormedMessage);

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
        $("#btnEx5").click(() => code.loadEx5());

        $("#btnToggleDyn").click(x => $("#containerHoare").toggleClass("showDynamic"));
        $("#btnToggleDyn").mouseenter(x => $("#containerHoare").addClass("showSem"));
        $("#btnToggleDyn").mouseleave(x => $("#containerHoare").removeClass("showSem"));

        $("#containerHoareContext").text(printProgram(program));
    })();
});

function additionalInit()
{
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
}