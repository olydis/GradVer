define(["require", "exports", "./editors/EditInstructions", "./editors/EditVerificationFormula", "./editors/EditableElement", "./runtime/ExecutionEnvironment", "./types/Expression", "./runtime/Hoare", "./runtime/Gamma", "./runtime/Program", "./testing/MainTest", "./types/VerificationFormulaGradual", "./types/Type", "./types/Statement", "./types/VerificationFormula"], function (require, exports, EditInstructions_1, EditVerificationFormula_1, EditableElement_1, ExecutionEnvironment_1, Expression_1, Hoare_1, Gamma_1, Program_1, MainTest_1, VerificationFormulaGradual_1, Type_1, Statement_1, VerificationFormula_1) {
    "use strict";
    function unique(list) {
        for (var i = 0; i < list.length; ++i)
            if (list.indexOf(list[i], i + 1) != -1)
                return false;
        return true;
    }
    function wellFormedProgram(p, hoare) {
        var res = null;
        if (res == null)
            res = hoare.checkMethod(Gamma_1.GammaNew, p.main, new VerificationFormulaGradual_1.VerificationFormulaGradual("true"), new VerificationFormulaGradual_1.VerificationFormulaGradual("true"));
        if (res == null)
            res = p.classes.map(function (c) { return wellFormedClass(c, hoare); }).filter(function (x) { return x != null; })[0];
        return res;
    }
    function wellFormedClass(c, hoare) {
        var res = null;
        if (res == null)
            res = unique(c.fields.map(function (x) { return x.name; })) ? null : "fields not unique";
        if (res == null)
            res = unique(c.methods.map(function (x) { return x.name; })) ? null : "methods not unique";
        if (res == null)
            res = c.methods.map(function (m) { return wellFormedMethod(c, m, hoare); }).filter(function (x) { return x != null; })[0];
        return res;
    }
    function wellFormedMethod(c, m, hoare) {
        var augmentPre = new VerificationFormula_1.FormulaPartNeq(new Expression_1.ExpressionX(Expression_1.Expression.getThis()), Expression_1.Expression.getNull());
        var res = null;
        if (res == null)
            res = m.frmPre.staticFormula.FV().every(function (x) { return x == m.argName || x == Expression_1.Expression.getThis(); })
                ? null : "precodiction contains unknown variables: " + m.frmPre;
        if (res == null)
            res = m.frmPost.staticFormula.FV().every(function (x) { return x == m.argName || x == Expression_1.Expression.getThis() || x == Expression_1.Expression.getResult(); })
                ? null : "postcodiction contains unknown variables: " + m.frmPost;
        if (res == null)
            res = hoare.checkMethod(Gamma_1.GammaAdd(m.argName, m.argType, Gamma_1.GammaAdd(Expression_1.Expression.getThis(), new Type_1.TypeClass(c.name), Gamma_1.GammaAdd(Expression_1.Expression.getResult(), m.retType, Gamma_1.GammaNew))), m.body, m.frmPre.append(augmentPre), m.frmPost);
        if (res == null)
            res = m.frmPre.sfrm() ? null : "precondition not self-framed: " + m.frmPre;
        if (res == null)
            res = m.frmPost.sfrm() ? null : "postcondition not self-framed: " + m.frmPost;
        if (res == null)
            res = m.body.filter(function (s) { return s.writesTo(m.argName); }).map(function (s) { return s + " writes to " + m.argName; })[0];
        return res;
    }
    $(function () {
        $(window).click(function () { return EditableElement_1.EditableElement.editEndAll(); });
        var program = {
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
                            type: Type_1.Type.getPrimitiveInt()
                        },
                        {
                            name: "y",
                            type: Type_1.Type.getPrimitiveInt()
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
                            retType: new Type_1.TypeClass("Point"),
                            argType: new Type_1.TypeClass("void"),
                            argName: "_",
                            frmPre: new VerificationFormulaGradual_1.VerificationFormulaGradual("acc(this.x) * acc(this.y)"),
                            frmPost: new VerificationFormulaGradual_1.VerificationFormulaGradual("acc(this.x) * acc(this.y) * acc(result.x) * acc(result.y) * this.x = result.y * this.y = result.x"),
                            body: [
                                Statement_1.Statement.parse("int t;"),
                                Statement_1.Statement.parse("Point res;"),
                                Statement_1.Statement.parse("res = new Point;"),
                                Statement_1.Statement.parse("t = this.y;"),
                                Statement_1.Statement.parse("res.x = t;"),
                                Statement_1.Statement.parse("t = this.x;"),
                                Statement_1.Statement.parse("res.y = t;"),
                                Statement_1.Statement.parse("return res;"),
                            ]
                        },
                        {
                            name: "swapXYstrong",
                            retType: new Type_1.TypeClass("Point"),
                            argType: new Type_1.TypeClass("void"),
                            argName: "_",
                            frmPre: new VerificationFormulaGradual_1.VerificationFormulaGradual("acc(this.x) * acc(this.y)"),
                            frmPost: new VerificationFormulaGradual_1.VerificationFormulaGradual("? * acc(this.x) * acc(this.y) * acc(result.x) * acc(result.y) * this.x = result.y * this.y = result.x"),
                            body: [
                                Statement_1.Statement.parse("int t;"),
                                Statement_1.Statement.parse("Point res;"),
                                Statement_1.Statement.parse("res = new Point;"),
                                Statement_1.Statement.parse("t = this.y;"),
                                Statement_1.Statement.parse("res.x = t;"),
                                Statement_1.Statement.parse("t = this.x;"),
                                Statement_1.Statement.parse("res.y = t;"),
                                Statement_1.Statement.parse("return res;"),
                            ]
                        }
                    ]
                },
                {
                    name: "Points",
                    fields: [
                        {
                            name: "h",
                            type: new Type_1.TypeClass("Point")
                        },
                        {
                            name: "t",
                            type: new Type_1.TypeClass("Points")
                        }
                    ],
                    methods: [
                        {
                            name: "insertAfter",
                            retType: new Type_1.TypeClass("void"),
                            argType: new Type_1.TypeClass("Point"),
                            argName: "p",
                            frmPre: new VerificationFormulaGradual_1.VerificationFormulaGradual("acc(this.t)"),
                            frmPost: new VerificationFormulaGradual_1.VerificationFormulaGradual("acc(this.t) * acc(this.t.h) * acc(this.t.t)"),
                            body: [
                                Statement_1.Statement.parse("Points t;"),
                                Statement_1.Statement.parse("t = new Points;"),
                                Statement_1.Statement.parse("t.h = p;"),
                                Statement_1.Statement.parse("Points temp;"),
                                Statement_1.Statement.parse("temp = this.t;"),
                                Statement_1.Statement.parse("t.t = temp;"),
                                Statement_1.Statement.parse("this.t = t;")
                            ]
                        },
                        {
                            name: "insertHere",
                            retType: new Type_1.TypeClass("void"),
                            argType: new Type_1.TypeClass("Point"),
                            argName: "p",
                            frmPre: new VerificationFormulaGradual_1.VerificationFormulaGradual("acc(this.h) * acc(this.t)"),
                            frmPost: new VerificationFormulaGradual_1.VerificationFormulaGradual("acc(this.h) * acc(this.t)"),
                            body: [
                                Statement_1.Statement.parse("Points t;"),
                                Statement_1.Statement.parse("t = new Points;"),
                                Statement_1.Statement.parse("Point temp1;"),
                                Statement_1.Statement.parse("temp1 = this.h;"),
                                Statement_1.Statement.parse("t.h = temp1;"),
                                Statement_1.Statement.parse("Points temp2;"),
                                Statement_1.Statement.parse("temp2 = this.t;"),
                                Statement_1.Statement.parse("t.t = temp2;"),
                                Statement_1.Statement.parse("this.t = t;"),
                                Statement_1.Statement.parse("this.h = p;")
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
                            retType: new Type_1.TypeClass("void"),
                            argType: new Type_1.TypeClass("Point"),
                            argName: "p",
                            frmPre: new VerificationFormulaGradual_1.VerificationFormulaGradual("?"),
                            frmPost: new VerificationFormulaGradual_1.VerificationFormulaGradual("?"),
                            body: [
                                Statement_1.Statement.parse("int i;"),
                                Statement_1.Statement.parse("i = -1;"),
                                Statement_1.Statement.parse("p.x = i;"),
                                Statement_1.Statement.parse("p.y = i;")
                            ]
                        },
                        {
                            name: "bar",
                            retType: new Type_1.TypeClass("void"),
                            argType: new Type_1.TypeClass("Point"),
                            argName: "p",
                            frmPre: new VerificationFormulaGradual_1.VerificationFormulaGradual("acc(p.x) * (p.x != -1)"),
                            frmPost: new VerificationFormulaGradual_1.VerificationFormulaGradual("acc(p.x) * (p.x == -1)"),
                            body: [
                                Statement_1.Statement.parse("void _;"),
                                Statement_1.Statement.parse("_ = this.baz(p);")
                            ]
                        },
                        {
                            name: "barg",
                            retType: new Type_1.TypeClass("void"),
                            argType: new Type_1.TypeClass("Point"),
                            argName: "p",
                            frmPre: new VerificationFormulaGradual_1.VerificationFormulaGradual("? * acc(p.x) * (p.x != -1)"),
                            frmPost: new VerificationFormulaGradual_1.VerificationFormulaGradual("acc(p.x) * (p.x == -1)"),
                            body: [
                                Statement_1.Statement.parse("void _;"),
                                Statement_1.Statement.parse("_ = this.baz(p);")
                            ]
                        },
                        {
                            name: "foo",
                            retType: new Type_1.TypeClass("void"),
                            argType: new Type_1.TypeClass("void"),
                            argName: "__",
                            frmPre: new VerificationFormulaGradual_1.VerificationFormulaGradual("true"),
                            frmPost: new VerificationFormulaGradual_1.VerificationFormulaGradual("true"),
                            body: [
                                Statement_1.Statement.parse("void _;"),
                                Statement_1.Statement.parse("int i0;"),
                                Statement_1.Statement.parse("Point p;"),
                                Statement_1.Statement.parse("p = new Point;"),
                                Statement_1.Statement.parse("p.x = i0;"),
                                Statement_1.Statement.parse("p.y = i0;"),
                                Statement_1.Statement.parse("assert acc(p.y) * (p.y = 0) * acc(p.x) * (p.x = 0)"),
                                Statement_1.Statement.parse("_ = this.bar(p);"),
                                Statement_1.Statement.parse("assert acc(p.y) * (p.y = 0)"),
                            ]
                        }
                    ]
                }],
            main: []
        };
        var env = new ExecutionEnvironment_1.ExecutionEnvironment(program);
        var hoare = new Hoare_1.Hoare(env);
        // var wellFormedMessage = wellFormedProgram(program, hoare);
        // if (wellFormedMessage != null)
        //     window.alert("program not well formed: " + wellFormedMessage);
        // containerHoare
        (function () {
            var code = new EditInstructions_1.EditInstructions($("#containerHoareCode"), hoare);
            var update = function () { };
            var inputPre = new EditVerificationFormula_1.EditVerificationFormula("true", function () { return update(); });
            var inputPost = new EditVerificationFormula_1.EditVerificationFormula("true", function () { return update(); });
            update = function () {
                var pPre = inputPre.getFormula();
                var pPost = inputPost.getFormula();
                code.updateConditions(pPre, pPost);
            };
            update();
            $("#containerHoarePre").append(inputPre.createHTML());
            $("#containerHoarePost").append(inputPost.createHTML());
            $("#btnEx1").click(function () { return code.loadEx1(); });
            $("#btnEx2").click(function () { return code.loadEx2(); });
            $("#btnEx3").click(function () { return code.loadEx3(); });
            $("#btnEx4").click(function () { return code.loadEx4(); });
            $("#btnEx5").click(function () { return code.loadEx5(); });
            $("#btnToggleDyn").click(function (x) { return $("#containerHoare").toggleClass("showDynamic"); });
            $("#btnToggleDyn").mouseenter(function (x) { return $("#containerHoare").addClass("showSem"); });
            $("#btnToggleDyn").mouseleave(function (x) { return $("#containerHoare").removeClass("showSem"); });
            $("#containerHoareContext").text(Program_1.printProgram(program));
        })();
    });
    function additionalInit() {
        // containerProps
        (function () {
            var input = new EditVerificationFormula_1.EditVerificationFormula("", function (phi) {
                $("#containerPropsOutSat").text(phi.satisfiable() ? "yes" : "no");
                $("#containerPropsOutSfrm").text(phi.sfrm() ? "yes" : "no");
                $("#containerPropsOutNorm").text(phi.norm().toString());
            });
            $("#containerPropsInput").append(input.createHTML());
        })();
        // containerWoVar
        (function () {
            var update = function () { };
            var input = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            var inputVar = $("#containerWoVarInputVar");
            inputVar.on("input", function () { return update(); });
            update = function () {
                var phi = input.getFormula();
                var x = inputVar.val();
                $("#containerWoVarOutput").text(phi.woVar(x).toString());
            };
            update();
            $("#containerWoVarInput").append(input.createHTML());
        })();
        // containerWoAcc
        (function () {
            var update = function () { };
            var input = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            var inputAcc = $("#containerWoAccInputAcc");
            inputAcc.on("input", function () { return update(); });
            update = function () {
                var phi = input.getFormula();
                var accText = inputAcc.val();
                var accE = Expression_1.Expression.parse(accText);
                if (accE instanceof Expression_1.ExpressionDot)
                    $("#containerWoAccOutput").text(phi.woAcc(accE.e, accE.f).toString());
                else
                    $("#containerWoAccOutput").text("format error");
            };
            update();
            $("#containerWoAccInput").append(input.createHTML());
        })();
        // containerImplies
        (function () {
            var update = function () { };
            var inputA = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            var inputB = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            update = function () {
                var pA = inputA.getFormula();
                var pB = inputB.getFormula();
                $("#containerImpliesOutput").text(pA.implies(pB.staticFormula) + "");
            };
            update();
            $("#containerImpliesInputA").append(inputA.createHTML());
            $("#containerImpliesInputB").append(inputB.createHTML());
        })();
        // containerSup
        (function () {
            var update = function () { };
            var inputA = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            var inputB = new EditVerificationFormula_1.EditVerificationFormula("", function () { return update(); });
            update = function () {
                var pA = inputA.getFormula();
                var pB = inputB.getFormula();
                if (!pA.gradual) {
                    inputA.setFormula(VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, pA.staticFormula));
                    return;
                }
                if (!pB.gradual) {
                    inputB.setFormula(VerificationFormulaGradual_1.VerificationFormulaGradual.create(true, pB.staticFormula));
                    return;
                }
                $("#containerSupOutput").text(VerificationFormulaGradual_1.VerificationFormulaGradual.supremum(pA, pB).toString());
            };
            update();
            $("#containerSupInputA").append(inputA.createHTML());
            $("#containerSupInputB").append(inputB.createHTML());
        })();
        $("#btnTESTS").click(function () { return MainTest_1.testAll(); });
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
});
