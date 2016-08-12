define(["require", "exports", "./editors/EditInstructions", "./editors/EditVerificationFormula", "./editors/EditableElement", "./runtime/ExecutionEnvironment", "./types/Expression", "./runtime/Hoare", "./testing/MainTest", "./types/VerificationFormulaGradual", "./types/Type"], function (require, exports, EditInstructions_1, EditVerificationFormula_1, EditableElement_1, ExecutionEnvironment_1, Expression_1, Hoare_1, MainTest_1, VerificationFormulaGradual_1, Type_1) {
    "use strict";
    $(function () {
        $(window).click(function () { return EditableElement_1.EditableElement.editEndAll(); });
        var program = {
            classes: [
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
                        }],
                    methods: []
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
                        }],
                    methods: []
                }],
            main: []
        };
        var env = new ExecutionEnvironment_1.ExecutionEnvironment(program);
        var hoare = new Hoare_1.Hoare(env);
        // containerHoare
        (function () {
            var code = new EditInstructions_1.EditInstructions($("#containerHoareCode"), hoare);
            var update = function () { };
            var inputPre = new EditVerificationFormula_1.EditVerificationFormula("?", function () { return update(); });
            var inputPost = new EditVerificationFormula_1.EditVerificationFormula("?", function () { return update(); });
            update = function () {
                var pPre = inputPre.getFormula();
                var pPost = inputPost.getFormula();
                code.updateConditions(pPre, pPost);
            };
            update();
            $("#containerHoarePre").append(inputPre.createHTML());
            $("#containerHoarePost").append(inputPost.createHTML());
            $("#btnEx1").click(function () { return code.loadEx1(); });
        })();
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
    });
});
