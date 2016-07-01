define(["require", "exports", "../types/VerificationFormula", "../types/Type", "../types/Expression"], function (require, exports, VerificationFormula_1, Type_1, Expression_1) {
    "use strict";
    var Hoare = (function () {
        function Hoare(env) {
            this.env = env;
        }
        // NewObject
        Hoare.prototype.HoareCheckNewObject = function (s, phi) {
            if (this.env.fields(s.C) == null)
                return "class '" + s.C + "' not found";
            if (phi.FV().some(function (x) { return x == s.x; }))
                return "transfer-phi cannot contain variable '" + s.x + "'";
            return null;
        };
        Hoare.prototype.HoareGetPostNewObject = function (s, phi) {
            var fs = this.env.fields(s.C);
            var ex = new Expression_1.ExpressionX(s.x);
            var res = [];
            res.push.apply(res, fs.map(function (f) { return new VerificationFormula_1.FormulaPartAcc(ex, f.name); }));
            res.push(new VerificationFormula_1.FormulaPartType(s.x, new Type_1.TypeClass(s.C)));
            res.push(new VerificationFormula_1.FormulaPartNeq(ex, Expression_1.ExpressionX.getNull()));
            res.push.apply(res, phi.parts);
            return new VerificationFormula_1.VerificationFormula(null, res);
        };
        Hoare.prototype.HoareGetPreNewObject = function (s, phi) {
            var res = [];
            res.push(new VerificationFormula_1.FormulaPartType(s.x, new Type_1.TypeClass(s.C)));
            res.push.apply(res, phi.parts);
            return new VerificationFormula_1.VerificationFormula(null, res);
        };
        // FieldAssign
        Hoare.prototype.HoareCheckFieldAssign = function (s, phi) {
            var Tx = phi.tryGetType(s.x);
            var Ty = phi.tryGetType(s.y);
            if (Tx == null)
                return "couldn't determine type of '" + s.x + "'";
            if (!(Tx instanceof Type_1.TypeClass))
                return "'" + s.x + "' must be class type";
            var Cx = Tx.C;
            var Cf = this.env.fieldType(Cx, s.f);
            if (Cf == null)
                return "class '" + Cx + "' doesn't have field '" + s.f + "'";
            if (Type_1.Type.eq(Cf, Ty))
                return "type mismatch of assignment";
            return null;
        };
        Hoare.prototype.HoareGetPostFieldAssign = function (s, phi) {
            var ex = new Expression_1.ExpressionX(s.x);
            var res = [];
            res.push(new VerificationFormula_1.FormulaPartAcc(ex, s.f));
            res.push(new VerificationFormula_1.FormulaPartEq(new Expression_1.ExpressionDot(ex, s.f), new Expression_1.ExpressionX(s.y)));
            res.push.apply(res, phi.parts);
            return new VerificationFormula_1.VerificationFormula(null, res);
        };
        Hoare.prototype.HoareGetPreFieldAssign = function (s, phi) {
            var ex = new Expression_1.ExpressionX(s.x);
            var res = [];
            res.push.apply(res, phi.parts);
            res.push(new VerificationFormula_1.FormulaPartAcc(ex, s.f));
            return new VerificationFormula_1.VerificationFormula(null, res);
        };
        return Hoare;
    }());
});
