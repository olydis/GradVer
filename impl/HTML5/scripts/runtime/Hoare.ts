import { VerificationFormula, FormulaPart, FormulaPartAcc, FormulaPartType, FormulaPartNeq, FormulaPartEq } from "../types/VerificationFormula";
import { Statement, 
    StatementAlloc,
    StatementMemberSet,
    StatementAssign,
    } from "../types/Statement";
import { Type, TypeClass } from "../types/Type";
import { ExpressionX, Expression, ExpressionDot } from "../types/Expression";
import { ExecutionEnvironment } from "./ExecutionEnvironment";

class Hoare
{
    constructor(private env: ExecutionEnvironment) { }


    // NewObject
    private HoareCheckNewObject(s: StatementAlloc, phi: VerificationFormula): string
    {
        if (this.env.fields(s.C) == null) return "class '" + s.C + "' not found";
        if (phi.FV().some(x => x == s.x)) return "transfer-phi cannot contain variable '" + s.x + "'";
        return null;
    }
    private HoareGetPostNewObject(s: StatementAlloc, phi: VerificationFormula): VerificationFormula
    {
        var fs = this.env.fields(s.C);
        var ex = new ExpressionX(s.x);
        var res: FormulaPart[] = [];
        res.push(...fs.map(f => new FormulaPartAcc(ex, f.name)));
        res.push(new FormulaPartType(s.x, new TypeClass(s.C)));
        res.push(new FormulaPartNeq(ex, ExpressionX.getNull()));
        res.push(...phi.parts);
        return new VerificationFormula(null, res);
    }
    private HoareGetPreNewObject(s: StatementAlloc, phi: VerificationFormula): VerificationFormula
    {
        var res: FormulaPart[] = [];
        res.push(new FormulaPartType(s.x, new TypeClass(s.C)));
        res.push(...phi.parts);
        return new VerificationFormula(null, res);
    }

    // FieldAssign
    private HoareCheckFieldAssign(s: StatementMemberSet, phi: VerificationFormula): string
    {
        var Tx = phi.tryGetType(s.x);
        var Ty = phi.tryGetType(s.y);
        if (Tx == null) return "couldn't determine type of '" + s.x + "'";
        if (!(Tx instanceof TypeClass)) return "'" + s.x + "' must be class type";
        var Cx = (<TypeClass>Tx).C;
        var Cf = this.env.fieldType(Cx, s.f);
        if (Cf == null) return "class '" + Cx + "' doesn't have field '" + s.f + "'";
        if (Type.eq(Cf, Ty)) return "type mismatch of assignment";
        return null;
    }
    private HoareGetPostFieldAssign(s: StatementMemberSet, phi: VerificationFormula): VerificationFormula
    {
        var ex = new ExpressionX(s.x);
        var res: FormulaPart[] = [];
        res.push(new FormulaPartAcc(ex, s.f));
        res.push(new FormulaPartEq(new ExpressionDot(ex, s.f), new ExpressionX(s.y)));
        res.push(...phi.parts);
        return new VerificationFormula(null, res);
    }
    private HoareGetPreFieldAssign(s: StatementMemberSet, phi: VerificationFormula): VerificationFormula
    {
        var ex = new ExpressionX(s.x);
        var res: FormulaPart[] = [];
        res.push(...phi.parts);
        res.push(new FormulaPartAcc(ex, s.f));
        return new VerificationFormula(null, res);
    }

}