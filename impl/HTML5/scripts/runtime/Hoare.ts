import { VerificationFormula, FormulaPart, FormulaPartAcc, FormulaPartNeq, FormulaPartEq } from "../types/VerificationFormula";
import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual"
import { Statement,
    StatementAlloc,
    StatementMemberSet,
    StatementAssign,
    StatementReturn,
    StatementCall,
    StatementAssert,
    StatementRelease,
    StatementDeclare
    } from "../types/Statement";
import { Type, TypeClass } from "../types/Type";
import { ExpressionX, Expression, ExpressionDot, ExpressionV } from "../types/Expression";
import { ExecutionEnvironment } from "./ExecutionEnvironment";
import { Field, Method } from "./Program";
import { Gamma, GammaAdd } from "./Gamma";

type Ctor<T> = { new(... args: any[]): T };

type Rule = {
        name: string,
        statementMatch: (s: Statement) => boolean,
        check: (s: Statement, pre: VerificationFormulaGradual, preGamma: Gamma, onErr: (msg: string) => void) => 
                { post: VerificationFormulaGradual, dyn: VerificationFormula, postGamma: Gamma },
    };

export class Hoare
{
    private ruleHandlers: Rule[];

    private addHandler<S extends Statement>(
        rule: string,
        SS: Ctor<S>,
        check: (s: S, pre: VerificationFormulaGradual, preGamma: Gamma, onErr: (msg: string) => void) => 
                { post: VerificationFormulaGradual, dyn: VerificationFormula, postGamma: Gamma }): void
    {
        var y = StatementAlloc;
        var x: typeof y;
        this.ruleHandlers.push({
            name: rule,
            statementMatch: s => s instanceof SS,
            check: check
        });
    }

    private getRule(s: Statement): Rule
    {
        for (var rule of this.ruleHandlers)
            if (rule.statementMatch(s))
                return rule;
        throw "unknown statement type";
    }
    public check(s: Statement, pre: VerificationFormulaGradual, g: Gamma): string[]
    {
        var rule = this.getRule(s);
        var errs: string[] = [];
        var res = rule.check(s, pre, g, msg => errs.push(msg));
        return res == null ? errs : null;
    }
    public post(s: Statement, pre: VerificationFormulaGradual, g: Gamma): { post: VerificationFormulaGradual, dyn: VerificationFormula, postGamma: Gamma }
    {
        var rule = this.getRule(s);
        var errs: string[] = [];
        return rule.check(s, pre, g, msg => errs.push(msg));
    }

    constructor(private env: ExecutionEnvironment) {
        this.ruleHandlers = [];

        this.addHandler<StatementAlloc>("NewObject", StatementAlloc,
            (s, pre, g, onErr) => {
                var ex = new ExpressionX(s.x);
                var fs = this.env.fields(s.C);

                // check
                if (fs == null)
                {
                    onErr("class '" + s.C + "' not found");
                    return null;
                }
                if (!new TypeClass(s.C).compatibleWith(ex.getType(env, g)))
                {
                    onErr("type mismatch");
                    return null;
                }

                // processing
                pre = pre.woVar(s.x);
                pre = pre.append(new FormulaPartNeq(ex, Expression.getNull()));
                for (var f of fs)
                    pre = pre.append(new FormulaPartAcc(ex, f.name));
                
                return {
                    post: pre,
                    dyn: VerificationFormula.empty(),
                    postGamma: g
                };
            });
        this.addHandler<StatementMemberSet>("FieldAssign", StatementMemberSet,
            (s, pre, g, onErr) => {
                var ex = new ExpressionX(s.x);
                var ey = new ExpressionX(s.y);
                var CT = ex.getType(env, g);

                // check
                if (CT instanceof TypeClass)
                {
                    var C = CT.C;
                    var fT = this.env.fieldType(C, s.f);
                    if (fT == null)
                    {
                        onErr("field not found");
                        return null;
                    }
                    if (!fT.compatibleWith(ey.getType(env, g)))
                    {
                        onErr("type mismatch");
                        return null;
                    }

                    // processing
                    var accPart = new FormulaPartAcc(ex, s.f);
                    var dyn = pre.impliesRuntime(new VerificationFormula(null, [accPart]));
                    pre = pre.woAcc(ex, s.f);
                    pre = pre.append(accPart);
                    pre = pre.append(new FormulaPartNeq(ex, Expression.getNull()));
                    pre = pre.append(new FormulaPartEq(new ExpressionDot(ex, s.f), ey));
                    
                    return {
                        post: pre,
                        dyn: dyn,
                        postGamma: g
                    };
                }
                onErr("type error");
                return null;
            });
        this.addHandler<StatementAssign>("VarAssign", StatementAssign,
            (s, pre, g, onErr) => {
                var ex = new ExpressionX(s.x);
                var xT = ex.getType(env, g);
                var eT = s.e.getType(env, g);

                // check
                if (xT == null)
                {
                    onErr("type error");
                    return null;
                }
                if (!xT.compatibleWith(eT))
                {
                    onErr("type mismatch");
                    return null;
                }

                // processing
                pre = pre.woVar(s.x);
                var accParts = s.e.necessaryFraming().map(a => new FormulaPartAcc(a.e, a.f));
                var dyn = pre.impliesRuntime(new VerificationFormula(null, accParts));
                pre = pre.append(new FormulaPartEq(ex, s.e));
                
                return {
                    post: pre,
                    dyn: dyn,
                    postGamma: g
                };
            });
        this.addHandler<StatementReturn>("Return", StatementReturn,
            (s, pre, g, onErr) => {
                var ex = new ExpressionX(s.x);
                var er = new ExpressionX(Expression.getResult());
                var xT = ex.getType(env, g);
                var rT = er.getType(env, g);

                // check
                if (xT == null)
                {
                    onErr("type error");
                    return null;
                }
                if (!xT.compatibleWith(rT))
                {
                    onErr("type mismatch");
                    return null;
                }

                // processing
                pre = pre.woVar(Expression.getResult());
                pre = pre.append(new FormulaPartEq(er, ex));
                
                return {
                    post: pre,
                    dyn: VerificationFormula.empty(),
                    postGamma: g
                };
            });
        this.addHandler<StatementCall>("Call", StatementCall,
            (s, pre, g, onErr) => {
                return null;
                // throw "not implemented";
            });
        this.addHandler<StatementAssert>("Assert", StatementAssert,
            (s, pre, g, onErr) => {
                var dyn = pre.impliesRuntime(s.assertion);
                pre = pre.implies(s.assertion);
                
                return {
                    post: pre,
                    dyn: dyn,
                    postGamma: g
                };
            });
        this.addHandler<StatementRelease>("Release", StatementRelease,
            (s, pre, g, onErr) => {
                var dyn = pre.impliesRuntime(s.assertion);

                // processing
                pre = pre.implies(s.assertion);
                for (var fp of s.assertion.footprintStatic())
                    pre = pre.woAcc(fp.e, fp.f);
                
                return {
                    post: pre,
                    dyn: dyn,
                    postGamma: g
                };
            });
        this.addHandler<StatementDeclare>("Declare", StatementDeclare,
            (s, pre, g, onErr) => {
                var ex = new ExpressionX(s.x);
                var xT = ex.getType(env, g);
                if (xT)
                {
                    onErr("already defined");
                    return null;
                }

                pre = pre.append(new FormulaPartEq(ex, s.T.defaultValue()));

                return {
                    post: pre,
                    dyn: VerificationFormula.empty(),
                    postGamma: GammaAdd(s.x, s.T, g)
                };
            });
    }

}