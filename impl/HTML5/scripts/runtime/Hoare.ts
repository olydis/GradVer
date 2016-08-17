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
    StatementDeclare,
    StatementCast,
    StatementComment
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
        checkStrucural: (s: Statement, preGamma: Gamma, onErr: (msg: string) => void) => 
                { info: any
                , postGamma: Gamma },
        checkImplication: (info: any) => 
                VerificationFormula,
        checkPost: (info: any, pre: VerificationFormulaGradual) => 
                VerificationFormulaGradual
    };

export class Hoare
{
    private ruleHandlers: Rule[];

    private addHandler<S extends Statement, StructuralInfo>(
        rule: string,
        SS: Ctor<S>,
        // returns null on error
        checkStrucural: (s: S, preGamma: Gamma, onErr: (msg: string) => void) => 
                { info: StructuralInfo
                , postGamma: Gamma },
        // cannot fail
        checkImplication: (info: StructuralInfo) => 
                VerificationFormula,
        // cannot fail
        checkPost: (info: StructuralInfo, pre: VerificationFormulaGradual) => 
                VerificationFormulaGradual
        ): void
    {
        var y = StatementAlloc;
        var x: typeof y;
        this.ruleHandlers.push({
            name: rule,
            statementMatch: s => s instanceof SS,
            checkStrucural: checkStrucural,
            checkImplication: checkImplication,
            checkPost: checkPost
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
        var res = rule.checkStrucural(s, g, msg => errs.push(msg));
        if (res == null) 
            return errs;

        var dyn = rule.checkImplication(res.info);
        var prex = pre.implies(dyn);
        if (prex == null)
            return ["could not prove: " + dyn];

        return null;
    }
    public post(s: Statement, pre: VerificationFormulaGradual, g: Gamma): { post: VerificationFormulaGradual, dyn: VerificationFormula, postGamma: Gamma }
    {
        var rule = this.getRule(s);

        var errs: string[] = [];
        var res = rule.checkStrucural(s, g, msg => errs.push(msg));
        if (res == null) 
            throw "call check first";

        var dyn = rule.checkImplication(res.info);
        pre = pre.implies(dyn);
        if (pre == null)
            throw "call check first";

        return {
            post: rule.checkPost(res.info, pre),
            dyn: dyn,
            postGamma: res.postGamma
        };
    }

    constructor(public env: ExecutionEnvironment) {
        this.ruleHandlers = [];

        this.addHandler<StatementAlloc, { ex: ExpressionX, fs: Field[] }>("NewObject", StatementAlloc,
            (s, g, onErr) => {
                var ex = new ExpressionX(s.x);
                var fs = this.env.fields(s.C);

                if (fs == null)
                {
                    onErr("class '" + s.C + "' not found");
                    return null;
                }
                var exT = ex.getType(env, g);
                if (!new TypeClass(s.C).compatibleWith(exT))
                {
                    onErr("type mismatch: " + s.C + " <-> " + exT);
                    return null;
                }

                return {
                    info: {
                        ex: ex,
                        fs: fs
                    },
                    postGamma: g
                };
            },
            (info) => VerificationFormula.empty(),
            (info, pre) => {
                pre = pre.woVar(info.ex.x);
                pre = pre.append(new FormulaPartNeq(info.ex, Expression.getNull()));
                for (var f of info.fs)
                    pre = pre.append(new FormulaPartAcc(info.ex, f.name));
                
                return pre;
            });
        this.addHandler<StatementMemberSet, { ex: ExpressionX, ey: ExpressionX, f: string }>("FieldAssign", StatementMemberSet,
            (s, g, onErr) => {
                var ex = new ExpressionX(s.x);
                var ey = new ExpressionX(s.y);
                var CT = ex.getType(env, g);

                if (CT instanceof TypeClass)
                {
                    var C = CT.C;
                    var fT = this.env.fieldType(C, s.f);
                    if (fT == null)
                    {
                        onErr("field not found");
                        return null;
                    }
                    var eyT = ey.getType(env, g);
                    if (!fT.compatibleWith(eyT))
                    {
                        onErr("type mismatch: " + fT + " <-> " + eyT);
                        return null;
                    }

                    return {
                        info: {
                            ex: ex,
                            ey: ey,
                            f: s.f
                        },
                        postGamma: g
                    };
                }
                onErr(ex + " not declared (as class type)");
                return null;
            },
            (info) => new FormulaPartAcc(info.ex, info.f).asFormula(),
            (info, pre) => {
                pre = pre.woAcc(info.ex, info.f);
                pre = pre.append(new FormulaPartAcc(info.ex, info.f));
                pre = pre.append(new FormulaPartNeq(info.ex, Expression.getNull()));
                pre = pre.append(new FormulaPartEq(new ExpressionDot(info.ex, info.f), info.ey));
                return pre;
            });
        this.addHandler<StatementAssign, { ex: ExpressionX, e: Expression }>("VarAssign", StatementAssign,
            (s, g, onErr) => {
                var ex = new ExpressionX(s.x);
                var xT = ex.getType(env, g);
                var eT = s.e.getType(env, g);

                if (xT == null)
                {
                    onErr(ex + " not declared");
                    return null;
                }
                if (!xT.compatibleWith(eT))
                {
                    onErr("type mismatch: " + xT + " <-> " + eT);
                    return null;
                }
                if (s.e.FV().indexOf(s.x) != -1)
                {
                    onErr("LHS not to appear in RHS");
                    return null;
                }
                
                return {
                    info: {
                        ex: ex,
                        e: s.e
                    },
                    postGamma: g
                };
            },
            (info) => new VerificationFormula(null, info.e.necessaryFraming().slice(0,1).map(a => new FormulaPartAcc(a.e, a.f))),
            (info, pre) => {
                pre = pre.woVar(info.ex.x);
                pre = pre.append(new FormulaPartEq(info.ex, info.e));
                return pre;
            });
        this.addHandler<StatementReturn, { ex: Expression, er: Expression }>("Return", StatementReturn,
            (s, g, onErr) => {
                var ex = new ExpressionX(s.x);
                var er = new ExpressionX(Expression.getResult());
                var xT = ex.getType(env, g);
                var rT = er.getType(env, g);

                if (xT == null)
                {
                    onErr(ex + " not declared");
                    return null;
                }
                if (!xT.compatibleWith(rT))
                {
                    onErr("type mismatch: " + xT + " <-> " + rT);
                    return null;
                }
                
                return {
                    info: {
                        ex: ex,
                        er: er
                    },
                    postGamma: g
                };
            },
            (info) => VerificationFormula.empty(),
            (info, pre) => {
                pre = pre.woVar(Expression.getResult());
                pre = pre.append(new FormulaPartEq(info.er, info.ex));
                return pre;
            });
        this.addHandler<StatementCall, { pre: VerificationFormulaGradual, post: VerificationFormulaGradual, ynn: FormulaPart, x: string }>("Call", StatementCall,
            (s, g, onErr) => {
                var ex = new ExpressionX(s.x);
                var ey = new ExpressionX(s.y);
                var ez = new ExpressionX(s.z);
                var exT = ex.getType(env, g);
                var eyT = ey.getType(env, g);
                var ezT = ez.getType(env, g);

                if (s.x == s.y || s.x == s.z)
                {
                    onErr("LHS not to appear in RHS");
                    return null;
                }

                if (eyT instanceof TypeClass)
                {
                    var C = eyT.C;
                    var m = this.env.mmethod(C, s.m);
                    if (m == null)
                    {
                        onErr("method not found");
                        return null;
                    }
                    if (!m.retType.compatibleWith(exT))
                    {
                        onErr("type mismatch: " + m.retType + " <-> " + exT);
                        return null;
                    }
                    if (!m.argType.compatibleWith(ezT))
                    {
                        onErr("type mismatch: " + m.argType + " <-> " + ezT);
                        return null;
                    }

                    var p_pre = m.frmPre.substs(xx => {
                        if (xx == Expression.getThis())
                            return s.y;
                        if (xx == m.argName)
                            return s.z;
                        return xx;
                    });

                    var p_post = m.frmPost.substs(xx => {
                        if (xx == Expression.getThis())
                            return s.y;
                        if (xx == m.argName)
                            return s.z;
                        if (xx == Expression.getResult())
                            return s.x;
                        return xx;
                    });

                    return {
                        info: {
                            pre: p_pre,
                            post: p_post,
                            ynn: new FormulaPartNeq(ey, Expression.getNull()),
                            x: s.x
                        },
                        postGamma: g
                    };
                }
                onErr(ex + " not declared (as class type)");
                return null;
            },
            (info) => info.pre.append(info.ynn).staticFormula,
            (info, pre) => {
                pre = pre.woVar(info.x);
                if (info.pre.gradual)
                    for (var fp of pre.staticFormula.footprintStatic())
                        pre = pre.woAcc(fp.e, fp.f);
                else
                    for (var fp of info.pre.staticFormula.footprintStatic())
                        pre = pre.woAcc(fp.e, fp.f);
                for (var p_part of info.post.staticFormula.parts)
                    pre = pre.append(p_part);

                // gradualness of info.post and info.pre
                pre = VerificationFormulaGradual.create(
                    info.pre.gradual || info.post.gradual || pre.gradual, 
                    pre.staticFormula);

                return pre;
            });
        this.addHandler<StatementAssert, VerificationFormula>("Assert", StatementAssert,
            (s, g, onErr) => {
                return {
                    info: s.assertion,
                    postGamma: g
                };
            },
            (info) => info,
            (info, pre) => {
                return pre;
            });
        this.addHandler<StatementRelease, VerificationFormula>("Release", StatementRelease,
            (s, g, onErr) => {
                return {
                    info: s.assertion,
                    postGamma: g
                };
            },
            (info) => info,
            (info, pre) => {
                for (var fp of info.footprintStatic())
                    pre = pre.woAcc(fp.e, fp.f);
                return pre;
            });
        this.addHandler<StatementDeclare, { ex: ExpressionX, T: Type }>("Declare", StatementDeclare,
            (s, g, onErr) => {
                var ex = new ExpressionX(s.x);
                var xT = ex.getType(env, g);
                if (xT)
                {
                    onErr("conflicting declaration");
                    return null;
                }

                return {
                    info: {
                        ex: ex,
                        T: s.T
                    },
                    postGamma: GammaAdd(s.x, s.T, g)
                };
            },
            (info) => VerificationFormula.empty(),
            (info, pre) => {
                pre = pre.woVar(info.ex.x);
                pre = pre.append(new FormulaPartEq(info.ex, info.T.defaultValue()));
                return pre;
            });
        this.addHandler<StatementCast, VerificationFormulaGradual>("Cast", StatementCast,
            (s, g, onErr) => {
                return {
                    info: s.T,
                    postGamma: g
                };
            },
            (info) => info.staticFormula,
            (info, pre) => {
                return info;
            });
        this.addHandler<StatementComment, { }>("Comment", StatementComment,
            (s, g, onErr) => {
                return {
                    info: { },
                    postGamma: g
                };
            },
            (info) => VerificationFormula.empty(),
            (info, pre) => {
                return pre;
            });
    }

}