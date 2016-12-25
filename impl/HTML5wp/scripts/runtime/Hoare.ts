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
    StatementComment,
    StatementHold,
    StatementUnhold
    } from "../types/Statement";
import { Type, TypeClass } from "../types/Type";
import { FootprintStatic } from "../types/Footprint";
import { ExpressionX, Expression, ExpressionDot, ExpressionV } from "../types/Expression";
import { ExecutionEnvironment } from "./ExecutionEnvironment";
import { Field, Method } from "./Program";
import { Gamma, GammaAdd } from "./Gamma";

type Ctor<T> = { new(... args: any[]): T };


type ScopeStackItem = { 
                postProc: (post: VerificationFormulaGradual) => VerificationFormulaGradual,
                checkInnerStmt: (stmt: Statement) => string,
                gamma: Gamma
            };

type Rule = {
        name: string,
        statementMatch: (s: Statement) => boolean,
        checkStrucural: (s: Statement, preGamma: Gamma, onErr: (msg: string) => void, 
            scopeStack: ScopeStackItem[]) => 
                { info: any
                , postGamma: Gamma },
        wlp: (info: any, post: VerificationFormulaGradual, 
            scopeStack: ScopeStackItem[]) => 
                VerificationFormulaGradual,
        checkImplication: (info: any) => 
                VerificationFormula,
        checkPost: (info: any, pre: VerificationFormulaGradual, 
            scopeStack: ScopeStackItem[]) => 
                VerificationFormulaGradual
    };

export class Hoare
{
    private ruleHandlers: Rule[];

    private addHandler<S extends Statement, StructuralInfo>(
        rule: string,
        SS: Ctor<S>,
        // returns null on error
        checkStrucural: (s: S, preGamma: Gamma, onErr: (msg: string) => void, 
            scopeStack: ScopeStackItem[]) => 
                { info: StructuralInfo
                , postGamma: Gamma },
        // cannot fail
        wlp: (info: StructuralInfo, post: VerificationFormulaGradual, 
            scopeStack: ScopeStackItem[]) => 
                VerificationFormulaGradual,
        // cannot fail
        checkImplication: (info: StructuralInfo) => 
                VerificationFormula,
        // cannot fail
        checkPost: (info: StructuralInfo, pre: VerificationFormulaGradual, 
            scopeStack: ScopeStackItem[]) => 
                VerificationFormulaGradual
        ): void
    {
        var y = StatementAlloc;
        var x: typeof y;
        this.ruleHandlers.push({
            name: rule,
            statementMatch: s => s instanceof SS,
            checkStrucural: checkStrucural,
            wlp: wlp,
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
    public checkMethod(g: Gamma, s: Statement[], pre: VerificationFormulaGradual, post: VerificationFormulaGradual): string
    {
        var scopePostProcStack: ScopeStackItem[] = [];
        s = s.slice();
        s.push(new StatementCast(post));
        for (var ss of s)
        {
            var err = this.check(ss, pre, g, scopePostProcStack);
            if (err != null)
                return ss + " failed check: " + err.join(", ");
            var res = this.post(ss, pre, g, scopePostProcStack);
            pre = res.post;
            g = res.postGamma;
        }
        if (scopePostProcStack.length != 0)
            return "scopes not closed";
        return null;
    }
    public check(s: Statement, pre: VerificationFormulaGradual, g: Gamma, scopePostProcStack: ScopeStackItem[]): string[]
    {
        for (var scopeItem of scopePostProcStack)
        {
            var err = scopeItem.checkInnerStmt(s);
            if (err != null)
                return [err];
        }

        var rule = this.getRule(s);

        var errs: string[] = [];
        var res = rule.checkStrucural(s, g, msg => errs.push(msg), scopePostProcStack);
        if (res == null) 
            return errs;

        var dyn = rule.checkImplication(res.info);
        var prex = pre.implies(dyn);
        if (prex == null)
            return ["could not prove: " + dyn];

        return null;
    }
    public post(s: Statement, pre: VerificationFormulaGradual, g: Gamma, scopePostProcStack: ScopeStackItem[]): { post: VerificationFormulaGradual, dyn: VerificationFormula, postGamma: Gamma }
    {
        var rule = this.getRule(s);

        var errs: string[] = [];
        var res = rule.checkStrucural(s, g, msg => errs.push(msg), scopePostProcStack);
        if (res == null) 
            throw "call check first";

        var dyn = rule.checkImplication(res.info);
        pre = pre.implies(dyn);
        if (pre == null)
            throw "call check first";

        return {
            post: rule.checkPost(res.info, pre, scopePostProcStack),
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
            (info, post) => {
                // cannot say that target is null
                if (!post.append(new FormulaPartNeq(info.ex, Expression.getNull())).satisfiable())
                    return null;
                // cannot say anything about a field (TODO: not perfect! doesn't prevent (in)equalities with other vars)
                for (var f of info.fs)
                    if (!post.append(new FormulaPartEq(new ExpressionDot(info.ex, f.name), Expression.getNull())).satisfiable())
                        return null;
                    if (!post.append(new FormulaPartEq(new ExpressionDot(info.ex, f.name), Expression.getZero())).satisfiable())
                        return null;

                return post.woVar(info.ex.x);
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
            (info, post) => {
                // cannot say anything but ...
                if (!post.append(new FormulaPartEq(new ExpressionDot(info.ex, info.f), info.ey)).satisfiable())
                    return null;

                return post.woAcc(info.ex, info.f).append(new FormulaPartAcc(info.ex, info.f));
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
            (info, post) => {
                // cannot say anything but ...
                if (!post.append(new FormulaPartEq(info.ex, info.e)).satisfiable())
                    return null;

                post = post.woVar(info.ex.x);
                for (var frm of info.e.necessaryFraming().map(x => new FormulaPartAcc(x.e, x.f)))
                    if (!post.implies(frm.asFormula()))
                        post = post.append(frm);
                return post;
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
            (info, post) => {
                // cannot say anything but ...
                if (!post.append(new FormulaPartEq(info.ex, info.er)).satisfiable())
                    return null;

                return post.woVar(Expression.getResult());
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
                onErr(ey + " not declared (as class type)");
                return null;
            },
            (info, post) => {
                // cannot say anything but ...
                // TODO

                return post.woVar(info.x);
            },
            (info) => info.pre.append(info.ynn).staticFormula,
            (info, pre) => {
                pre = pre.woVar(info.x);
                if (info.pre.gradual)
                    for (var fp1 of pre.staticFormula.autoFraming())
                        pre = pre.woAcc(fp1.e, fp1.f);
                else
                    for (var fp2 of info.pre.staticFormula.footprintStatic())
                        pre = pre.woAcc(fp2.e, fp2.f);
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
            (info, post) => {
                return VerificationFormulaGradual.infimum(post, VerificationFormulaGradual.create(true, info));
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
            (info, post) => {
                // cannot say anything but ...
                var removed = info.footprintStatic();
                if (removed.map(acc => post.implies(new FormulaPartAcc(acc.e, acc.f).asFormula())).some(nec => nec != null && nec.norm().staticFormula.isEmpty()))
                    return null;

                return VerificationFormulaGradual.infimum(post, VerificationFormulaGradual.create(true, info));
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
            (info, post) => {
                // cannot say anything but ...
                if (!post.append(new FormulaPartEq(info.ex, info.T.defaultValue())).satisfiable())
                    return null;

                return post.woVar(info.ex.x);
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
            (info, post) => {
                if (!post.satisfiable())
                    return null;
                if (info.implies(post.staticFormula) == null)
                    return null;

                return VerificationFormulaGradual.create(info.gradual, VerificationFormula.empty());
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
            (info, post) => {
                return post;
            },
            (info) => VerificationFormula.empty(),
            (info, pre) => {
                return pre;
            });
        this.addHandler<StatementHold, { phi: VerificationFormula, gamma: Gamma }>("Hold", StatementHold,
            (s, g, onErr) => {
                if (!s.p.sfrm())
                {
                    onErr("framed-off formula must be self-framed");
                    return null;
                }
                return {
                    info: { phi: s.p, gamma: g },
                    postGamma: g
                };
            },
            (info, post) => {
                return post; // TODO
            },
            (info) => info.phi,
            (info, pre, postProcStack) => {
                var frameOff = pre;
                var readOnly = info.phi.FV();
                for (var fp of info.phi.footprintStatic())
                    pre = pre.woAcc(fp.e, fp.f);
                for (var fp2 of pre.staticFormula.autoFraming())
                    frameOff = frameOff.woAcc(fp2.e, fp2.f);
                for (var fv of frameOff.staticFormula.FV())
                    if (readOnly.indexOf(fv) == -1)
                        frameOff = frameOff.woVar(fv);
                
                postProcStack.push({ 
                    postProc: post => {
                        for (var part of frameOff.staticFormula.parts)
                            post = post.append(part);
                        return post;
                    },
                    checkInnerStmt: s => {
                        if (readOnly.some(x => s.writesTo(x)))
                            return "writes to protected variable";
                        return null;
                    },
                    gamma: info.gamma
                });
                
                return pre;
            });
        this.addHandler<StatementUnhold, { }>("Unhold", StatementUnhold,
            (s, g, onErr, postProcStack) => {
                if (postProcStack.length == 0)
                {
                    onErr("no scope to close");
                    return null;
                }

                return {
                    info: { },
                    postGamma: postProcStack[postProcStack.length - 1].gamma
                };
            },
            (info, post) => {
                return post; // TODO
            },
            (info) => VerificationFormula.empty(),
            (info, pre, postProcStack) => {
                var proc = postProcStack.pop();
                return proc.postProc(pre);
            });
    }

}