// import { VerificationFormula, FormulaPart, FormulaPartAcc, FormulaPartNeq, FormulaPartEq } from "../types/VerificationFormula";
// import { VerificationFormulaGradual } from "../types/VerificationFormulaGradual"
// import { Statement,
//     StatementAlloc,
//     StatementMemberSet,
//     StatementAssign,
//     StatementReturn,
//     StatementCall,
//     StatementAssert,
//     StatementRelease,
//     StatementDeclare
//     } from "../types/Statement";
// import { Type, TypeClass } from "../types/Type";
// import { ExpressionX, Expression, ExpressionDot, ExpressionV } from "../types/Expression";
// import { ExecutionEnvironment } from "./ExecutionEnvironment";
// import { Field, Method } from "./Program";
// type Ctor<T> = { new(... args: any[]): T };
// type Rule = {
//         name: string,
//         statementMatch: (s: Statement) => boolean,
//         params: (s: Statement, pre: VerificationFormulaGradual, onErr: (msg: string) => void) => any,
//         notInPhi: (s: Statement) => string[],
//         pre: (s: Statement, phi: VerificationFormula, params: any) => VerificationFormula,
//         post: (s: Statement, phi: VerificationFormula, params: any) => VerificationFormula,
//     };
// export class Hoare
// {
//     private ruleHandlers: Rule[];
//     private addHandler<S extends Statement, P>(
//         rule: string,
//         SS: Ctor<S>,
//         getParams: (s: S, pre: VerificationFormulaGradual, onErr: (msg: string) => void) => P,
//         notInPhi: (s: S) => string[],
//         getPre: (s: S, phi: VerificationFormula, params: P) => VerificationFormula,
//         getPost: (s: S, phi: VerificationFormula, params: P) => VerificationFormula): void
//     {
//         var y = StatementAlloc;
//         var x: typeof y;
//         this.ruleHandlers.push({
//             name: rule,
//             statementMatch: s => s instanceof SS,
//             params: getParams, // check
//             notInPhi: notInPhi,
//             pre: getPre,
//             post: getPost
//         });
//     }
//     private getRule(s: Statement): Rule
//     {
//         for (var rule of this.ruleHandlers)
//             if (rule.statementMatch(s))
//                 return rule;
//         throw "unknown statement type";
//     }
//     public check(s: Statement, pre: VerificationFormulaGradual): string[]
//     {
//         var rule = this.getRule(s);
//         var errs: string[] = [];
//         var res = rule.params(s, pre, msg => errs.push(msg));
//         return res == null ? errs : null;
//     }
//     private guessPhiFromPre(s: Statement, pre: VerificationFormulaGradual): VerificationFormula
//     {
//         var rule = this.getRule(s);
//         var params = rule.params(s, pre, () => {});
//         var barePre = rule.pre(s, VerificationFormula.empty(), params);
//         var nonos = rule.notInPhi(s);
//         var isNono = (x : string) => nonos.indexOf(x) != -1;
//         var remaining = pre.staticFormula.parts.filter(p1 => !(
//             p1 instanceof FormulaPartAcc &&
//             barePre.parts.some(p2 => FormulaPart.eq(p1, p2))));
//         remaining = remaining.filter(p => p.FV().every(x => !isNono(x)));
//         return new VerificationFormula(null, remaining);
//     }
//     private guessPhiFromPost(s: Statement, pre: VerificationFormulaGradual, post: VerificationFormulaGradual): VerificationFormula
//     {
//         var rule = this.getRule(s);
//         var params = rule.params(s, pre, () => {});
//         var barePost = rule.post(s, VerificationFormula.empty(), params);
//         var nonos = rule.notInPhi(s);
//         var isNono = (x : string) => nonos.indexOf(x) != -1;
//         var remaining = post.staticFormula.parts.filter(p1 => !(
//             barePost.parts.some(p2 => FormulaPart.eq(p1, p2))));
//         remaining = remaining.filter(p => p.FV().every(x => !isNono(x)));
//         return new VerificationFormula(null, remaining);
//     }
//     public guessPhi(s: Statement, pre: VerificationFormulaGradual, post: VerificationFormulaGradual): VerificationFormula
//     {
//         var phiPre = this.guessPhiFromPre(s, pre);
//         var phiPost = this.guessPhiFromPost(s, pre, post);
//         return VerificationFormula.intersect(phiPre, phiPost);
//     }
//     public genPost(s: Statement, pre: VerificationFormulaGradual, post: VerificationFormulaGradual): VerificationFormulaGradual
//     {
//         var rule = this.getRule(s);
//         var params = rule.params(s, pre, () => {});
//         if (params == null)
//             return VerificationFormulaGradual.create(pre.gradual, VerificationFormula.empty());
//         var phi = this.guessPhi(s, pre, post);
//         return VerificationFormulaGradual.create(pre.gradual, rule.post(s, phi, params));
//     }
//     public genPre(s: Statement, pre: VerificationFormulaGradual, post: VerificationFormulaGradual): VerificationFormulaGradual
//     {
//         var rule = this.getRule(s);
//         var params = rule.params(s, pre, () => {});
//         if (params == null)
//             return VerificationFormulaGradual.create(post.gradual, VerificationFormula.empty());
//         var phi = this.guessPhi(s, pre, post);
//         return VerificationFormulaGradual.create(post.gradual, rule.pre(s, phi, params));
//     }
//     // public validate(s: Statement, pre: VerificationFormulaGradual, post: VerificationFormulaGradual): { errs: string[], runtimeCheck: VerificationFormula }
//     // {
//     //     var check = this.check(s, pre);
//     //     if (check) return { errs: check, runtimeCheck: VerificationFormula.empty() };
//     //     var rule = this.getRule(s);
//     //     var params = rule.params(s, pre, () => {});
//     //     var phi = this.guessPhiFromPost(s, pre, post);
//     //     var xpre = rule.pre(s, phi, params);
//     //     var xpost = rule.post(s, phi, params);
//     //     if (!pre.impliesApprox(xpre))
//     //         return { errs: ["couldn't prove pre implication"], runtimeCheck: VerificationFormula.empty() };
//     //     if (!post.containsApprox(xpost))
//     //         return { errs: ["couldn't prove post membership"], runtimeCheck: VerificationFormula.empty() };
//     //     return { errs: null, runtimeCheck: pre.impliesApproxMissing(xpre) };
//     // }
//     constructor(private env: ExecutionEnvironment) {
//         this.ruleHandlers = [];
//         this.addHandler<StatementAlloc, { fs: Field[] }>("NewObject", StatementAlloc,
//             (s, pre, onErr) => {
//                 var fs = this.env.fields(s.C);
//                 // check
//                 if (fs == null)
//                 {
//                     onErr("class '" + s.C + "' not found");
//                     return null;
//                 }
//                 return {fs: fs};
//             },
//             s => [s.x],
//             (s, phi, params) => {
//                 var res: FormulaPart[] = [];
//                 res.push(new FormulaPartType(s.x, new TypeClass(s.C)));
//                 res.push(...phi.parts);
//                 return new VerificationFormula(null, res);
//             },
//             (s, phi, params) => {
//                 var ex = new ExpressionX(s.x);
//                 var res: FormulaPart[] = [];
//                 res.push(...params.fs.map(f => new FormulaPartAcc(ex, f.name)));
//                 res.push(new FormulaPartType(s.x, new TypeClass(s.C)));
//                 res.push(new FormulaPartNeq(ex, ExpressionX.getNull()));
//                 res.push(...phi.parts);
//                 return new VerificationFormula(null, res);
//             });
//         this.addHandler<StatementMemberSet, {C: TypeClass, T: Type}>("FieldAssign", StatementMemberSet,
//             (s, pre, onErr) => {
//                 var Tx = pre.staticFormula.tryGetType(s.x);
//                 if (!(Tx instanceof TypeClass))
//                 {
//                     if (pre.gradual) return { C: null, T: null };
//                     onErr("couldn't determine type of '" + s.x + "'");
//                     return null;
//                 }
//                 var Cx = <TypeClass>Tx;
//                 var Cf = this.env.fieldType(Cx.C, s.f);
//                 // check
//                 if (Cf == null)
//                 {
//                     onErr("class '" + Cx + "' doesn't have field '" + s.f + "'");
//                     return null;
//                 }
//                 return {C: Cx, T: Cf};
//             },
//             s => [],
//             (s, phi, params) => {
//                 var ex = new ExpressionX(s.x);
//                 var res: FormulaPart[] = [];
//                 if (params.C)
//                     res.push(new FormulaPartType(s.x, params.C));
//                 if (params.T)
//                     res.push(new FormulaPartType(s.y, params.T));
//                 res.push(...phi.parts);
//                 res.push(new FormulaPartAcc(ex, s.f));
//                 return new VerificationFormula(null, res);
//             },
//             (s, phi, params) => {
//                 var ex = new ExpressionX(s.x);
//                 var res: FormulaPart[] = [];
//                 if (params.C)
//                     res.push(new FormulaPartType(s.x, params.C));
//                 res.push(new FormulaPartAcc(ex, s.f));
//                 res.push(new FormulaPartEq(new ExpressionDot(ex, s.f), new ExpressionX(s.y)));
//                 res.push(...phi.parts);
//                 return new VerificationFormula(null, res);
//             });
//         this.addHandler<StatementAssign, {T: Type, Tx: Type}>("VarAssign", StatementAssign,
//             (s, pre, onErr) => {
//                 var Tx = pre.staticFormula.tryGetType(s.x);
//                 if (Tx == null)
//                 {
//                     if (pre.gradual) return { T: null, Tx: null };
//                     onErr("couldn't determine type of '" + s.x + "'");
//                     return null;
//                 }
//                 var Te = this.env.tryGetType(pre.staticFormula, s.e);
//                 if (Te == null)
//                 {
//                     if (pre.gradual) return { T: null, Tx: null };
//                     onErr("couldn't determine type of RHS expression");
//                     return null;
//                 }
//                 var TeCore = this.env.tryGetCoreType(pre.staticFormula, s.e);
//                 // check
//                 if (s.e.FV().some(x => x == s.x))
//                 {
//                     onErr("RHS expression cannot contain variable '" + s.x + "'");
//                     return null;
//                 }
//                 if (!Type.eq(Tx, Te))
//                 {
//                     onErr("type mismatch");
//                     return null;
//                 }
//                 return {T:Te, Tx: TeCore};
//             },
//             s => [s.x],
//             (s, phi, params) => {
//                 var ex = new ExpressionX(s.x);
//                 var res: FormulaPart[] = [];
//                 if (params.T)
//                     res.push(new FormulaPartType(s.x, params.T));
//                 if (params.Tx)
//                     res.push(...this.unfoldTypeFormula(s.e, params.Tx));
//                 res.push(...phi.parts);
//                 return new VerificationFormula(null, res);
//             },
//             (s, phi, params) => {
//                 var ex = new ExpressionX(s.x);
//                 var res: FormulaPart[] = [];
//                 if (params.Tx)
//                     res.push(...this.unfoldTypeFormula(s.e, params.Tx));
//                 res.push(...phi.parts);
//                 res.push(new FormulaPartEq(ex, s.e));
//                 return new VerificationFormula(null, res);
//             });
//         this.addHandler<StatementReturn, {T: Type}>("Return", StatementReturn,
//             (s, pre, onErr) => {
//                 var Tx = pre.staticFormula.tryGetType(s.x);
//                 if (Tx == null)
//                 {
//                     if (pre.gradual) return {T: null};
//                     onErr("couldn't determine type of '" + s.x + "'");
//                     return null;
//                 }
//                 return {T:Tx};
//             },
//             s => [Expression.getResult()],
//             (s, phi, params) => {
//                 var ex = new ExpressionX(s.x);
//                 var res: FormulaPart[] = [];
//                 if (params.T)
//                     res.push(new FormulaPartType(s.x, params.T));
//                 res.push(new FormulaPartType(Expression.getResult(), params.T));
//                 res.push(...phi.parts);
//                 return new VerificationFormula(null, res);
//             },
//             (s, phi, params) => {
//                 var ex = new ExpressionX(s.x);
//                 var res: FormulaPart[] = [];
//                 if (params.T)
//                     res.push(new FormulaPartType(Expression.getResult(), params.T));
//                 res.push(new FormulaPartEq(new ExpressionX(Expression.getResult()), ex));
//                 res.push(...phi.parts);
//                 return new VerificationFormula(null, res);
//             });
//         this.addHandler<StatementCall, {m: Method, C: TypeClass}>("Call", StatementCall,
//             (s, pre, onErr) => {
//                 var Ty = pre.staticFormula.tryGetType(s.y);
//                 if (!(Ty instanceof TypeClass))
//                 {
//                     if (pre.gradual) return {m: null, C: null};
//                     onErr("'" + s.y + "' must have class type");
//                     return null;
//                 }
//                 var Cy = <TypeClass>Ty;
//                 var m = this.env.mmethod(Cy.C, s.m);
//                 // check
//                 if (m == null)
//                 {
//                     onErr("class '" + Cy + "' doesn't have method '" + s.m + "'");
//                     return null;
//                 }
//                 if (s.x == s.y || s.x == s.z)
//                 {
//                     onErr("'" + s.x + "' cannot appear both in LHS and RHS");
//                     return null;
//                 }
//                 return {m: m, C: Cy};
//             },
//             s => [s.x],
//             (s, phi, params) => {
//                 var ex = new ExpressionX(s.x);
//                 var res: FormulaPart[] = [];
//                 if (params.m)
//                     res.push(new FormulaPartType(s.x, params.m.retType));
//                 if (params.C)
//                     res.push(new FormulaPartType(s.y, params.C));
//                 if (params.m)
//                     res.push(new FormulaPartType(s.z, params.m.argType));
//                 res.push(...phi.parts);
//                 res.push(new FormulaPartNeq(new ExpressionX(s.y), Expression.getNull()));
//                 if (params.m)
//                     res.push(...params.m.frmPre.staticFormula.substs(x =>
//                     {
//                         if (x == Expression.getThis()) return s.y;
//                         if (x == params.m.argName) return s.z;
//                         return x;
//                     }).parts);
//                 return new VerificationFormula(null, res);
//             },
//             (s, phi, params) => {
//                 var ex = new ExpressionX(s.x);
//                 var res: FormulaPart[] = [];
//                 res.push(...phi.parts);
//                 if (params.m)
//                     res.push(...params.m.frmPre.staticFormula.substs(x =>
//                     {
//                         if (x == Expression.getThis()) return s.y;
//                         if (x == params.m.argName) return s.z;
//                         if (x == Expression.getResult()) return s.x;
//                         return x;
//                     }).parts);
//                 return new VerificationFormula(null, res);
//             });
//         this.addHandler<StatementAssert, {}>("Assert", StatementAssert,
//             (s, pre, onErr) => {
//                 if (!pre.impliesApprox(s.assertion))
//                 {
//                     onErr("couldn't prove assertion");
//                     return null;
//                 }
//                 return {};
//             },
//             s => [],
//             (s, phi, params) => {
//                 return phi;
//             },
//             (s, phi, params) => {
//                 return phi;
//             });
//         this.addHandler<StatementRelease, {}>("Release", StatementRelease,
//             (s, pre, onErr) => {
//                 return {};
//             },
//             s => [],
//             (s, phi, params) => {
//                 return new VerificationFormula(null, phi.parts.concat(s.assertion.parts));
//             },
//             (s, phi, params) => {
//                 return phi;
//             });
//         this.addHandler<StatementDeclare, {}>("Declare", StatementDeclare,
//             (s, pre, onErr) => {
//                 return {};
//             },
//             s => [s.x],
//             (s, phi, params) => {
//                 return phi;
//             },
//             (s, phi, params) => {
//                 var res: FormulaPart[] = [];
//                 res.push(new FormulaPartType(s.x, s.T));
//                 res.push(new FormulaPartEq(new ExpressionX(s.x), s.T.defaultValue()));
//                 res.push(...phi.parts);
//                 return new VerificationFormula(null, res);
//             });
//     }
// } 
