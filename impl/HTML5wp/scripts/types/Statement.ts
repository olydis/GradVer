import { VerificationFormula } from "./VerificationFormula";
import { VerificationFormulaGradual } from "./VerificationFormulaGradual";
import { Type } from "./Type";
import { Expression, ExpressionX } from "./Expression";
import { StackEnv, cloneStackEnv, topEnv } from "../runtime/StackEnv";
import { ExecutionEnvironment } from "../runtime/ExecutionEnvironment";
import { Rho } from "../runtime/EvalEnv";
import { ValueObject } from "./ValueExpression";

export abstract class Statement
{
    abstract toString(): string;
    public abstract smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv;

    public writesTo(x: string): boolean
    {
        return false;
    }

    public static parse(source: string): Statement
    {
        var fallBack = new StatementComment(source.trim() == "" 
            ? " write a statement here" 
            : " parse error: " + source);
        var result: Statement = null;
        source = source.replace(/;$/, "");
        var sourceWS = source;
        try
        {
            if (!result) result = StatementHold.parse(source);
            if (!result) result = StatementUnhold.parse(source);

            if (!result) result = StatementComment.parse(source);
            if (!result) result = StatementCast.parse(source);
            source = source.replace(/\s/g, "");
            if (!result) result = StatementCall.parse(source);
            if (!result) result = StatementAlloc.parse(source);
            if (!result) result = StatementAssert.parse(source);
            if (!result) result = StatementRelease.parse(source);
            if (!result) result = StatementReturn.parse(source);
            if (!result) result = StatementMemberSet.parse(source);
            if (!result) result = StatementAssign.parse(source);
            if (!result) result = StatementDeclare.parse(sourceWS);
            if (!result) result = fallBack;
        }
        catch(e)
        {
            console.error("parse error");
            result = fallBack;
        }
        return result;
    }
}

export class StatementMemberSet extends Statement
{
    public constructor(
        public x: string,
        public f: string,
        public y: string)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
        if (!Expression.isValidX(f)) throw "null arg";
        if (!Expression.isValidX(y)) throw "null arg";
    }

    public static parse(source: string): Statement
    {
        var eqIndex = source.indexOf(":=");
        if (eqIndex == -1) eqIndex = source.indexOf("=");
        if (eqIndex == -1) return null;

        var a = source.substr(0, eqIndex);
        var b = source.substr(eqIndex + 1).replace(/=/g, "");

        var dotIndex = a.lastIndexOf(".");
        if (dotIndex == -1)
            return null;
        var x = a.substr(0, dotIndex);
        var f = a.substr(dotIndex + 1);

        return new StatementMemberSet(x, f, b);
    }

    public toString(): string
    {
        return this.x + "." + this.f + " := " + this.y + ";";
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        var envx = topEnv(env);
        env = cloneStackEnv(env);
        if (env.S[env.S.length - 1].ss.shift() != this)
            throw "dispatch failure";

        var o = new ExpressionX(this.x).eval(envx);
        if (o instanceof ValueObject)
        {
            if (!envx.A.some(a => a.o == (o as ValueObject).UID && a.f == this.f))
                return null;

            var v = new ExpressionX(this.y).eval(envx);
            if (v == null)
                return null;

            var Hentry = env.H[o.UID];
            if (Hentry == null || Hentry.fs == null)
                return null;

            Hentry.fs[this.f] = v;
            return env;
        }
        return null;
    }
}

export class StatementAssign extends Statement
{
    public constructor(
        public x: string,
        public e: Expression)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
        if (e == null) throw "null arg";
    }
    public writesTo(x: string): boolean
    {
        return this.x == x;
    }

    public static parse(source: string): Statement
    {
        var eqIndex = source.indexOf(":=");
        if (eqIndex == -1) eqIndex = source.indexOf("=");
        if (eqIndex == -1) return null;

        var a = source.substr(0, eqIndex);
        var b = source.substr(eqIndex + 1).replace(/=/g, "");

        var e = Expression.parse(b);

        return e != null
            ? new StatementAssign(a, e)
            : null;
    }

    public toString(): string
    {
        return this.x + " := " + this.e.toString() + ";";
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        var envx = topEnv(env);
        env = cloneStackEnv(env);
        if (env.S[env.S.length - 1].ss.shift() != this)
            throw "dispatch failure";

        var v = this.e.eval(envx);
        if (v == null)
            return null;

        var topIdx = env.S.length - 1;
        env.S[topIdx].r[this.x] = v;
        return env;
    }
}

export class StatementAlloc extends Statement
{
    public constructor(
        public x: string,
        public C: string)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
        if (!Expression.isValidX(C)) throw "null arg";
    }
    public writesTo(x: string): boolean
    {
        return this.x == x;
    }

    public static parse(source: string): Statement
    {
        var eqIndex = source.indexOf(":=");
        if (eqIndex == -1) eqIndex = source.indexOf("=");
        if (eqIndex == -1) return null;

        var a = source.substr(0, eqIndex);
        var b = source.substr(eqIndex + 1).replace(/=/g, "");
        if (b.substr(0, 3) != "new")
            return null;
        b = b.substr(3);

        return new StatementAlloc(a, b);
    }

    public toString(): string
    {
        return this.x + " := new " + this.C + ";";
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        var envx = topEnv(env);
        env = cloneStackEnv(env);
        if (env.S[env.S.length - 1].ss.shift() != this)
            throw "dispatch failure";

        // find first free object
        var o = 0;
        while (envx.H[o] != null)
            o++;
        var vo = new ValueObject(o);

        var fs = context.fields(this.C);
        if (fs == null)
            return null;

        var topIdx = env.S.length - 1;
        env.H[o] = { C: this.C, fs: { } };

        env.S[topIdx].r[this.x] = vo;
        for (var f of fs)
        {
            env.H[o].fs[f.name] = f.type.defaultValue().eval(envx);
            env.S[topIdx].A.push({ o: o, f: f.name });
        }
        return env;
    }
}

export class StatementCall extends Statement
{
    public constructor(
        public x: string,
        public y: string,
        public m: string,
        public z: string[])
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
        if (!Expression.isValidX(y)) throw "null arg";
        if (!Expression.isValidX(m)) throw "null arg";
        if (z.some(z => !Expression.isValidX(z))) throw "null arg";
    }
    public writesTo(x: string): boolean
    {
        return this.x == x;
    }

    public static parse(source: string): Statement
    {
        var eqIndex = source.indexOf(":=");
        if (eqIndex == -1) eqIndex = source.indexOf("=");
        if (eqIndex == -1) return null;

        var x = source.substr(0, eqIndex);
        var b = source.substr(eqIndex + 1).replace(/=/g, "");

        var dotIndex = b.lastIndexOf(".");
        if (dotIndex == -1)
            return null;
        var y = b.substr(0, dotIndex);
        var call = b.substr(dotIndex + 1);
        var braceIndex = call.indexOf("(");
        if (braceIndex == -1)
            return null;
        var m = call.substr(0, braceIndex);
        var z = call.substr(braceIndex + 1).replace(")", "");

        return new StatementCall(x, y, m, z.split(",").filter(z => z));
    }

    public toString(): string
    {
        return this.x + " := " + this.y + "." + this.m + "(" + this.z.join(", ") + ");";
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        var envx = topEnv(env);
        env = cloneStackEnv(env);

        var isEntry = env.S[env.S.length - 1].ss.length != 0;
        if (!isEntry)
            env.S.pop();

        var vo = new ExpressionX(this.y).eval(topEnv(env));
        if (vo instanceof ValueObject)
        {
            var o = vo.UID;

            var Hentry = envx.H[o];
            if (Hentry == null)
                return null;

            var m = context.mmethod(Hentry.C, this.m);
            if (m == null || m.name != this.m)
                return null;

            if (isEntry)
            { // ESApp
                if (env.S[env.S.length - 1].ss[0] != this)
                    throw "dispatch failure";


                var rr: Rho = {};
                rr[Expression.getResult()] = m.retType.defaultValue().eval(envx);
                rr[Expression.getThis()] = vo;
                for (let i = 0; i < Math.min(); ++i) {
                    var v = new ExpressionX(this.z[i]).eval(envx);
                    if (v == null)
                        return null;
                    rr[m.args[i].name] = v;
                }

                if (!m.frmPre.eval({ H: envx.H, r: rr, A: envx.A }))
                    return null;

                var AA = m.frmPre.gradual ? envx.A : m.frmPre.staticFormula.footprintDynamic({ H: envx.H, r: rr, A: envx.A });
                var topIdx = env.S.length - 1;
                env.S[topIdx].A = env.S[topIdx].A.filter(a => !AA.some(b => a.f == b.f && a.o == b.o));
                env.S.push({
                    r: rr,
                    A: AA,
                    ss: m.body
                });
            }
            else
            { // ESAppFinish
                if (env.S[env.S.length - 1].ss.shift() != this)
                    throw "dispatch failure";

                if (!m.frmPost.eval(envx))
                    return null;

                var vr = new ExpressionX(Expression.getResult()).eval(envx);
                if (vr == null)
                    return null;

                var topIdx = env.S.length - 1;
                env.S[topIdx].r[this.x] = vr;
                env.S[topIdx].A.push(...envx.A);
            }

            return env;
        }
        else
            return null;
    }
}

export class StatementReturn extends Statement
{
    public constructor(public x: string) 
    { 
        super(); 
        if (!Expression.isValidX(x)) throw "null arg";
    }
    public writesTo(x: string): boolean
    {
        return Expression.getResult() == x;
    }

    public static parse(source: string): Statement
    {
        if (source.substr(0, 6) != "return")
            return null;
        return new StatementReturn(source.substr(6));
    }

    public toString(): string
    {
        return "return " + this.x + ";";
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        var envx = topEnv(env);
        env = cloneStackEnv(env);
        if (env.S[env.S.length - 1].ss.shift() != this)
            throw "dispatch failure";

        var v = new ExpressionX(this.x).eval(envx);
        if (v == null)
            return null;

        var topIdx = env.S.length - 1;
        env.S[topIdx].r[Expression.getResult()] = v;
        return env;
    }
}

export class StatementAssert extends Statement
{
    public constructor(public assertion: VerificationFormula) { super(); }

    public static parse(source: string): Statement
    {
        if (source.substr(0, 6) != "assert")
            return null;
        return new StatementAssert(new VerificationFormula(source.substr(6)));
    }

    public toString(): string
    {
        return "assert " + this.assertion.toString() + ";";
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        var envx = topEnv(env);
        env = cloneStackEnv(env);
        if (env.S[env.S.length - 1].ss.shift() != this)
            throw "dispatch failure";

        if (!this.assertion.eval(envx))
            return null;

        return env;
    }
}

export class StatementRelease extends Statement
{
    public constructor(public assertion: VerificationFormula) { super(); }

    public static parse(source: string): Statement
    {
        if (source.substr(0, 7) != "release")
            return null;
        return new StatementRelease(new VerificationFormula(source.substr(7)));
    }

    public toString(): string
    {
        return "release " + this.assertion.toString() + ";";
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        var envx = topEnv(env);
        env = cloneStackEnv(env);
        if (env.S[env.S.length - 1].ss.shift() != this)
            throw "dispatch failure";

        if (!this.assertion.eval(envx))
            return null;

        var AA = this.assertion.footprintDynamic(envx);
        var topIdx = env.S.length - 1;
        env.S[topIdx].A = env.S[topIdx].A.filter(a => !AA.some(b => a.f == b.f && a.o == b.o));
        return env;
    }
}

export class StatementDeclare extends Statement
{
    public constructor(
        public T: Type,
        public x: string)
    {
        super();
        if (!Expression.isValidX(x)) throw "null arg";
    }
    public writesTo(x: string): boolean
    {
        return this.x == x;
    }

    public static parse(source: string): Statement
    {
        var srcParts = source.trim().split(" ");
        if (srcParts.length != 2) return null;
        var T = Type.parse(srcParts[0]);
        if (T == null) return null;
        return new StatementDeclare(T, srcParts[1]);
    }

    public toString(): string
    {
        return this.T.toString() + " " + this.x + ";";
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        var envx = topEnv(env);
        env = cloneStackEnv(env);
        if (env.S[env.S.length - 1].ss.shift() != this)
            throw "dispatch failure";

        var topIdx = env.S.length - 1;
        env.S[topIdx].r[this.x] = this.T.defaultValue().eval(envx);
        return env;
    }
}

// EXTENSIONS

export class StatementCast extends Statement
{
    public constructor(
        public T: VerificationFormulaGradual)
    {
        super();
    }

    public static parse(source: string): Statement
    {
        source = source.trim();
        if (source.charAt(0) != '{')
            return null;
        if (source.charAt(source.length - 1) != '}')
            return null;
        source = source.slice(1, source.length - 1);
        return new StatementCast(new VerificationFormulaGradual(source));
    }

    public toString(): string
    {
        return "{ " + this.T.toString() + " }";
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        env = cloneStackEnv(env);
        if (env.S[env.S.length - 1].ss.shift() != this)
            throw "dispatch failure";

        return env;
    }
}

export class StatementComment extends Statement
{
    public constructor(
        public comment: string)
    {
        super();
    }

    public static parse(source: string): Statement
    {
        source = source.trim();
        if (source.charAt(0) != '/')
            return null;
        if (source.charAt(1) != '/')
            return null;
        source = source.slice(2);
        return new StatementComment(source);
    }

    public toString(): string
    {
        return "//" + this.comment;
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        env = cloneStackEnv(env);
        if (env.S[env.S.length - 1].ss.shift() != this)
            throw "dispatch failure";

        return env;
    }
}

export class StatementHold extends Statement
{
    public constructor(
        public p: VerificationFormula)
    {
        super();
        if (p == null) throw "null arg";
    }

    public static parse(source: string): Statement
    {
        if (source.slice(0,4) != "hold")
            return null;
        source = source.slice(4);
        if (source.charAt(source.length - 1) == "{")
            source = source.slice(0, source.length - 1);
        return new StatementHold(new VerificationFormula(source));
    }

    public toString(): string
    {
        return "hold " + this.p + " {";
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        var envx = topEnv(env);
        env = cloneStackEnv(env);

        var isEntry = env.S[env.S.length - 1].ss.length != 0;
        if (!isEntry)
            env.S.pop();

        if (isEntry)
        { 
            // ESHold
            if (env.S[env.S.length - 1].ss[0] != this)
                throw "dispatch failure";

            if (!this.p.eval(envx))
                return null;

            var AA = this.p.footprintDynamic(envx);
            var topIdx = env.S.length - 1;
            var Awo = env.S[topIdx].A.filter(a => !AA.some(b => a.f == b.f && a.o == b.o))
            env.S[topIdx].A = AA;
            env.S.push({
                r: envx.r,
                A: Awo,
                ss: env.S[topIdx].ss.slice(1)
            });
        }
        else
        {
            // exit handled by closing curly... so scope not closed if we get here
            return null;
        }

        return env;
    }
}
export class StatementUnhold extends Statement
{
    public constructor()
    {
        super();
    }

    public static parse(source: string): Statement
    {
        if (source != "}")
            return null;
        return new StatementUnhold();
    }

    public toString(): string
    {
        return "}";
    }
    public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
    {
        var envx = topEnv(env);
        env = cloneStackEnv(env);

        // ESHoldFinish
        if (env.S.pop().ss.shift() != this)
            throw "dispatch failure";

        // reset next stack frame
        var ss = env.S[env.S.length - 1].ss;
        var entryStmt = ss[0];
        ss = ss.slice(ss.indexOf(this) + 1);
        env.S[env.S.length - 1].ss = ss;

        // update env
        var topIdx = env.S.length - 1;
        env.S[topIdx].A.push(...envx.A);
        env.S[topIdx].r = envx.r;

        return env;
    }
}

// export class StatementSugar extends Statement
// {
//     public constructor(
//         public children: Statement[])
//     {
//         super();
//     }

//     public static parse(source: string): Statement
//     {
//         source = source.trim();
//         if (source.charAt(0) != '/')
//             return null;
//         if (source.charAt(1) != '/')
//             return null;
//         source = source.slice(2);
//         return new StatementComment(source);
//     }

//     public toString(): string
//     {
//         return "";
//     }
//     public smallStep(env: StackEnv, context: ExecutionEnvironment): StackEnv
//     {
//         env = cloneStackEnv(env);
//         if (env.S[env.S.length - 1].ss.shift() != this)
//             throw "dispatch failure";

//         return env;
//     }
// }