import { Expression, ExpressionV, ExpressionX, ExpressionDot } from "../types/Expression";
import { Value, ValueExpression, ValueObject } from "../types/ValueExpression";
import { FootprintDynamic } from "../types/Footprint";
import { VerificationFormula,
        FormulaPart,
        FormulaPartAcc,
        FormulaPartEq,
        FormulaPartNeq } from "../types/VerificationFormula";

export type ValuePair = {v1: Value, v2: Value};

export type HeapEntryMap = { [f: string]: Value };
export type HeapEntry = { C: string | null, fs: HeapEntryMap };
export type Heap = { [o: number]: HeapEntry };
export type Rho = { [x: string]: Value };

export type EvalEnv = { H: Heap, r: Rho, A: FootprintDynamic };

function printHeapEntry(Hentry: {[f:string]: Value})
{
    var fs: string[] = Object.getOwnPropertyNames(Hentry);
    return "{" + fs.map(f => f + "=" + Hentry[f]).join(",") + "}";
}
function printHeap(H: Heap)
{
    var objs: number[] = Object.getOwnPropertyNames(H).map(so => parseInt(so));
    return "{" + objs.map(o => o + ":" + H[o].C + "=" + printHeapEntry(H[o].fs)).join(",") + "}";
}
function printRho(r: Rho)
{
    var vars: string[] = Object.getOwnPropertyNames(r);
    return "{" + vars.map(v => v + "=" + r[v]).join(",") + "}";
}
function printAccess(A: FootprintDynamic)
{
    return "{" + A.map(a => "(" + new ValueObject(a.o) + "." + a.f + ")").join(",") + "}";
}
export function printEnv(env: EvalEnv)
{
    return "(" +
        printHeap(env.H) +
        ", " + 
        printRho(env.r) +
        ", " + 
        printAccess(env.A) + 
    ")";
}

function cloneHeapEntry(He: HeapEntry): HeapEntry
{
    var res: HeapEntry = { C: He.C, fs: {} };
    for (var f in He.fs)
        res.fs[f] = He.fs[f];
    return res;
}
export function cloneHeap(H: Heap): Heap
{
    var res: Heap = {};
    for (var o in H)
        res[o] = cloneHeapEntry(H[o]);
    return res;
}
export function cloneRho(rho: Rho): Rho
{
    var res: Rho = {};
    for (var x in rho)
        res[x] = rho[x];
    return res;
}
export function cloneAccess(A: FootprintDynamic): FootprintDynamic
{
    var res: FootprintDynamic = [];
    for (var a of A)
        res.push({o: a.o, f: a.f});
    return res;
}
export function cloneEvalEnv(env: EvalEnv): EvalEnv
{
    return { H: cloneHeap(env.H)
           , r: cloneRho(env.r)
           , A: cloneAccess(env.A)};
}

export class NormalizedEnv {
    public static create(
        ineq: ValuePair[] = [],
        env: EvalEnv = { H: {}, r: {}, A: [] }): NormalizedEnv | null
    {
        var result = new NormalizedEnv(ineq, env);
        return result.getConsistent() ? result : null;
    }

    private static mergeObjHeapFields(fs1: HeapEntryMap, fs2: HeapEntryMap): ValuePair[]
    {
        var res: ValuePair[] = [];
        for (var f in fs1)
        {
            if (fs2[f])
                res.push({v1: fs1[f], v2: fs2[f]});
            fs2[f] = fs1[f];
        }
        return res;
    }
    private static mergeObjHeap(o: number, v: Value, H: Heap): { H: Heap, todo: ValuePair[] } | null
    {
        H = cloneHeap(H);
        var HEntry = H[o];
        if (!HEntry) return { H: H, todo: [] };
        if (v instanceof ValueObject)
        {
            var oo = v.UID;
            var todo: ValuePair[] = [];
            if (H[oo])
            {
                if (HEntry.C != H[oo].C) return null;
                todo = NormalizedEnv.mergeObjHeapFields(HEntry.fs, H[oo].fs);
            }
            else
                H[oo] = H[o];
            delete H[o];
            return {H:H, todo: todo};
        }
        return null;
    }
    private static mergeObjHeapC(vo: Value, v: Value, H: Heap): Heap
    {
        H = cloneHeap(H);
        for (var o in H)
        {
            var fs = H[o].fs;
            for (var f in fs)
                if (fs[f].equalTo(vo))
                    fs[f] = v;
        }
        return H;
    }
    private static mergeObjAccess(o: number, v: Value, A: FootprintDynamic): FootprintDynamic | null
    {
        if (v instanceof ValueObject)
            return A.map(a => {return { o: a.o == o ? v.UID : a.o, f: a.f }});
        return A.some(a => a.o == o)
            ? null
            : A;
    }
    private static mergeObjIneq(vo: Value, v: Value, ineq: ValuePair[]): ValuePair[]
    {
        return ineq.map(a => {return { 
            v1: a.v1 == vo ? v : a.v1, 
            v2: a.v2 == vo ? v : a.v2 }});
    }

    constructor(
        private ineq: ValuePair[] = [],
        private env: EvalEnv = { H: {}, r: {}, A: [] })
    { }

    private expressionDfs(e: Expression, seen: number[], todo: (e: Expression, v: Value) => void): void
    {
        var v = e.eval(this.env);
        todo(e, v);
        if (v instanceof ValueObject)
        {
            var o = v.UID;
            if (seen.indexOf(o) == -1)
            {
                seen = seen.concat([o]);
                var he = this.env.H[o];
                if (he)
                {
                    var fs = he.fs;
                    for (var f in fs)
                        this.expressionDfs(new ExpressionDot(e, f), seen, todo);
                }
            }
        }
    }
    private allExpressionDfs(todo: (e: Expression, v: Value) => void): void
    {
        for (var x in this.env.r)
            this.expressionDfs(new ExpressionX(x), [], todo);
    }

    private reachableObjects(): number[]
    {
        var reachableObjects: number[] = [];
        this.allExpressionDfs((e, v) => {
            if (v instanceof ValueObject)
                reachableObjects.push(v.UID);
        });
        return reachableObjects;
    }
    private getNameableObjects_cache: { [o: number]: Expression[] } | null = null;
    private getNameableObjects(): { [o: number]: Expression[] }
    {
        if (this.getNameableObjects_cache) return this.getNameableObjects_cache;

        // collect reachable objects
        var reachableObjects: {e: Expression, o: number}[] = [];
        this.allExpressionDfs((e, v) => {
            if (v instanceof ValueObject)
                reachableObjects.push({e: e, o: v.UID});
        });
        var os = reachableObjects.map(x => x.o).sort();
        os = os.filter((x, i) => i == 0 || os[i - 1] != x);
        var objs: { [o: number]: Expression[] } = {};
        for (var o of os)
            objs[o] = reachableObjects
                .filter(x => x.o == o)
                .map(x => x.e)
                .sort((a, b) => a.depth() - b.depth());
        return this.getNameableObjects_cache = objs;
    }
    private getExpressions(v: Value): Expression[]
    {
        var res: Expression[] = [];
        if (v instanceof ValueExpression)
            res.push(new ExpressionV(v));
        this.allExpressionDfs((e, vv) => {
            if (vv.equalTo(v))
                res.push(e);
        });
        return res;
    }
    public impliedEqualities(): {e1: Expression, e2: Expression}[]
    {
        var res: {e1: Expression, e2: Expression}[] = [];
        this.allExpressionDfs((e, v) => {
            res.push(...this.getExpressions(v).map(ex => {return {e1: e, e2: ex};}));
        });
        return res;
    }
    public impliedInequalities(): {e1: Expression, e2: Expression}[]
    {
        var res: {e1: Expression, e2: Expression}[] = [];
        this.ineq.forEach(ineq => {
            var a = ineq.v1;
            var b = ineq.v2;
            for (var ea of this.getExpressions(a))
                for (var eb of this.getExpressions(b))
                    res.push({e1: ea, e2: eb});
        });
        return res;
    }
    public createFormula(): VerificationFormula
    {
        var objs = this.getNameableObjects();
        // BUILD
        var parts: FormulaPart[] = [];
        // accs
        for (var acc of this.env.A)
            if (objs[acc.o])
                parts.push(new FormulaPartAcc(objs[acc.o][0], acc.f));
        // ineq
        var getExpression: (v: Value) => Expression | null = (v: Value) => {
            if (v instanceof ValueExpression)
                return new ExpressionV(v);
            if (v instanceof ValueObject)
            {
                var o = v.UID;
                if (objs[o])
                    return objs[o][0];
                return null;
            }
            throw "unknown subtype";
        };
        for (var ineq of this.ineq)
        {
            var e1 = getExpression(ineq.v1);
            var e2 = getExpression(ineq.v2);
            if (e1 && e2)
                parts.push(new FormulaPartNeq(e1, e2));
        }
        // eq
        this.allExpressionDfs((e, v) => {
            var ex = getExpression(v);
            if (ex)
                parts.push(new FormulaPartEq(e, ex));
        });
        // not nulls
        this.allExpressionDfs((e, v) => {
            if (v instanceof ValueObject)
                if (this.env.H[v.UID])
                    parts.push(new FormulaPartNeq(e, Expression.getNull()));
        });
        // MINIFY
        for (var i = parts.length - 1; i >= 0; --i)
        {
            var partTarget = parts[i];
            var partsSource = parts.filter((_, j) => i != j);
            if (new VerificationFormula(null, partsSource).implies(
                new VerificationFormula(null, [partTarget])))
            {
                parts = partsSource;
            }
        }
        return new VerificationFormula(null, parts);
    }

    public getEnv(): EvalEnv { return cloneEvalEnv(this.env); }

    public getPivotEnv(): EvalEnv
    {
        var res = this.getEnv();
        for (var x in res.r)
        {
            var v = res.r[x];
            if (v instanceof ValueObject)
            {
                if (res.H[v.UID] == null)
                    res.r[x] = ValueExpression.getNull();
            }
        }
        return res;
    }

    // consistent
    private getConsistentAcc(): boolean
    {
        var a: FootprintDynamic = [];
        for (var x of this.env.A)
        {
            if (a.some(y => y.f == x.f && y.o == x.o))
                return false;
            a.push(x);
        }
        return true;
    }
    private getConsistentIneq(): boolean
    {
        return this.ineq.every(x => !x.v1.equalTo(x.v2));
    }
    private getConsistent(): boolean
    {
        return this.getConsistentAcc() && this.getConsistentIneq();
    }

    private ensure(e: Expression): NormalizedEnv | null
    {
        if (e.eval(this.env)) return this;

        if (e instanceof ExpressionX)
        {
            var env = this.getEnv();
            env.r[e.x] = new ValueObject();
            return NormalizedEnv.create(this.ineq, env);
        }
        if (e instanceof ExpressionDot)
        {
            var nenv = this.ensure(e.e);
            if (!nenv) return null;
            var vo = e.e.eval(nenv.env);
            if (vo instanceof ValueObject)
            {
                var o = vo.UID;
                var env: EvalEnv = nenv.getEnv();
                // check heap entry
                if (!env.H[o])
                    env.H[o] = {C: null, fs:{}};
                var HEntry = env.H[o];
                // check field entry
                if (!HEntry.fs[e.f])
                    HEntry.fs[e.f] = new ValueObject();
                return NormalizedEnv.create(nenv.ineq, env);
            }
            return null;
        }
        throw "wat";
    }

    private addAccV(v: Value, f: string): NormalizedEnv | null
    {
        if (v instanceof ValueObject)
        {
            var ineq = this.ineq.slice();
            var env = this.getEnv();
            env.A.push({ o: v.UID, f: f });
            return NormalizedEnv.create(ineq, env);
        }
        return null;
    }
    private addIneqV(v1: Value, v2: Value): NormalizedEnv | null
    {
        return NormalizedEnv.create(this.ineq.concat([{v1: v1, v2: v2}]), this.env);
    }
    private mergeObj(o: ValueObject, v: Value): { env: NormalizedEnv, todo: ValuePair[] } | null
    {
        var ineq = NormalizedEnv.mergeObjIneq(o, v, this.ineq);
        var acc = NormalizedEnv.mergeObjAccess(o.UID, v, this.env.A);
        var Htodo = NormalizedEnv.mergeObjHeap(o.UID, v, NormalizedEnv.mergeObjHeapC(o, v, this.env.H));
        var rho = cloneRho(this.env.r);
        for (var x in rho)
            if (rho[x].equalTo(o))
                rho[x] = v;

        if (!ineq || !acc || !Htodo)
            return null;
        var env = NormalizedEnv.create(ineq, {H: Htodo.H, r: rho, A: acc});
        return env
            ? { env: env, todo: Htodo.todo }
            : null;
    }
    private merge(v1: Value, v2: Value): { env: NormalizedEnv, todo: ValuePair[] } | null
    {
        if (v1.equalTo(v2))
            return { env: this, todo: [] };
        if (v1 instanceof ValueObject)
            return this.mergeObj(v1, v2);
        if (v2 instanceof ValueObject)
            return this.mergeObj(v2, v1);
        return null;
    }

    private addEqV(v1: Value, v2: Value): NormalizedEnv | null
    {
        var res: NormalizedEnv = this;
        var todo: ValuePair[] = [{v1: v1, v2: v2}];
        while (todo.length > 0)
        {
            var job = todo.pop();
            if (job === undefined) throw "unreachable";
            var mergeRes = res.merge(job.v1, job.v2);
            if (!mergeRes) return null;
            res = mergeRes.env;
            todo.push(...mergeRes.todo);
        }
        return res;
    }

    public addAcc(e: Expression, f: string): NormalizedEnv | null
    {
        var env = this.ensure(new ExpressionDot(e, f));
        if (!env) return null;
        return env.addAccV(e.eval(env.env), f);
    }

    public addIneq(e1: Expression, e2: Expression): NormalizedEnv | null
    {
        var env = this.ensure(e1);
        if (!env) return null;
        env = env.ensure(e2);
        if (!env) return null;
        return env.addIneqV(e1.eval(env.env), e2.eval(env.env));
    }

    public addEq(e1: Expression, e2: Expression): NormalizedEnv | null
    {
        var env = this.ensure(e1);
        if (!env) return null;
        env = env.ensure(e2);
        if (!env) return null;
        return env.addEqV(e1.eval(env.env), e2.eval(env.env));
    }

    public woVar(x: string): NormalizedEnv
    {
        var env = cloneEvalEnv(this.env);
        delete env.r[x];
        return NormalizedEnv.create(this.ineq, env) as NormalizedEnv;
    }
    private createExpression(o: number): Expression | null
    {
        // collect reachable objects
        var reachableObjects: {e: Expression, o: number}[] = [];
        this.allExpressionDfs((e, v) => {
            if (v instanceof ValueObject)
                reachableObjects.push({e: e, o: v.UID});
        });

        var res = reachableObjects.filter(x => x.o == o)[0];
        if (res)
            return res.e;
        return null;
    }
    private woAccInternal(o: number, f: string): NormalizedEnv
    {
        var ineq = this.ineq.slice();
        // augment implicit inequalities
        this.allExpressionDfs((e, v) => {
            if (v instanceof ValueObject && this.addEqV(v, new ValueObject(o)) == null)
                ineq.push({v1: v, v2: new ValueObject(o)});
        });

        var env = cloneEvalEnv(this.env);
        env.A = env.A.filter(x => x.o != o || x.f != f);
        var he = env.H[o];
        if (he)
            delete he.fs[f]; // failing monotonicity: acc(x.f) => x <> 1     but not anymore after applying [w/o x.f]
            //if (he.fs[f] !== undefined)
            //    he.fs[f] = new ValueObject();
        return NormalizedEnv.create(ineq, env) as NormalizedEnv;
    }
    public woAcc(e: Expression, f: string): NormalizedEnv
    {
        var x: NormalizedEnv = this;
        for (var o of this.reachableObjects())
        {
            var ex = this.createExpression(o);
            if (ex && this.addEq(e, ex) == null)
            {
                continue; // aliasing apparently impossible
            }
            x = x.woAccInternal(o, f);
        }
        return x;
    }
}

