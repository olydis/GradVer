import { Expression, ExpressionV, ExpressionX, ExpressionDot } from "../types/Expression";
import { Value, ValueExpression, ValueObject } from "../types/ValueExpression";
import { FootprintDynamic } from "../types/Footprint";

export type ValuePair = {v1: Value, v2: Value};

export type HeapEntryMap = { [f: string]: Value };
export type HeapEntry = { C: string, fs: HeapEntryMap };
export type Heap = { [o: number]: HeapEntry };
export type Rho = { [x: string]: Value };

export type EvalEnv = { H: Heap, r: Rho, A: FootprintDynamic };

function cloneHeapEntry(He: HeapEntry): HeapEntry
{
    var res: HeapEntry = { C: He.C, fs: {} };
    for (var f in He.fs)
        res.fs[f] = He.fs[f];
    return res;
}
function cloneHeap(H: Heap): Heap
{
    var res: Heap = {};
    for (var o in H)
        res[o] = cloneHeapEntry(H[o]);
    return res;
}
function cloneRho(rho: Rho): Rho
{
    var res: Rho = {};
    for (var x in rho)
        res[x] = rho[x];
    return res;
}
function cloneAccess(A: FootprintDynamic): FootprintDynamic
{
    var res: FootprintDynamic = [];
    for (var a of A)
        res.push({o: a.o, f: a.f});
    return res;
}
function cloneEvalEnv(env: EvalEnv): EvalEnv
{
    return { H: cloneHeap(env.H)
           , r: cloneRho(env.r)
           , A: cloneAccess(env.A)};
}

export class NormalizedEnv {
    public static create(
        ineq: ValuePair[] = [],
        env: EvalEnv = { H: {}, r: {}, A: [] }): NormalizedEnv
    {
        var result = new NormalizedEnv(ineq, env);
        return result.getConsistent() ? result : null;
    }

    private static mergeObjHeapFields(fs1: HeapEntryMap, fs2: HeapEntryMap): ValuePair[]
    {
        var res: ValuePair[] = [];
        for (var f in fs1)
            if (fs2[f])
                res.push({v1: fs1[f], v2: fs2[f]});
        return res;
    }
    private static mergeObjHeap(o: number, v: Value, H: Heap): { H: Heap, todo: ValuePair[] }
    {
        var HEntry = H[o];
        if (!HEntry) return { H: H, todo: [] };
        if (v instanceof ValueObject)
        {
            var oo = v.UID;
            H = cloneHeap(H);
            var todo: ValuePair[] = [];
            if (H[oo])
            {
                if (HEntry.C != H[oo].C) return null;
                todo = NormalizedEnv.mergeObjHeapFields(HEntry.fs, H[oo].fs);
            }
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
    private static mergeObjAccess(o: number, v: Value, A: FootprintDynamic): FootprintDynamic
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

    public getEnv(): EvalEnv { return cloneEvalEnv(this.env); }

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

    private ensure(e: Expression): NormalizedEnv
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

    private addAccV(v: Value, f: string): NormalizedEnv
    {
        if (v instanceof ValueObject)
        {
            var env = this.getEnv();
            env.A.push({ o: v.UID, f: f });
            return NormalizedEnv.create(this.ineq, env);
        }
        return null;
    }
    private addIneqV(v1: Value, v2: Value): NormalizedEnv
    {
        return NormalizedEnv.create(this.ineq.concat([{v1: v1, v2: v2}]), this.env);
    }
    private mergeObj(o: ValueObject, v: Value): { env: NormalizedEnv, todo: ValuePair[] }
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
    private merge(v1: Value, v2: Value): { env: NormalizedEnv, todo: ValuePair[] }
    {
        if (v1.equalTo(v2))
            return { env: this, todo: [] };
        if (v1 instanceof ValueObject)
            return this.mergeObj(v1, v2);
        if (v2 instanceof ValueObject)
            return this.mergeObj(v2, v1);
        return null;
    }

    private addEqV(v1: Value, v2: Value): NormalizedEnv
    {
        var res: NormalizedEnv = this;
        var todo: ValuePair[] = [{v1: v1, v2: v2}];
        while (todo.length > 0)
        {
            var job = todo.pop();
            var mergeRes = res.merge(job.v1, job.v2);
            if (!mergeRes) return null;
            res = mergeRes.env;
            todo.push(...mergeRes.todo);
        }
        return res;
    }

    public addAcc(e: Expression, f: string): NormalizedEnv
    {
        var env = this.ensure(e);
        if (!env) return null;
        return env.addAccV(e.eval(env.env), f);
    }

    public addIneq(e1: Expression, e2: Expression): NormalizedEnv
    {
        var env = this.ensure(e1);
        if (!env) return null;
        env = env.ensure(e2);
        if (!env) return null;
        return env.addIneqV(e1.eval(env.env), e2.eval(env.env));
    }

    public addEq(e1: Expression, e2: Expression): NormalizedEnv
    {
        var env = this.ensure(e1);
        if (!env) return null;
        env = env.ensure(e2);
        if (!env) return null;
        return env.addEqV(e1.eval(env.env), e2.eval(env.env));
    }
}

