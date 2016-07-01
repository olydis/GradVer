import { VerificationFormulaData, ExpressionPair } from "./VerificationFormulaData";
import { Expression } from "./Expression";
import { Type } from "./Type";

export function vfdTrue(): VerificationFormulaData
{
    return {  
        access: [],
        equalities: [],
        inEqualities: [],
        types: [],
        knownToBeFalse: false
    };
}

function ExpressionPairEq(ep1: ExpressionPair, ep2: ExpressionPair): boolean
{
    return Expression.eq(ep1.e1, ep2.e1)
        && Expression.eq(ep1.e2, ep2.e2);
}

function ExpressionLT(e1: Expression, e2: Expression): boolean
{
    var d1 = e1.depth();
    var d2 = e2.depth();
    return d1 < d2 || (d1 == d2 && e1.toString() < e2.toString());
}

function ExpressionTryReduce(
    eqs: ExpressionPair[], 
    e: Expression): Expression
{
    var eOrig = e;
    var changed = true;
    while (changed)
    {
        changed = false;
        for (var eq of eqs)
        {
            var ex = e.subste(eq.e1, eq.e2);
            if (!Expression.eq(e, ex))
            {
                e = ex;
                changed = true;
            }
        }
    }
    return Expression.eq(e, eOrig) ? null : e;
}

function ExpressionPairSort(eqs: ExpressionPair[]): ExpressionPair[]
{
    eqs = eqs.map(eq =>
    {
        if (ExpressionLT(eq.e1, eq.e2))
            return { e1: eq.e2, e2: eq.e1 };
        else
            return eq;
    });
    eqs.sort((a, b) => ExpressionLT(a.e1, b.e1) ? 1 : -1);
    return eqs;
}
function ExpressionsReduce(
        eqs: ExpressionPair[],
        eqsToReduce: ExpressionPair[]): boolean
{
    var changed = false;
    for (var i = 0; i < eqsToReduce.length; ++i)
    {
        var eq = { e1: eqsToReduce[i].e1, e2: eqsToReduce[i].e2 };
        var e1x = ExpressionTryReduce(eqs.filter(e => eqsToReduce[i] != e), eq.e1);
        var e2x = ExpressionTryReduce(eqs.filter(e => eqsToReduce[i] != e), eq.e2);
        eq.e1 = e1x || eq.e1;
        eq.e2 = e2x || eq.e2;
        if (e1x != null || e2x != null)
        {
            eqsToReduce[i] = eq;
            changed = true;
        }
    }
    return changed;
}

function ExpressionTryPeal(e: Expression): Expression
{
    if (e.depth() <= 1) return null;
    return (<any>e).e;
}
function ExpressionTryPealPair(p: ExpressionPair): ExpressionPair
{
    if (p.e1.depth() <= 1 || p.e2.depth() <= 1) return null;
    if ((<any>p.e1).f != (<any>p.e2).f) return null;
    return { e1: ExpressionTryPeal(p.e1), e2: ExpressionTryPeal(p.e2) };
}

function ExpressionTryGetCoreVar(e: Expression): string
{
    var ee: any = e;
    var d = e.depth();
    if (d == 0) return null;
    if (d == 1) return ee.x;
    return ExpressionTryGetCoreVar(ee.e);
}

export function vfdNormalize(data: VerificationFormulaData): VerificationFormulaData
{
    var knownToBeFalse = data.knownToBeFalse;

    // EQ
    var eqs = data.equalities.slice();
    var changed = true;
    // reduction
    while (changed)
    {
        // remove tautos
        eqs = eqs.filter(eq => !Expression.eq(eq.e1, eq.e2));
        // normal order
        eqs = ExpressionPairSort(eqs);
        // reduce
        changed = ExpressionsReduce(eqs, eqs);
    }
    // equivalence classes
    // TODO?

    // ACCESS
    var accs = data.access.slice();
    // reduce
    for (var acc of accs)
    {
        var ex = ExpressionTryReduce(eqs, acc.e);
        acc.e = ex || acc.e;
    }
    // sort
    accs.sort((a, b) => (a.e.toString() + "." + a.f) < (b.e.toString() + "." + b.f) ? -1 : 1);
    // duplicate? => impossible
    for (var i = 1; i < accs.length; ++i)
    {
        var a = accs[i - 1];
        var b = accs[i];
        if (Expression.eq(a.e, b.e) && a.f == b.f)
            knownToBeFalse = true;
    }

    // NEQ
    var neq = data.inEqualities.slice();
    // induce from access
    for (var acc of accs)
        neq.push({ e1: acc.e, e2: Expression.getNull() });
    // reduce
    ExpressionsReduce(eqs, neq);
    // expand
    // TODO? using equalities
    // peal
    for (var i = 0; i < neq.length; ++i)
    {
        var pealed = ExpressionTryPealPair(neq[i]);
        if (pealed != null)
            neq.push(pealed);
    }
    // sort
    neq = ExpressionPairSort(neq);
    // refl entry? => impossible
    for (var neqEntry of neq)
        if (Expression.eq(neqEntry.e1, neqEntry.e2))
            knownToBeFalse = true;

    // TYPES
    var types = data.types.slice();
    // induce from eq and neq
    for (var eq of eqs)
        if (eq.e1.depth() == 1 && ExpressionTryGetCoreVar(eq.e1) && eq.e2.depth() == 0)
            types.push({ x: ExpressionTryGetCoreVar(eq.e1), T: (<any>eq.e2).v.getType() });
    for (var eq of eqs.concat(neq))
    {
        if (eq.e1.depth() > 1)
            types.push({ x: ExpressionTryGetCoreVar(eq.e1), T: null });
        if (eq.e2.depth() > 1)
            types.push({ x: ExpressionTryGetCoreVar(eq.e2), T: null });
    }
    // sort
    types.sort((a, b) => a.x < b.x ? -1 : 1);
    // reduce
    var typesRed: { x: string, T: Type }[] = [];
    for (var type of types)
    {
        var newEntry = typesRed.length == 0 || typesRed[typesRed.length - 1].x != type.x;
        if (newEntry)
            typesRed.push(type);
        var entry = typesRed[typesRed.length - 1];
        var intersection = Type.intersect(entry.T, type.T);
        if (intersection.impossible)
            knownToBeFalse = true;
        else
            entry.T = intersection.t;
    }
    types = typesRed;

    return {
        access: accs,
        equalities: eqs,
        inEqualities: neq,
        types: types,
        knownToBeFalse: knownToBeFalse
    };
}

// pot. false negatives!
export function vfdImpliesApprox(
    data1: VerificationFormulaData,
    data2: VerificationFormulaData): boolean
{
    if (data1.knownToBeFalse)
        return true;

    // --equalities
    for (var eq2 of data2.equalities)
    {   // prove eq2!
        if (data1.equalities.some(eq1 => ExpressionPairEq(eq1, eq2)))
            continue; // found exact match
        return false;
    }
    // here: equalities GUARANTEED to be implied

    // --inEqualities
    for (var neq2 of data2.inEqualities)
    {   // prove neq2!
        if (data1.inEqualities.some(neq1 => ExpressionPairEq(neq1, neq2)))
            continue; // found exact match
        return false;
    }
    // here: inEqualities GUARANTEED to be implied
    
    // --access
    var acc1s = data1.access;
    for (var acc2 of data2.access)
    {   // prove acc2!
        if (acc1s.some(acc1 => Expression.eq(acc1.e, acc2.e) && acc1.f == acc2.f))
        {
            acc1s = acc1s.filter(acc1 => !(Expression.eq(acc1.e, acc2.e) && acc1.f == acc2.f));
            continue; // found exact match
        }
        return false;
    }
    // here: access GUARANTEED to be implied
    
    // --type
    for (var ty2 of data2.types)
    {   // prove acc2!
        var ty1s = data1.types.filter(ty1 => ty1.x == ty2.x);
        if (ty1s.length > 0)
        {
            var ty1 = ty1s[0];
            if (Type.implies(ty1.T, ty2.T))
                continue; // found compatible match
        }
        return false;
    }
    // here: types GUARANTEED to be implied

    return true;
}