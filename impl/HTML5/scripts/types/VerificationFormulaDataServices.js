define(["require", "exports", "./Expression", "./Type", "./VerificationFormula"], function (require, exports, Expression_1, Type_1, VerificationFormula_1) {
    "use strict";
    function vfdTrue() {
        return {
            access: [],
            equalities: [],
            inEqualities: [],
            types: [],
            knownToBeFalse: false
        };
    }
    exports.vfdTrue = vfdTrue;
    function ExpressionPairEq(ep1, ep2) {
        return Expression_1.Expression.eq(ep1.e1, ep2.e1)
            && Expression_1.Expression.eq(ep1.e2, ep2.e2);
    }
    function ExpressionLT(e1, e2) {
        var d1 = e1.depth();
        var d2 = e2.depth();
        return d1 < d2 || (d1 == d2 && e1.toString() < e2.toString());
    }
    function ExpressionTryReduce(eqs, e) {
        var eOrig = e;
        var changed = true;
        while (changed) {
            changed = false;
            for (var _i = 0, eqs_1 = eqs; _i < eqs_1.length; _i++) {
                var eq = eqs_1[_i];
                var ex = e.subste(eq.e1, eq.e2);
                if (!Expression_1.Expression.eq(e, ex)) {
                    e = ex;
                    changed = true;
                }
            }
        }
        return Expression_1.Expression.eq(e, eOrig) ? null : e;
    }
    function ExpressionPairSort(eqs) {
        eqs = eqs.map(function (eq) {
            if (ExpressionLT(eq.e1, eq.e2))
                return { e1: eq.e2, e2: eq.e1 };
            else
                return eq;
        });
        eqs.sort(function (a, b) { return ExpressionLT(a.e1, b.e1) ? 1 : -1; });
        return eqs;
    }
    function ExpressionsReduce(eqs, eqsToReduce) {
        var changed = false;
        for (var i = 0; i < eqsToReduce.length; ++i) {
            var eq = { e1: eqsToReduce[i].e1, e2: eqsToReduce[i].e2 };
            var e1x = ExpressionTryReduce(eqs.filter(function (e) { return eqsToReduce[i] != e; }), eq.e1);
            var e2x = ExpressionTryReduce(eqs.filter(function (e) { return eqsToReduce[i] != e; }), eq.e2);
            eq.e1 = e1x || eq.e1;
            eq.e2 = e2x || eq.e2;
            if (e1x != null || e2x != null) {
                eqsToReduce[i] = eq;
                changed = true;
            }
        }
        return changed;
    }
    function ExpressionTryPeal(e) {
        if (e.depth() <= 1)
            return null;
        return e.e;
    }
    function ExpressionTryPealPair(p) {
        if (p.e1.depth() <= 1 || p.e2.depth() <= 1)
            return null;
        if (p.e1.f != p.e2.f)
            return null;
        return { e1: ExpressionTryPeal(p.e1), e2: ExpressionTryPeal(p.e2) };
    }
    function ExpressionTryGetCoreVar(e) {
        var ee = e;
        var d = e.depth();
        if (d == 0)
            return null;
        if (d == 1)
            return ee.x;
        return ExpressionTryGetCoreVar(ee.e);
    }
    function vfdNormalize(data) {
        var knownToBeFalse = data.knownToBeFalse;
        // EQ
        var eqs = data.equalities.slice();
        var changed = true;
        // reduction
        while (changed) {
            // remove tautos
            eqs = eqs.filter(function (eq) { return !Expression_1.Expression.eq(eq.e1, eq.e2); });
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
        for (var _i = 0, accs_1 = accs; _i < accs_1.length; _i++) {
            var acc = accs_1[_i];
            var ex = ExpressionTryReduce(eqs, acc.e);
            acc.e = ex || acc.e;
        }
        // sort
        accs.sort(function (a, b) { return (a.e.toString() + "." + a.f) < (b.e.toString() + "." + b.f) ? -1 : 1; });
        // duplicate? => impossible
        for (var i = 1; i < accs.length; ++i) {
            var a = accs[i - 1];
            var b = accs[i];
            if (Expression_1.Expression.eq(a.e, b.e) && a.f == b.f)
                knownToBeFalse = true;
        }
        // NEQ
        var neq = data.inEqualities.slice();
        // induce from access
        for (var _a = 0, accs_2 = accs; _a < accs_2.length; _a++) {
            var acc = accs_2[_a];
            neq.push({ e1: acc.e, e2: Expression_1.Expression.getNull() });
        }
        // reduce
        ExpressionsReduce(eqs, neq);
        // expand
        // TODO? using equalities
        // peal
        for (var i = 0; i < neq.length; ++i) {
            var pealed = ExpressionTryPealPair(neq[i]);
            if (pealed != null)
                neq.push(pealed);
        }
        // sort
        neq = ExpressionPairSort(neq);
        // refl entry? => impossible
        for (var _b = 0, neq_1 = neq; _b < neq_1.length; _b++) {
            var neqEntry = neq_1[_b];
            if (Expression_1.Expression.eq(neqEntry.e1, neqEntry.e2))
                knownToBeFalse = true;
        }
        // TYPES
        var types = data.types.slice();
        // induce from eq and neq
        for (var _c = 0, eqs_2 = eqs; _c < eqs_2.length; _c++) {
            var eq = eqs_2[_c];
            if (eq.e1.depth() == 1 && ExpressionTryGetCoreVar(eq.e1) && eq.e2.depth() == 0)
                types.push({ x: ExpressionTryGetCoreVar(eq.e1), T: eq.e2.v.getType() });
        }
        for (var _d = 0, _e = eqs.concat(neq); _d < _e.length; _d++) {
            var eq = _e[_d];
            if (eq.e1.depth() > 1)
                types.push({ x: ExpressionTryGetCoreVar(eq.e1), T: null });
            if (eq.e2.depth() > 1)
                types.push({ x: ExpressionTryGetCoreVar(eq.e2), T: null });
        }
        // sort
        types.sort(function (a, b) { return a.x < b.x ? -1 : 1; });
        // reduce
        var typesRed = [];
        for (var _f = 0, types_1 = types; _f < types_1.length; _f++) {
            var type = types_1[_f];
            var newEntry = typesRed.length == 0 || typesRed[typesRed.length - 1].x != type.x;
            if (newEntry)
                typesRed.push(type);
            var entry = typesRed[typesRed.length - 1];
            var intersection = Type_1.Type.intersect(entry.T, type.T);
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
    exports.vfdNormalize = vfdNormalize;
    function vfdMaterialize(data) {
        if (data.knownToBeFalse)
            return [new VerificationFormula_1.FormulaPartNeq(Expression_1.Expression.getNull(), Expression_1.Expression.getNull())];
        var res = [];
        res.push.apply(res, data.access.map(function (x) { return new VerificationFormula_1.FormulaPartAcc(x.e, x.f); }));
        res.push.apply(res, data.equalities.map(function (x) { return new VerificationFormula_1.FormulaPartEq(x.e1, x.e2); }));
        res.push.apply(res, data.inEqualities.map(function (x) { return new VerificationFormula_1.FormulaPartNeq(x.e1, x.e2); }));
        res.push.apply(res, data.types.filter(function (x) { return x.T != null; }).map(function (x) { return new VerificationFormula_1.FormulaPartType(x.x, x.T); }));
        return res;
    }
    // potentially too many items (returns data2/data1)
    function vfdExceptRevApprox(data1, data2) {
        if (data1.knownToBeFalse)
            return vfdMaterialize(data2);
        var res = [];
        // --equalities
        for (var _i = 0, _a = data2.equalities; _i < _a.length; _i++) {
            var eq2 = _a[_i];
            if (data1.equalities.some(function (eq1) { return ExpressionPairEq(eq1, eq2); }))
                continue; // found exact match
            res.push(new VerificationFormula_1.FormulaPartEq(eq2.e1, eq2.e2));
        }
        // here: equalities GUARANTEED to be implied
        // --inEqualities
        for (var _b = 0, _c = data2.inEqualities; _b < _c.length; _b++) {
            var neq2 = _c[_b];
            if (data1.inEqualities.some(function (neq1) { return ExpressionPairEq(neq1, neq2); }))
                continue; // found exact match
            // try simple arithmetic
            if (neq2.e2.depth() == 0) {
                var val2 = neq2.e2;
                var data1s = data1.equalities.filter(function (eq1) { return Expression_1.Expression.eq(neq2.e1, eq1.e1) && eq1.e2.depth() == 0; });
                if (data1s.length != 0) {
                    var val1 = data1s[0].e2;
                    if (!Expression_1.Expression.eq(val1, val2))
                        continue; // found witness for arithmetic inequality
                }
            }
            res.push(new VerificationFormula_1.FormulaPartNeq(neq2.e1, neq2.e2));
        }
        // here: inEqualities GUARANTEED to be implied
        // --access
        var acc1s = data1.access;
        for (var _d = 0, _e = data2.access; _d < _e.length; _d++) {
            var acc2 = _e[_d];
            if (acc1s.some(function (acc1) { return Expression_1.Expression.eq(acc1.e, acc2.e) && acc1.f == acc2.f; })) {
                acc1s = acc1s.filter(function (acc1) { return !(Expression_1.Expression.eq(acc1.e, acc2.e) && acc1.f == acc2.f); });
                continue; // found exact match
            }
            res.push(new VerificationFormula_1.FormulaPartAcc(acc2.e, acc2.f));
        }
        // here: access GUARANTEED to be implied
        // --type
        for (var _f = 0, _g = data2.types; _f < _g.length; _f++) {
            var ty2 = _g[_f];
            var ty1s = data1.types.filter(function (ty1) { return ty1.x == ty2.x; });
            if (ty1s.length > 0) {
                var ty1 = ty1s[0];
                if (Type_1.Type.implies(ty1.T, ty2.T))
                    continue; // found compatible match
            }
            if (ty2.T != null)
                res.push(new VerificationFormula_1.FormulaPartType(ty2.x, ty2.T));
        }
        // here: types GUARANTEED to be implied
        return res;
    }
    exports.vfdExceptRevApprox = vfdExceptRevApprox;
    // pot. false negatives!
    function vfdImpliesApprox(data1, data2) {
        return vfdExceptRevApprox(data1, data2).length == 0;
    }
    exports.vfdImpliesApprox = vfdImpliesApprox;
    function vfdSatisfiableApprox(data) {
        if (data.knownToBeFalse)
            return false;
        return true; // WRONG!
    }
    exports.vfdSatisfiableApprox = vfdSatisfiableApprox;
});
