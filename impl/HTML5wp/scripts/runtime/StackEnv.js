define(["require", "exports", "./EvalEnv"], function (require, exports, EvalEnv_1) {
    "use strict";
    Object.defineProperty(exports, "__esModule", { value: true });
    function cloneStackEntry(se) {
        return {
            r: EvalEnv_1.cloneRho(se.r),
            A: EvalEnv_1.cloneAccess(se.A),
            ss: se.ss.slice()
        };
    }
    function cloneStackEnv(env) {
        return {
            H: EvalEnv_1.cloneHeap(env.H),
            S: env.S.map(cloneStackEntry)
        };
    }
    exports.cloneStackEnv = cloneStackEnv;
    function topEnv(env) {
        var top = env.S[env.S.length - 1];
        return {
            H: env.H,
            r: top.r,
            A: top.A
        };
    }
    exports.topEnv = topEnv;
});
