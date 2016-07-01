import { Program, Class, Field, Method } from "./Program";
import { Type } from "../types/Type";
import { Statement } from "../types/Statement";

export class ExecutionEnvironment
{
    public constructor(
        private program: Program
    )
    {
    }

    private getMain(): Statement[]
    {
        return this.program.main;
    }

    private getClasses(): Class[]
    {
        return this.program.classes;
    }

    private getClass(C: string): Class
    {
        var res = this.getClasses().filter(c => c.name == C);
        return res.length == 0 ? null : res[0];
    }

    public fields(C: string): Field[]
    {
        var cls = this.getClass(C);
        return cls == null
            ? null
            : cls.fields;
    }

    public fieldType(C: string, f: string): Type
    {
        var res = this.fields(C);
        if (res == null) return null;
        res = res.filter(c => c.name == f);
        return res.length == 0 ? null : res[0].type;
    }

    public mmethod(C: string, m: string): Method
    {
        var res = this.getClass(C);
        if (res == null) return null;
        var mm = res.methods.filter(c => c.name == m);
        return mm.length == 0 ? null : mm[0];
    }

// (*coq2latex: HSubst #o #f #v #H := #H[#o \mapsto [#f \mapsto #v]] *)
// Definition HSubst (o' : o) (f' : f) (v' : v) (h : H) : H :=
//   fun o'' =>
//     if o_decb o'' o'
//       then 
//       (
//         match h o'' with
//         | Some (C', ff') => Some (C', fun f'' => if f_decb f'' f' then Some v' else ff' f'')
//         | None => None
//         end
//       )
//       else h o''
// .

// (*coq2latex: HSubsts #o #m #H := #H[#o \mapsto [#m]] *)
// Definition HSubsts (o' : o) (r : list (f * v)) (h : H) : H :=
//   fold_left (fun a b => HSubst o' (fst b) (snd b) a) r h.

// Definition Halloc (o : o) (C : C) (h : H) : H :=
//   match fields C with
//   | Some fs =>
//       (fun o' => if o_decb o o' 
//         then Some (C, (fun f => option_map (fun fs' => defaultValue (fst fs')) (find (fun fs' => f_decb f (snd fs')) fs)))
//         else h o')
//   | None => h
//   end.

// (*coq2latex: rhoSubst #x #v #rho := #rho[#x \mapsto #v] *)
// Definition rhoSubst (x' : x) (v' : v) (r : rho) : rho :=
//   fun x'' => if x_decb x'' x' then Some v' else r x''.


// (* Figure 6: Evaluation of expressions for core language *)
// Fixpoint evale' (H : H) (rho : rho) (e : e) : option v :=
//   match e with
//   | ex x' => rho x'
//   | edot e'' f' =>
//     match evale' H rho e'' with
//     | Some (vo o') => option_bind (fun x => snd x f') (H o')
//     | _ => None
//     end
//   | ev v => Some (ve v)
//   end.

// (*coq2latex: evale #H #rho #e #v := \evalex #H #rho #e #v *)
// Definition evale (H : H) (rho : rho) (e : e) (v : v) : Prop := evale' H rho e = Some v.

// (* dynamic type derivation *)
// (*coq2latex: hasDynamicType #H #v #T := #H \vdash #v : #T *)
// Inductive hasDynamicType : H -> v -> T -> Prop :=
// | DTValNum : forall H n, hasDynamicType H (ve (vn n)) TPrimitiveInt
// | DTValNull : forall H C, hasDynamicType H (ve vnull) (TClass C)
// | DTValObj : forall H C m o, H o = Some (C,m) -> hasDynamicType H (vo o) (TClass C)
// .
// Definition hasNoDynamicType (H : H) (rho : rho) (v : v) : Prop :=
//   ~ exists T, hasDynamicType H v T.

// Definition ehasDynamicType (H : H) (rho : rho) (e : e) (T : T) : Prop :=
//   exists v, evale H rho e v /\ hasDynamicType H v T.


// (* Figure 8: Definition of footprint meta-function *)
// (*coq2latex: footprint' #H #r #p := \dynamicFP #H #r #p *)
// Definition footprint' (h : H) (r : rho) (p : phi') : A_d :=
//   match p with
//   | phiAcc e' f' => 
//       match evale' h r e' with
//       | Some (vo o) => [(o, f')]
//       | _ => []
//       end
//   | _ => []
//   end.
// (*coq2latex: footprint #H #r #p := \dynamicFP #H #r #p *)
// Definition footprint (h : H) (r : rho) (p : phi) : A_d :=
//   flat_map (footprint' h r) p.

// (* Figure 7: Evaluation of formulas for core language *)
// (*coq2latex: evalphi' #H #rho #A #p := \evalphix #H #rho #A #p *)
// Inductive evalphi' : H -> rho -> A_d -> phi' -> Prop :=
// | EATrue : forall H rho(*\*) A,
//     evalphi' H rho A phiTrue
// | EAEqual : forall H rho(*\*) A e_1 e_2 v_1 v_2,
//     evale H rho e_1 v_1 ->
//     evale H rho e_2 v_2 ->
//     v_1 = v_2 ->
//     evalphi' H rho A (phiEq e_1 e_2)
// | EANEqual : forall H rho(*\*) A e_1 e_2 v_1 v_2,
//     evale H rho e_1 v_1 ->
//     evale H rho e_2 v_2 ->
//     neq v_1 v_2 ->
//     evalphi' H rho A (phiNeq e_1 e_2)
// | EAAcc : forall H rho(*\*) (A : A_d) e (o : o) f,
//     evale H rho e (vo o) ->
//     In (o, f) A ->
//     evalphi' H rho A (phiAcc e f)
// | EAType : forall H rho(*\*) (A : A_d) x T v,
//     rho x = Some v ->
//     hasDynamicType H v T ->
//     evalphi' H rho A (phiType x T)
// .
// (*coq2latex: evalphi #H #rho #A #p := \evalphix #H #rho #A #p *)
// Inductive evalphi : H -> rho -> A_d -> phi -> Prop :=
// | EAEmpty : forall H r A, evalphi H r A []
// | EASepOp : forall H r A A1 A2 x xs,
//     A1 = footprint' H r x ->
//     incl A1 A ->
//     A2 = Aexcept A A1 ->
//     evalphi' H r A1 x ->
//     evalphi H r A2 xs ->
//     evalphi H r A (x :: xs)
// .

// (* implication on phi *)
// (*coq2latex: phiImplies #a #b := #a \implies #b *)
// Definition phiImplies (p1 p2 : phi) : Prop :=
//   forall h r a, evalphi h r a p1 -> evalphi h r a p2.


// (* static type derivation *)
// (*coq2latex: hasStaticType #p #x #T := #p \vdash #x : #T *)
// Inductive hasStaticType : phi -> e -> T -> Prop :=
// | STValNum : forall p n, 
//   hasStaticType p (ev (vn n)) TPrimitiveInt
// | STValNull : forall p C, 
//   hasStaticType p (ev vnull) (TClass C)
// | STVar : forall p T x, 
//   phiImplies p [phiType x T] -> 
//   hasStaticType p (ex x) T
// | STField : forall p e f C T, 
//   hasStaticType p e (TClass C) ->
//   fieldType C f = Some T ->
//   hasStaticType p (edot e f) T
// .

// (*coq2latex: hasNoStaticType #p #x := #x \not\in \dom(#p) *)
// Definition hasNoStaticType (phi : phi) (e : e) : Prop :=
//   ~ exists T, hasStaticType phi e T.

// (*coq2latex: fieldHasType #x #f #T := \vdash #x.#f : #T *)
// Definition fieldHasType C f T := fieldType C f = Some T.

// (* Figure 5: Hoare-based proof rules for core language *)
// (*coq2latex: accListApp #x \overline{f} #p := \overline{\acc(#x, f_i) * } #p *)
// Definition accListApp (x : x) (f_bar : list f) (p : phi) : phi := fold_right
//         (fun arg1 arg2 => phiAcc (ex x) arg1 :: arg2)
//         p
//         f_bar.


// (*coq2latex: @app phi' #p1 #p2 := #p1 * #p2 *)
// (*coq2latex: @cons phi' #p1 (@nil phi') := #p1 *)
// (*coq2latex: @cons phi' #p1 #p2 := #p1 * #p2 *)
// (*coq2latex: @pair rho A_d #a #b := #a, #b *)
// (*coq2latex: @In phi' #x #xs := #xs \implies #x *)
// (*coq2latex: @cons #_ #p1 #p2 := #p1 \cdot #p2 *)
// (*coq2latex: @appEnd phi' #xs #x := #xs * #x *)

// (*hacky: *)
// (*coq2latex: snd cf' := f_i *)
// (*coq2latex: Halloc #o #C #H := #H[#o \mapsto [\overline{f \mapsto \texttt{defaultValue}(T)}]] *)

// (*coq2latex: FVe #e := FV(#e) *)
// Fixpoint FVe (e : e) : list x :=
//   match e with
//   | ev v => []
//   | ex x => [x]
//   | edot e f => FVe e
//   end.
// Fixpoint FVeo (e : e) : option x := 
//   match e with
//   | ev _ => None
//   | ex x => Some x
//   | edot e _ => FVeo e
//   end.
// Definition FV' (phi : phi') : list x :=
//   match phi with
//   | phiTrue => []
//   | phiEq e1 e2 => FVe e1 ++ FVe e2
//   | phiNeq e1 e2 => FVe e1 ++ FVe e2
//   | phiAcc e f => FVe e
//   | phiType x T => [x]
//   end.
// Definition FV (phi : phi) : list x := flat_map FV' phi.

// Definition FVA_s (A : A_s) : list x := flat_map FVe (map fst A).
// (* Definition FVmTarg (m : list (x * e)) : list x := flat_map FVe (map snd m). *)


// Inductive hoareSinglePreMini : phi -> s -> phi -> Prop :=
// | H'NewObj : forall phi(*\*) phi'(*\*) x (C : C) f_bar(*\overline{f}*),
//     phiImplies phi phi' ->
//     sfrmphi [] phi' ->
//     NotIn x (FV phi') ->
//     hasStaticType phi (ex x) (TClass C) ->
//     fieldsNames C = Some f_bar ->
//     hoareSinglePreMini
//       phi
//       (sAlloc x C)
//       (accListApp x f_bar (phiType x (TClass C) :: phiNeq (ex x) (ev vnull) :: phi'))
// | H'FieldAssign : forall (phi(*\*) : phi) phi'(*\*) (x y : x) (f : f) C T,
//     phiImplies phi (phiAcc (ex x) f :: 
//                     phiNeq (ex x) (ev vnull) :: phi') ->
//     sfrmphi [] phi' ->
//     (* NotIn x (FV phi') -> *)
//     hasStaticType phi (ex x) (TClass C) ->
//     hasStaticType phi (ex y) T ->
//     fieldHasType C f T ->
//     hoareSinglePreMini phi (sMemberSet x f y) 
//       (phiType x (TClass C) ::
//        phiAcc (ex x) f ::
//        phiNeq (ex x) (ev vnull) ::
//        phiEq (edot (ex x) f) (ex y) :: phi')
// | H'VarAssign : forall T phi(*\*) phi'(*\*) (x : x) (e : e),
//     phiImplies phi phi' ->
//     sfrmphi [] phi' ->
//     NotIn x (FV phi') ->
//     NotIn x (FVe e) ->
//     hasStaticType phi (ex x) T ->
//     hasStaticType phi e T ->
//     sfrme (staticFootprint phi') e ->
//     hoareSinglePreMini phi (sAssign x e) (phi' ++ [phiEq (ex x) e])
// | H'Return : forall phi(*\*) phi'(*\*) (x : x) T,
//     phiImplies phi phi' ->
//     sfrmphi [] phi' ->
//     NotIn xresult (FV phi') ->
//     hasStaticType phi (ex x) T ->
//     hasStaticType phi (ex xresult) T ->
//     hoareSinglePreMini 
//       phi 
//       (sReturn x) 
//       (phiType xresult T :: phiEq (ex xresult) (ex x) :: phi')
// | H'App : forall underscore(*\_*) phi_i(*\phi*) phi_p(*\*) phi_r(*\*) phi_q(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
//     hasStaticType phi_i (ex y) (TClass C) ->
//     mmethod C m = Some (Method T_r m T_p z (Contract phi_pre phi_post) underscore) ->
//     hasStaticType phi_i (ex x) T_r ->
//     hasStaticType phi_i (ex z') T_p ->
//     phiImplies phi_i (phiNeq (ex y) (ev vnull) :: phi_p ++ phi_r) ->
//     sfrmphi [] phi_r ->
//     NotIn x (FV phi_r) ->
//     (* NotIn y (FV phi_r) ->
//     NotIn z' (FV phi_r) -> *)
//     listDistinct [x ; y ; z'] ->
//     phi_p = phiSubsts2 xthis y (xUserDef z) z' phi_pre ->
//     phi_q = phiSubsts3 xthis y (xUserDef z) z' xresult x phi_post ->
//     hoareSinglePreMini phi_i (sCall x y m z') (phi_q ++ phi_r)
// | H'Assert : forall phi_1(*\*) phi_2(*\*),
//     phiImplies phi_1 phi_2 ->
//     hoareSinglePreMini phi_1 (sAssert phi_2) phi_1
// | H'Release : forall phi_1(*\*) phi_2(*\*) phi_r(*\*),
//     phiImplies phi_1 (phi_2 ++ phi_r) ->
//     sfrmphi [] phi_r ->
//     hoareSinglePreMini phi_1 (sRelease phi_2) phi_r
// | H'Declare : forall phi(*\*) phi'(*\*) x T,
//     phiImplies phi phi' ->
//     sfrmphi [] phi' ->
//     NotIn x (FV phi') ->
//     hoareSinglePreMini 
//       phi
//       (sDeclare T x)
//       (phiType x T ::
//        phiEq (ex x) (ev (defaultValue' T)) :: phi')
// .


// (*coq2latex: unfoldTypeJudjPremise #e #T #TT := \hasTypePremise {#e} {#T} {#TT} *)
// Fixpoint unfoldTypeJudjPremise (e : e) (T T' : T) : Prop :=
//   match e with
//   | ev v => T = T' /\ hasStaticType [] (ev v) T
//   | ex x => T = T'
//   | edot e f => exists C, unfoldTypeJudjPremise e (TClass C) T' /\ fieldType C f = Some T
//   end.

// (*coq2latex: unfoldTypeJudjFormula #e #T #TT := \hasTypeFormula {#e} {#T} {#TT} *)
// Fixpoint unfoldTypeJudjFormula (e : e) (T T' : T) : phi :=
//   match e with
//   | ev v => []
//   | ex x => [phiType x T']
//   | edot e f => unfoldTypeJudjFormula e T T' ++ [phiAcc e f]
//   end.

// Definition NotInFV (x : x) (p : phi) : Prop := NotIn x (FV p).

// (*coq2latex: hoareSingle #p1 #s #p2 := \hoare #p1 #s #p2 *)
// Inductive hoareSingle : phi -> s -> phi -> Prop :=
// | HNewObj : forall phi(*\*) x (C : C) f_bar(*\overline{f}*),
//     NotInFV x phi ->
//     fieldsNames C = Some f_bar ->
//     hoareSingle
//       (phiType x (TClass C) :: phi)
//       (sAlloc x C)
//       (accListApp x f_bar (phiType x (TClass C) :: phiNeq (ex x) (ev vnull) :: phi))
// | HFieldAssign : forall phi(*\*) (x y : x) (f : f) C T,
//     fieldHasType C f T ->
//     hoareSingle 
//       (phiType x (TClass C) :: 
//        phiType y T ::
//        phi ++ [phiAcc (ex x) f])
//       (sMemberSet x f y) 
//       (phiType x (TClass C) ::
//        phiAcc (ex x) f ::
//        phiEq (edot (ex x) f) (ex y) :: phi)
// | HVarAssign : forall T phi(*\*) (x : x) (e : e) T',
//     NotInFV x phi ->
//     NotIn x (FVe e) ->
//     unfoldTypeJudjPremise e T T' ->
//     hoareSingle
//       (phiType x T :: unfoldTypeJudjFormula e T T' ++ phi)
//       (sAssign x e)
//       (unfoldTypeJudjFormula e T T' ++ phi ++ [phiEq (ex x) e])
// | HReturn : forall phi(*\*) (x : x) T,
//     NotInFV xresult phi ->
//     hoareSingle 
//       (phiType x T :: phiType xresult T :: phi) 
//       (sReturn x) 
//       (phiType xresult T :: phiEq (ex xresult) (ex x) :: phi)
// | HApp : forall underscore(*\_*) phi_r(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
//     mmethod C m = Some (Method T_r m T_p z (Contract phi_pre phi_post) underscore) ->
//     NotInFV x phi_r ->
//     listDistinct [x ; y ; z'] ->
//     hoareSingle
//       (phiType x T_r :: phiType y (TClass C) :: phiType z' T_p :: phi_r ++ 
//        phiNeq (ex y) (ev vnull) :: phiSubsts2 xthis y (xUserDef z) z' phi_pre)
//       (sCall x y m z')
//       (phi_r ++ phiSubsts3 xthis y (xUserDef z) z' xresult x phi_post)
// | HAssert : forall phi(*\*) phi'(*\*),
//     phiImplies phi phi' ->
//     hoareSingle phi (sAssert phi') phi
// | HRelease : forall phi(*\*) phi'(*\*),
//     hoareSingle (phi ++ phi') (sRelease phi') phi
// | HDeclare : forall phi(*\*)  x T,
//     NotInFV x phi ->
//     hoareSingle 
//       phi
//       (sDeclare T x)
//       (phiType x T ::
//        phiEq (ex x) (ev (defaultValue' T)) :: phi)
// .

// (*coq2latex: hoare #p1 #s #p2 := \hoare #p1 #s #p2 *)
// Inductive hoare : phi -> list s -> phi -> Prop :=
// | HSec : forall (p q1 q2 r : phi) (s1 : s) (s2 : list s), (* w.l.o.g.??? *)
//     hoareSingle p s1 q1 ->
//     phiImplies q1 q2 ->
//     sfrmphi [] q2 ->
//     hoare q2 s2 r ->
//     hoare p (s1 :: s2) r
// | HEMPTY : forall p, hoare p [] p
// .

// (* Figure 9: Dynamic semantics for core language *)
// (*coq2latex: rhoFrom2 #x1 #v1 #x2 #v2 := [#x1 \mapsto #v1, #x2 \mapsto #v2] *)
// Definition rhoFrom2 (x1 : x) (v1 : v) (x2 : x) (v2 : v) : rho := 
//   fun rx => if x_decb rx x1 then Some v1 else
//            (if x_decb rx x2 then Some v2 else None).
// (*coq2latex: rhoFrom3 #x1 #v1 #x2 #v2 #x3 #v3 := [#x1 \mapsto #v1, #x2 \mapsto #v2, #x3 \mapsto #v3] *)
// Definition rhoFrom3 (x1 : x) (v1 : v) (x2 : x) (v2 : v) (x3 : x) (v3 : v) : rho := 
//   fun rx => if x_decb rx x1 then Some v1 else
//            (if x_decb rx x2 then Some v2 else
//            (if x_decb rx x3 then Some v3 else None)).

// (*coq2latex: HeapNotSetAt #H #o := #o \not\in \dom(#H) *)
// Definition HeapNotSetAt (H : H) (o : o) : Prop := H o = None.

// Definition execState : Set := H * S.
// (*coq2latex: dynSem #s1 #s2 := #s1 \rightarrow #s2 *)
// Inductive dynSem : execState -> execState -> Prop :=
// | ESFieldAssign : forall H H' (S : S) (s_bar(*\overline{s}*) : list s) (A : A_d) rho(*\*) (x y : x) (v_y : v) (o : o) (f : f),
//     evale H rho (ex x) (vo o) ->
//     evale H rho (ex y) v_y ->
//     In (o, f) A ->
//     H' = HSubst o f v_y H ->
//     dynSem (H, (rho, A, sMemberSet x f y :: s_bar) :: S) (H', (rho, A, s_bar) :: S)
// | ESVarAssign : forall H (S : S) (s_bar(*\overline{s}*) : list s) (A : A_d) rho(*\*) rho'(*\*) (x : x) (e : e) (v : v),
//     evale H rho e v ->
//     rho' = rhoSubst x v rho ->
//     dynSem (H, (rho, A, sAssign x e :: s_bar) :: S) (H, (rho', A, s_bar) :: S)
// | ESNewObj : forall H H' (S : S) (s_bar(*\overline{s}*) : list s) (A A' : A_d) rho(*\*) rho'(*\*) (x : x) (o : o) (C : C) Tfs,
//     HeapNotSetAt H o ->
//     fields C = Some Tfs ->
//     rho' = rhoSubst x (vo o) rho ->
//     A' = A ++ map (fun cf' => (o, snd cf')) Tfs ->
//     H' = Halloc o C H ->
//     dynSem (H, (rho, A, sAlloc x C :: s_bar) :: S) (H', (rho', A', s_bar) :: S)
// | ESReturn : forall H (S : S) (s_bar(*\overline{s}*) : list s) (A : A_d) rho(*\*) rho'(*\*) (x : x) (v_x : v),
//     evale H rho (ex x) v_x ->
//     rho' = rhoSubst xresult v_x rho ->
//     dynSem (H, (rho, A, sReturn x :: s_bar) :: S) (H, (rho', A, s_bar) :: S)
// | ESApp : forall underscore2(*\_*) phi H (S : S) (s_bar(*\overline{s}*) r_bar(*\overline{r}*) : list s) (A A' : A_d) T T_r rho(*\*) rho'(*\*) w (x y z : x) (v : v) (m : m) (o : o) (C : C) underscore(*\_*),
//     evale H rho (ex y) (vo o) ->
//     evale H rho (ex z) v ->
//     H o = Some (C, underscore) ->
//     mmethod C m = Some (Method T_r m T w (Contract phi underscore2) r_bar) ->
//     rho' = rhoFrom3 xresult (defaultValue T_r) xthis (vo o) (xUserDef w) v ->
//     evalphi H rho' A phi ->
//     A' = footprint H rho' phi ->
//     dynSem (H, (rho, A, sCall x y m z :: s_bar) :: S) (H, (rho', A', r_bar) :: (rho, Aexcept A A', sCall x y m z :: s_bar) :: S)
// | ESAppFinish : forall underscore(*\_*) o phi(*\*) H (S : S) (s_bar(*\overline{s}*) : list s) (A A' A'' : A_d) rho(*\*) rho'(*\*) (x : x) z (m : m) y (C : C) v_r,
//     evale H rho (ex y) (vo o) ->
//     H o = Some (C, underscore) ->
//     mpost C m = Some phi ->
//     evalphi H rho' A' phi ->
//     A'' = footprint H rho' phi ->
//     evale H rho' (ex xresult) v_r ->
//     dynSem (H, (rho', A', []) :: (rho, A, sCall x y m z :: s_bar) :: S) (H, (rhoSubst x v_r rho, A ++ A'', s_bar) :: S)
// | ESAssert : forall H rho(*\*) A phi(*\*) s_bar(*\overline{s}*) S,
//     evalphi H rho A phi ->
//     dynSem (H, (rho, A, sAssert phi :: s_bar) :: S) (H, (rho, A, s_bar) :: S)
// | ESRelease : forall H rho(*\*) A A' phi(*\*) s_bar(*\overline{s}*) S,
//     evalphi H rho A phi ->
//     A' = Aexcept A (footprint H rho phi) ->
//     dynSem (H, (rho, A, sRelease phi :: s_bar) :: S) (H, (rho, A', s_bar) :: S)
// | ESDeclare : forall H rho(*\*) rho'(*\*) A s_bar(*\overline{s}*) S T x,
//     rho' = rhoSubst x (defaultValue T) rho ->
//     dynSem (H, (rho, A, sDeclare T x :: s_bar) :: S) (H, (rho', A, s_bar) :: S)
// .

// (* helper definitions *)
// Definition isStuck (s : execState) : Prop :=
//   ~ exists s', dynSem s s'.
// Definition isFinished (s : execState) : Prop :=
//   exists r a, snd s = [(r,a,[])].
// Definition isFail (s : execState) : Prop :=
//   isStuck s /\ ~ isFinished s.

// Inductive dynSemStar : execState -> execState -> Prop :=
// | ESSNone : forall a, dynSemStar a a
// | ESSStep : forall a b c, dynSem a b -> dynSemStar b c -> dynSemStar a c
// .

// Lemma dynSemStarBack : forall a b c,
//   dynSemStar a b -> dynSem b c -> dynSemStar a c.
// Proof.
//   intros.
//   induction H0.
//   - econstructor; eauto; constructor.
//   - intuition. econstructor; eauto.
// Qed.

// (*Definition dynSemFull (initial final : execState) : Prop := dynSemStar initial final /\ isFinished final.
// *)
// Definition newHeap : H := fun _ => None.
// Definition newRho : rho := fun _ => None.
// Definition newAccess : A_d := [].


// Inductive writesTo : x -> s -> Prop :=
// | wtAssign : forall x e, writesTo x (sAssign x e)
// | wtAlloc : forall x C, writesTo x (sAlloc x C)
// | wtCall : forall x y m z, writesTo x (sCall x y m z)
// | wtReturn : forall x, writesTo xresult (sReturn x)
// | wtDeclare : forall T x, writesTo x (sDeclare T x)
// .


// (* ASSUMPTIONS *)
// Definition mWellDefined (C : C) (m : method) := 
//   match m with Method T' m' pT px c s =>
//     match c with Contract pre post =>
//       let pre' := phiType (xUserDef px) pT :: phiType xthis (TClass C) :: pre in
//       let post' := phiType (xUserDef px) pT :: phiType xthis (TClass C) :: phiType xresult T' :: post in
//         incl (FV pre) [xUserDef px ; xthis] /\
//         incl (FV post) [xUserDef px ; xthis ; xresult] /\
//         hoare pre' s post' /\
//         sfrmphi [] pre /\
//         sfrmphi [] post /\
//         (forall s', In s' s -> ~ writesTo xthis s') /\
//         (forall s', In s' s -> ~ writesTo (xUserDef px) s')
//     end
//   end.
// Definition CWellDefined (c : cls) :=
//   match c with Cls c fs ms =>
//     (listDistinct (map (fun f => match f with Field _ x => x end) fs)) /\
//     (listDistinct (map (fun m => match m with Method _ x _ _ _ _ => x end) ms)) /\
//     (forall m, In m ms -> mWellDefined c m)
//   end.
  
// Axiom pWellDefined : forall c, In c classes -> CWellDefined c.

// Lemma IsClassWellDef : forall c c',
//   class c = Some c' ->
//   CWellDefined c'.
// Proof.
//   intros.
//   unfold class in H0.
//   apply find_some in H0.
//   inversion H0.
//   apply (pWellDefined c').
//   assumption.
// Qed.

// Lemma IsMethodWellDef : forall c m m',
//   mmethod c m = Some m' ->
//   mWellDefined c m'.
// Proof.
//   intros.
//   unfold mmethod in H0.
//   destruct (class c) eqn: cc; try discriminate.
//   destruct c0.
//   assert (c0 = c).
//     unfold class in cc.
//     apply find_some in cc.
//     inversion cc.
//     undecb.
//     destruct (string_dec c0 c); try discriminate.
//     assumption.
//   subst.
//   apply IsClassWellDef in cc.
//   unfold CWellDefined in cc.
//   apply find_some in H0.
//   inversion H0.
//   apply cc in H1.
//   assumption.
// Qed.

}