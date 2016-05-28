Require Import Coq.Unicode.Utf8 Arith Bool Ring Setoid String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Sets.Powerset.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Import ListNotations.

(* helpers *)
Definition dec2decb {A : Type} (dec : ∀ a1 a2 : A, {a1 = a2} + {a1 ≠ a2}) : (A -> A -> bool) :=
  fun a b => if dec a b then true else false.
Definition except {A : Type} (A_decb : A -> A -> bool) (a b : list A) : list A :=
  filter (fun x => negb (existsb (A_decb x) b)) a.
Definition appEnd {A : Type} (l : list A) (x : A) := l ++ [x].

Definition option_bind {A B : Type} (f : A -> option B) (x : option A) : option B :=
match x with
| Some x' => f x'
| None => None
end.

(*coq2latex: @NotIn #_ #x #xs := #x \not \in #xs *)
Definition NotIn {T : Type} (x : T) (xs : list T) : Prop := ~(In x xs).

Definition nat_decb := dec2decb eq_nat_dec.
Hint Resolve eq_nat_dec.
Hint Resolve list_eq_dec eq_nat_dec.

Program Instance string_EqDec : EqDec string eq := string_dec.
Definition string_decb := dec2decb string_dec.
Hint Resolve string_dec.
Hint Resolve list_eq_dec string_dec.

(* Figure 1: Syntax of a Java-like language for core language *)
Definition C := string.
Definition f := string.
Definition m := string.
Definition o := nat.
Definition x' := string.
Inductive x :=
(*coq2latex: xUserDef #x := #x *)
| xUserDef : x' -> x
(*coq2latex: xthis := \xthis *)
| xthis : x
(*coq2latex: xresult := \xresult *)
| xresult : x.
Inductive T :=
(*coq2latex: TPrimitiveInt := \Tint *)
| TPrimitiveInt : T
(*coq2latex: TClass #C := #C *)
| TClass : C -> T.

Inductive v :=
(*coq2latex: vn #n := #n *)
| vn : nat -> v
(*coq2latex: vnull := \vnull *)
| vnull : v
(*coq2latex: vo #o := #o *)
| vo : o -> v
.

(*coq2latex: defaultValue #T := \texttt{defaultValue}(#T) *)
Definition defaultValue (T : T) : v :=
  match T with
  | TPrimitiveInt => vn 0
  | TClass C => vnull
  end.

Inductive e :=
(*coq2latex: ev #v := #v *)
| ev : v -> e
(*coq2latex: ex #x := #x *)
| ex : x -> e
(*coq2latex: edot #e #f := #e.#f *)
| edot : e -> f -> e.
Inductive phi' :=
(*coq2latex: phiTrue := \true *)
| phiTrue : phi'
(*coq2latex: phiEq #a #b := (#a = #b) *)
| phiEq : e -> e -> phi'
(*coq2latex: phiNeq #a #b := (#a \neq #b) *)
| phiNeq : e -> e -> phi'
(*coq2latex: phiAcc #x #f := \acc(#x.#f) *)
| phiAcc : x -> f -> phi'
(*coq2latex: phiType #x #T := #x : #T *)
| phiType : x -> T -> phi'.
Definition phi := list phi'.
Inductive s :=
(*coq2latex: sMemberSet #x #f #y := #x.#f := #y *)
| sMemberSet : x -> f -> x -> s
(*coq2latex: sAssign #x #e := #x := #e *)
| sAssign : x -> e -> s
(*coq2latex: sAlloc #x #C := #x := \new #C *)
| sAlloc : x -> C -> s
(*coq2latex: sCall #x #y #m #z := #x := #y.#m(#z) *)
| sCall : x -> x -> m -> x -> s
(*coq2latex: sReturn #x := \return #x *)
| sReturn : x -> s
(*coq2latex: sAssert #p := \assert #p *)
| sAssert : phi -> s
(*coq2latex: sRelease #p := \release #p *)
| sRelease : phi -> s
(*coq2latex: sDeclare #T #x := #T~#x *)
| sDeclare : T -> x -> s.
Inductive contract :=
(*coq2latex: Contract #pre #post := \requires #pre;~\ensures #post; *)
| Contract : phi -> phi -> contract.
Inductive method :=
(*coq2latex: Method #Tr #m #Tp #xp #c #s := #Tr~#m(#Tp~#xp)~#c~\{ #s \} *)
| Method : T -> m -> T -> x' -> contract -> list s -> method.
Inductive field :=
| Field : T -> f -> field.
Inductive cls :=
| Cls : C -> list field -> list method -> cls.
Inductive program :=
| Program : (list cls) -> (list s) -> program.

Definition H := o -> option (C * (f -> option v)).
Definition rho := x -> option v.
Definition A_s := list (x * f).
Definition A_d := list (o * f).
Definition S := list (rho * A_d * list s).

(* equality *)

Definition C_dec := string_dec.
Definition C_decb := string_decb.
Definition f_dec := string_dec.
Definition f_decb := string_decb.
Definition m_dec := string_dec.
Definition m_decb := string_decb.

Definition o_dec : ∀ n m : o, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance o_EqDec : EqDec o eq := o_dec.
Definition o_decb := dec2decb o_dec.
Hint Resolve o_dec.
Hint Resolve list_eq_dec o_dec.

Definition x_dec : ∀ n m : x, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance x_EqDec : EqDec x eq := x_dec.
Definition x_decb := dec2decb x_dec.
Hint Resolve x_dec.
Hint Resolve list_eq_dec x_dec.

Definition T_dec : ∀ n m : T, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance T_EqDec : EqDec T eq := T_dec.
Definition T_decb := dec2decb T_dec.
Hint Resolve T_dec.
Hint Resolve list_eq_dec T_dec.

Definition v_dec : ∀ n m : v, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance v_EqDec : EqDec v eq := v_dec.
Definition v_decb := dec2decb v_dec.
Hint Resolve v_dec.
Hint Resolve list_eq_dec v_dec.

Definition A_s'_decb (a b : x * f) : bool := x_decb (fst a) (fst b) && string_decb (snd a) (snd b).
Definition A_d'_decb (a b : o * f) : bool := o_decb (fst a) (fst b) && string_decb (snd a) (snd b).

Ltac undecb :=
  unfold
    A_s'_decb,
    A_d'_decb,
    v_decb,
    T_decb,
    x_decb,
    o_decb,
    m_decb,
    f_decb,
    C_decb,
    string_decb,
    dec2decb
      in *.

Definition A_sexcept := except A_s'_decb.
(*coq2latex: Aexcept #A1 #A2 := #A1 \backslash #A2 *)
Definition Aexcept := except A_d'_decb.

(*coq2latex: neq #a #b := #a \neq #b *)
Definition neq (a b : v) : Prop := a <> b.

Module Semantics.

Parameter p : program.

(* accessors *)
Definition classes : list cls := match p with Program clss _ => clss end.
Definition class (C' : C) : option cls :=
    find (fun class => match class with Cls C'' _ _ => C_decb C'' C' end) classes.
(*coq2latex: fields #C := \fields(#C) *)
Definition fields (C' : C) : option (list (T * f)) :=
  match class C' with
  | None => None
  | Some class => 
    match class with
    | Cls _ fs _ => Some (map (fun f => match f with Field T' f' => (T', f') end) fs)
    end
  end.
(*coq2latex: fieldsNames #C := \fields(#C) *)
Definition fieldsNames (C' : C) : option (list f) :=
  option_map (fun l => map snd l) (fields C').
(*coq2latex: fieldType #C #f := \fieldType(#C, #f) *)
Definition fieldType (C' : C) (f' : f) : option T :=
  match class C' with
  | None => None
  | Some class => 
    match class with
    | Cls C'' fs _ => option_map
        (fun f => match f with Field T' _ => T' end)
        (find (fun f => match f with Field _ f'' => f_decb f'' f' end) fs)
    end
  end.
Definition allMethods : list method := flat_map (fun cl => match cl with Cls _ _ x => x end) classes.
(*coq2latex: mmethod #C #m := \mmethod(#C, #m) *)
Definition mmethod (C' : C) (m' : m) : option method :=
  match class C' with
  | None => None
  | Some class => 
    match class with
    | Cls C'' _ ms =>
      find (fun me => match me with Method _ m'' _ _ _ _ => m_decb m'' m' end) ms
    end
  end.
Definition mcontract (C' : C) (m' : m) : option contract :=
  option_map
    (fun me => match me with Method _ _ _ _ contr _ => contr end)
    (mmethod C' m').
(*coq2latex: mpre #C #m := \mpre(#C, #m) *)
Definition mpre (C' : C) (m' : m) : option phi :=
  option_map
    (fun contr => match contr with Contract res _ => res end)
    (mcontract C' m').
(*coq2latex: mpost #C #m := \mpost(#C, #m) *)
Definition mpost (C' : C) (m' : m) : option phi :=
  option_map
    (fun contr => match contr with Contract _ res => res end)
    (mcontract C' m').
(*coq2latex: mbody #C #m := \mbody(#C, #m) *)
Definition mbody (C' : C) (m' : m) : option (list s) :=
  option_map
    (fun me => match me with Method _ _ _ _ _ instrs => instrs end)
    (mmethod C' m').
(*coq2latex: mparam #C #m := \mparam(#C, #m) *)
Definition mparam (C' : C) (m' : m) : option (T * x') :=
  option_map
    (fun me => match me with Method _ _ paramT paramx _ _ => (paramT, paramx) end)
    (mmethod C' m').
(*coq2latex: mrettype #C #m := \mrettype(#C, #m) *)
Definition mrettype (C' : C) (m' : m) : option T :=
  option_map
    (fun me => match me with Method rt _ _ _ _ _ => rt end)
    (mmethod C' m').


Definition getMain : list s := match p with Program _ main => main end.

(* substitution *)

Fixpoint eSubsts (r : list (x * e)) (ee : e) : e :=
  match ee with
  | ex x'' => 
    match find (fun r => x_decb x'' (fst r)) r with
    | Some (_, e') => e'
    | None => ee
    end
  | edot e'' f' => edot (eSubsts r e'') f'
  | _ => ee
  end.
Definition eSubst (x' : x) (e' : e) (ee : e) : e :=
  eSubsts [(x', e')] ee.

Definition phi'Substs (r : list (x * e)) (p : phi') : phi' :=
match p with
| phiEq  e1 e2 => phiEq  (eSubsts r e1) (eSubsts r e2)
| phiNeq e1 e2 => phiNeq (eSubsts r e1) (eSubsts r e2)
| phiAcc x f'' => 
  match eSubsts r (ex x) with
  | ex x' => phiAcc x' f''
  | _ => phiTrue
  end
| phiType x T => 
  match eSubsts r (ex x) with
  | ex x' => phiType x' T
  | _ => phiTrue
  end
| phiTrue => p
end.

(*coq2latex: phiSubsts #m #phi := #phi[#m] *)
Definition phiSubsts (r : list (x * e)) (p : phi) : phi :=
  map (phi'Substs r) p.

(*coq2latex: phiSubst #x #e #phi := #phi[#e / #x] *)
Definition phiSubst (x' : x) (e' : e) (p : phi) : phi :=
  phiSubsts [(x', e')] p.
(*coq2latex: phiSubsts2 #x1 #e1 #x2 #e2 #phi := #phi[#e1, #e2 / #x1, #x2] *)
Definition phiSubsts2 (x1 : x) (e1 : e) (x2 : x) (e2 : e) (p : phi) : phi :=
  phiSubsts [(x1, e1) ; (x2, e2)] p.
(*coq2latex: phiSubsts3 #x1 #e1 #x2 #e2 #x3 #e3 #phi := #phi[#e1, #e2, #e3 / #x1, #x2, #x3] *)
Definition phiSubsts3 (x1 : x) (e1 : e) (x2 : x) (e2 : e) (x3 : x) (e3 : e) (p : phi) : phi :=
  phiSubsts [(x1, e1) ; (x2, e2) ; (x3, e3)] p.

(*coq2latex: HSubst #o #f #v #H := #H[#o \mapsto [#f \mapsto #v]] *)
Definition HSubst (o' : o) (f' : f) (v' : v) (h : H) : H :=
  fun o'' =>
    if o_decb o'' o'
      then 
      (
        match h o'' with
        | Some (C', ff') => Some (C', fun f'' => if f_decb f'' f' then Some v' else ff' f'')
        | None => None
        end
      )
      else h o''
.

(*coq2latex: HSubsts #o #m #H := #H[#o \mapsto [#m]] *)
Definition HSubsts (o' : o) (r : list (f * v)) (h : H) : H :=
  fold_left (fun a b => HSubst o' (fst b) (snd b) a) r h.

Definition Halloc (o : o) (fs : list (T * f)) (h : H) : H :=
  HSubsts o (map (fun x => (snd x, defaultValue (fst x))) fs) h.

(*coq2latex: rhoSubst #x #v #rho := #rho[#x \mapsto #v] *)
Definition rhoSubst (x' : x) (v' : v) (r : rho) : rho :=
  fun x'' => if x_decb x'' x' then Some v' else r x''.

(* Figure 2: Static typing rules for expressions of the core language *)
(*coq2latex: sfrme #A #e := #A \sfrme #e *)
Inductive sfrme : A_s -> e -> Prop :=
| WFVar : forall A x,
    sfrme A (ex x)
| WFValue : forall A v,
    sfrme A (ev v)
| WFField : forall A x f,
    In (x, f) A ->
    sfrme A (edot (ex x) f)
.


(* Figure 4: Deﬁnition of a static version of footprint *)
(*coq2latex: staticFootprint' #p := \staticFP #p *)
Definition staticFootprint' (p : phi') : A_s := 
  match p with
  | phiAcc x' f' => [(x', f')]
  | _ => []
  end.
(*coq2latex: staticFootprint #p := \staticFP #p *)
Definition staticFootprint (p : phi) : A_s := flat_map staticFootprint' p.

(* Figure 3: Static rules for syntactically self-framed formulas *)
(*coq2latex: sfrmphi' #A #e := #A \sfrmphi #e *)
Inductive sfrmphi' : A_s -> phi' -> Prop :=
| WFTrue : forall A, sfrmphi' A phiTrue
| WFEqual : forall A (e_1 e_2 : e), sfrme A e_1 -> sfrme A e_2 -> sfrmphi' A (phiEq e_1 e_2)
| WFNEqual : forall A (e_1 e_2 : e), sfrme A e_1 -> sfrme A e_2 -> sfrmphi' A (phiNeq e_1 e_2)
| WFAcc : forall A x f, sfrmphi' A (phiAcc x f)
| WFType : forall A x T, sfrmphi' A (phiType x T)
.
(*coq2latex: sfrmphi #A #e := #A \sfrmphi #e *)
Fixpoint sfrmphi (a : A_s) (p : phi) : Prop :=
  match p with
  | [] => True
  | x :: xs => sfrmphi' a x /\ sfrmphi (staticFootprint' x ++ a) xs
  end.

(* Figure 6: Evaluation of expressions for core language *)
Fixpoint evale' (H : H) (rho : rho) (e : e) : option v :=
  match e with
  | ex x' => rho x'
  | edot e'' f' =>
    match evale' H rho e'' with
    | Some (vo o') => option_bind (fun x => snd x f') (H o')
    | _ => None
    end
  | ev v => Some v
  end.

(*coq2latex: evale #H #rho #e #v := \evalex #H #rho #e #v *)
Definition evale (H : H) (rho : rho) (e : e) (v : v) : Prop := evale' H rho e = Some v.

(* dynamic type derivation *)
Inductive hasDynamicType : H -> v -> T -> Prop :=
| DTValNum : forall H n, hasDynamicType H (vn n) TPrimitiveInt
| DTValNull : forall H T, hasDynamicType H vnull T
| DTValObj : forall H C m o, H o = Some (C,m) -> hasDynamicType H (vo o) (TClass C)
.
Definition hasNoDynamicType (H : H) (rho : rho) (v : v) : Prop :=
  ~ exists T, hasDynamicType H v T.

Definition ehasDynamicType (H : H) (rho : rho) (e : e) (T : T) : Prop :=
  exists v, evale H rho e v /\ hasDynamicType H v T.


(* Figure 8: Definition of footprint meta-function *)
(*coq2latex: footprint' #H #r #p := \dynamicFP #H #r #p *)
Fixpoint footprint' (h : H) (r : rho) (p : phi') : A_d :=
  match p with
  | phiAcc x' f' => 
      match r x' with
      | Some (vo o) => [(o, f')]
      | _ => []
      end
  | _ => []
  end.
(*coq2latex: footprint #H #r #p := \dynamicFP #H #r #p *)
Definition footprint (h : H) (r : rho) (p : phi) : A_d :=
  flat_map (footprint' h r) p.

(* Figure 7: Evaluation of formulas for core language *)
(*coq2latex: evalphi' #H #rho #A #p := \evalphix #H #rho #A #p *)
Inductive evalphi' : H -> rho -> A_d -> phi' -> Prop :=
| EATrue : forall H rho(*\*) A,
    evalphi' H rho A phiTrue
| EAEqual : forall H rho(*\*) A e_1 e_2 v_1 v_2,
    evale H rho e_1 v_1 ->
    evale H rho e_2 v_2 ->
    v_1 = v_2 ->
    evalphi' H rho A (phiEq e_1 e_2)
| EANEqual : forall H rho(*\*) A e_1 e_2 v_1 v_2,
    evale H rho e_1 v_1 ->
    evale H rho e_2 v_2 ->
    neq v_1 v_2 ->
    evalphi' H rho A (phiNeq e_1 e_2)
| EAAcc : forall H rho(*\*) (A : A_d) x (o : o) f,
    rho x = Some (vo o) ->
    In (o, f) A ->
    evalphi' H rho A (phiAcc x f)
| EAType : forall H rho(*\*) (A : A_d) x T v,
    rho x = Some v ->
    hasDynamicType H v T ->
    evalphi' H rho A (phiType x T)
.
(*coq2latex: evalphi #H #rho #A #p := \evalphix #H #rho #A #p *)
Inductive evalphi : H -> rho -> A_d -> phi -> Prop :=
| EAEmpty : forall H r A, evalphi H r A []
| EASepOp : forall H r A A1 A2 x xs,
    A1 = footprint' H r x ->
    incl A1 A ->
    A2 = Aexcept A A1 ->
    evalphi' H r A1 x ->
    evalphi H r A2 xs ->
    evalphi H r A (x :: xs)
.

(* implication on phi *)
(*coq2latex: phiImplies #a #b := #a \implies #b *)
Definition phiImplies (p1 p2 : phi) : Prop :=
  forall h r a, evalphi h r a p1 -> evalphi h r a p2.


(* static type derivation *)
(*coq2latex: hasStaticType #p #x #T := #p \vdash #x : #T *)
Inductive hasStaticType : phi -> e -> T -> Prop :=
| STValNum : forall p n, 
  hasStaticType p (ev (vn n)) TPrimitiveInt
| STValNull : forall p T, 
  hasStaticType p (ev vnull) T
| STVar : forall p T x, 
  phiImplies p [phiType x T] -> 
  hasStaticType p (ex x) T
| STField : forall p e f C T, 
  hasStaticType p e (TClass C) -> 
  fieldType C f = Some T -> 
  hasStaticType p (edot e f) T
.

(*coq2latex: hasNoStaticType #p #x := #x \not\in \dom(#p) *)
Definition hasNoStaticType (phi : phi) (e : e) : Prop :=
  ~ exists T, hasStaticType phi e T.

(*coq2latex: fieldHasType #x #f #T := \vdash #x.#f : #T *)
Definition fieldHasType C f T := fieldType C f = Some T.

(* Figure 5: Hoare-based proof rules for core language *)
(*coq2latex: accListApp #x \overline{f} #p := \overline{\acc(#x, f_i) * } #p *)
Definition accListApp (x : x) (f_bar : list f) (p : phi) : phi := fold_left 
        (fun arg1 arg2 => phiAcc x arg2 :: arg1)
        f_bar
        p.


(*coq2latex: @app phi' #p1 #p2 := #p1 * #p2 *)
(*coq2latex: @cons phi' #p1 #p2 := #p1 * #p2 *)
(*coq2latex: @pair rho A_d #a #b := #a, #b *)
(*coq2latex: @In phi' #x #xs := #xs \implies #x *)
(*coq2latex: @cons #_ #p1 #p2 := #p1 \cdot #p2 *)
(*coq2latex: @appEnd phi' #xs #x := #xs * #x *)

(*hacky: *)
(*coq2latex: snd cf' := f_i *)
(*coq2latex: Halloc #o Tfs #H := #H[#o \mapsto [\overline{f \mapsto \texttt{defaultValue}(T)}]] *)

Fixpoint FVe (e : e) : list x :=
  match e with
  | ev v => []
  | ex x => [x]
  | edot e f => FVe e
  end.
Definition FV' (phi : phi') : list x :=
  match phi with
  | phiTrue => []
  | phiEq e1 e2 => FVe e1 ++ FVe e2
  | phiNeq e1 e2 => FVe e1 ++ FVe e2
  | phiAcc x f => [x]
  | phiType x T => [x]
  end.
Definition FV (phi : phi) : list x := flat_map FV' phi.

(*coq2latex: hoareSingle #p1 #s #p2 := \hoare #p1 #s #p2 *)
Inductive hoareSingle : phi -> s -> phi -> Prop :=
| HNewObj : forall phi(*\*) phi'(*\*) x (C : C) f_bar(*\overline{f}*),
    phiImplies phi phi' ->
    sfrmphi [] phi' ->
    NotIn x (FV phi') ->
    hasStaticType phi (ex x) (TClass C) ->
    fieldsNames C = Some f_bar ->
    hoareSingle
      phi
      (sAlloc x C)
      (accListApp x f_bar (phiType x (TClass C) :: phiNeq (ex x) (ev vnull) :: phi'))
| HFieldAssign : forall (phi(*\*) : phi) phi'(*\*) (x y : x) (f : f) C T,
    phiImplies phi (phiAcc x f :: 
                    phiNeq (ex x) (ev vnull) :: phi') ->
    sfrmphi [] phi' ->
    NotIn x (FV phi') ->
    hasStaticType phi (ex x) (TClass C) ->
    hasStaticType phi (ex y) T ->
    fieldHasType C f T ->
    hoareSingle phi (sMemberSet x f y) 
      (phiType x (TClass C) ::
       phiAcc x f ::
       phiNeq (ex x) (ev vnull) ::
       phiEq (edot (ex x) f) (ex y) :: phi')
| HVarAssign : forall T phi(*\*) phi'(*\*) (x : x) (e : e),
    phiImplies phi phi' ->
    sfrmphi [] phi' ->
    NotIn x (FV phi') ->
    hasStaticType phi (ex x) T ->
    hasStaticType phi e T ->
    sfrme (staticFootprint phi') e ->
    hoareSingle phi (sAssign x e) (phi' ++ [phiEq (ex x) e])
| HReturn : forall phi(*\*) phi'(*\*) (x : x) T,
    phiImplies phi phi' ->
    sfrmphi [] phi' ->
    NotIn xresult (FV phi') ->
    hasStaticType phi (ex x) T ->
    hasStaticType phi (ex xresult) T ->
    hoareSingle 
      phi 
      (sReturn x) 
      (phiType xresult T :: phiEq (ex xresult) (ex x) :: phi')
| HApp : forall underscore(*\_*) phi_i(*\phi*) phi_p(*\*) phi_r(*\*) phi_q(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
    hasStaticType phi_i (ex y) (TClass C) ->
    mmethod C m = Some (Method T_r m T_p z (Contract phi_pre phi_post) underscore) ->
    hasStaticType phi_i (ex x) T_r ->
    hasStaticType phi_i (ex z') T_p ->
    phiImplies phi_i (phiNeq (ex y) (ev vnull) :: phi_p ++ phi_r) ->
    sfrmphi [] phi_r ->
    NotIn x (FV phi_r) ->
    NotIn y (FV phi_r) ->
    NotIn z' (FV phi_r) ->
    phi_p = phiSubsts2 xthis (ex y) (xUserDef z) (ex z') phi_pre ->
    phi_q = phiSubsts3 xthis (ex y) (xUserDef z) (ex z') xresult (ex x) phi_post ->
    hoareSingle phi_i (sCall x y m z') (phi_q ++ phi_r)
| HAssert : forall phi_1(*\*) phi_2(*\*),
    phiImplies phi_1 phi_2 ->
    hoareSingle phi_1 (sAssert phi_2) phi_1
| HRelease : forall phi_1(*\*) phi_2(*\*) phi_r(*\*),
    phiImplies phi_1 (phi_2 ++ phi_r) ->
    sfrmphi [] phi_r ->
    hoareSingle phi_1 (sRelease phi_2) phi_r
| HDeclare : forall phi(*\*) phi'(*\*) x T,
    phiImplies phi phi' ->
    sfrmphi [] phi' ->
    NotIn x (FV phi') ->
    hoareSingle 
      phi
      (sDeclare T x)
      (phiType x T ::
       phiEq (ex x) (ev (defaultValue T)) :: phi')
.

(*coq2latex: hoare #p1 #s #p2 := \hoare #p1 #s #p2 *)
Inductive hoare : phi -> list s -> phi -> Prop :=
| HSec : forall (p q1 q2 r : phi) (s1 : s) (s2 : list s), (* w.l.o.g.??? *)
    hoareSingle p s1 q1 ->
    phiImplies q1 q2 ->
    hoare q2 s2 r ->
    hoare p (s1 :: s2) r
| HEMPTY : forall p, hoare p [] p
.

(* Figure 9: Dynamic semantics for core language *)
(*coq2latex: rhoFrom2 #x1 #v1 #x2 #v2 := [#x1 \mapsto #v1, #x2 \mapsto #v2] *)
Definition rhoFrom2 (x1 : x) (v1 : v) (x2 : x) (v2 : v) : rho := 
  fun rx => if x_decb rx x1 then Some v1 else
           (if x_decb rx x2 then Some v2 else None).
(*coq2latex: rhoFrom3 #x1 #v1 #x2 #v2 #x3 #v3 := [#x1 \mapsto #v1, #x2 \mapsto #v2, #x3 \mapsto #v3] *)
Definition rhoFrom3 (x1 : x) (v1 : v) (x2 : x) (v2 : v) (x3 : x) (v3 : v) : rho := 
  fun rx => if x_decb rx x1 then Some v1 else
           (if x_decb rx x2 then Some v2 else
           (if x_decb rx x3 then Some v3 else None)).

(*coq2latex: HeapNotSetAt #H #o := #o \not\in \dom(#H) *)
Definition HeapNotSetAt (H : H) (o : o) : Prop := H o = None.

Definition execState : Set := H * S.
(*coq2latex: dynSem #s1 #s2 := #s1 \rightarrow #s2 *)
Inductive dynSem : execState -> execState -> Prop :=
| ESFieldAssign : forall H H' (S : S) (s_bar(*\overline{s}*) : list s) (A : A_d) rho(*\*) (x y : x) (v_y : v) (o : o) (f : f),
    evale H rho (ex x) (vo o) ->
    evale H rho (ex y) v_y ->
    In (o, f) A ->
    H' = HSubst o f v_y H ->
    dynSem (H, (rho, A, sMemberSet x f y :: s_bar) :: S) (H', (rho, A, s_bar) :: S)
| ESVarAssign : forall H (S : S) (s_bar(*\overline{s}*) : list s) (A : A_d) rho(*\*) rho'(*\*) (x : x) (e : e) (v : v),
    evale H rho e v ->
    rho' = rhoSubst x v rho ->
    dynSem (H, (rho, A, sAssign x e :: s_bar) :: S) (H, (rho', A, s_bar) :: S)
| ESNewObj : forall H H' (S : S) (s_bar(*\overline{s}*) : list s) (A A' : A_d) rho(*\*) rho'(*\*) (x : x) (o : o) (C : C) Tfs,
    HeapNotSetAt H o ->
    fields C = Some Tfs ->
    rho' = rhoSubst x (vo o) rho ->
    A' = A ++ map (fun cf' => (o, snd cf')) Tfs ->
    H' = Halloc o Tfs H ->
    dynSem (H, (rho, A, sAlloc x C :: s_bar) :: S) (H', (rho', A', s_bar) :: S)
| ESReturn : forall H (S : S) (s_bar(*\overline{s}*) : list s) (A : A_d) rho(*\*) rho'(*\*) (x : x) (v_x : v),
    evale H rho (ex x) v_x ->
    rho' = rhoSubst xresult v_x rho ->
    dynSem (H, (rho, A, sReturn x :: s_bar) :: S) (H, (rho', A, s_bar) :: S)
| ESApp : forall underscore2(*\_*) phi H (S : S) (s_bar(*\overline{s}*) r_bar(*\overline{r}*) : list s) (A A' : A_d) T T_r rho(*\*) rho'(*\*) w (x y z : x) (v : v) (m : m) (o : o) (C : C) underscore(*\_*),
    evale H rho (ex y) (vo o) ->
    evale H rho (ex z) v ->
    H o = Some (C, underscore) ->
    mmethod C m = Some (Method T_r m T w (Contract phi underscore2) r_bar) ->
    rho' = rhoFrom3 xresult (defaultValue T_r) xthis (vo o) (xUserDef w) v ->
    evalphi H rho' A phi ->
    A' = footprint H rho' phi ->
    dynSem (H, (rho, A, sCall x y m z :: s_bar) :: S) (H, (rho', A', r_bar) :: (rho, Aexcept A A', sCall x y m z :: s_bar) :: S)
| ESAppFinish : forall underscore(*\_*) o phi(*\*) H (S : S) (s_bar(*\overline{s}*) : list s) (A A' A'' : A_d) rho(*\*) rho'(*\*) (x : x) z (m : m) y (C : C) v_r,
    evale H rho (ex y) (vo o) ->
    H o = Some (C, underscore) ->
    mpost C m = Some phi ->
    evalphi H rho' A' phi ->
    A'' = footprint H rho' phi ->
    evale H rho' (ex xresult) v_r ->
    dynSem (H, (rho', A', []) :: (rho, A, sCall x y m z :: s_bar) :: S) (H, (rhoSubst x v_r rho, A ++ A'', s_bar) :: S)
| ESAssert : forall H rho(*\*) A phi(*\*) s_bar(*\overline{s}*) S,
    evalphi H rho A phi ->
    dynSem (H, (rho, A, sAssert phi :: s_bar) :: S) (H, (rho, A, s_bar) :: S)
| ESRelease : forall H rho(*\*) A A' phi(*\*) s_bar(*\overline{s}*) S,
    evalphi H rho A phi ->
    A' = Aexcept A (footprint H rho phi) ->
    dynSem (H, (rho, A, sRelease phi :: s_bar) :: S) (H, (rho, A', s_bar) :: S)
| ESDeclare : forall H rho(*\*) rho'(*\*) A s_bar(*\overline{s}*) S T x,
    rho' = rhoSubst x (defaultValue T) rho ->
    dynSem (H, (rho, A, sDeclare T x :: s_bar) :: S) (H, (rho', A, s_bar) :: S)
.

(* helper definitions *)
Definition isStuck (s : execState) : Prop :=
  ~ exists s', dynSem s s'.
Definition isFinished (s : execState) : Prop :=
  exists r a, snd s = [(r,a,[])].
Definition isFail (s : execState) : Prop :=
  isStuck s /\ ~ isFinished s.

Inductive dynSemStar : execState -> execState -> Prop :=
| ESSNone : forall a, dynSemStar a a
| ESSStep : forall a b c, dynSem a b -> dynSemStar b c -> dynSemStar a c
.

Lemma dynSemStarBack : forall a b c,
  dynSemStar a b -> dynSem b c -> dynSemStar a c.
Proof.
  intros.
  induction H0.
  - econstructor; eauto; constructor.
  - intuition. econstructor; eauto.
Qed.

(*Definition dynSemFull (initial final : execState) : Prop := dynSemStar initial final /\ isFinished final.
*)
Definition newHeap : H := fun _ => None.
Definition newRho : rho := fun _ => None.
Definition newAccess : A_d := [].


Inductive writesTo : x -> s -> Prop :=
| wtAssign : forall x e, writesTo x (sAssign x e)
| wtAlloc : forall x C, writesTo x (sAlloc x C)
| wtCall : forall x y m z, writesTo x (sCall x y m z)
| wtReturn : forall x, writesTo xresult (sReturn x)
| wtDeclare : forall T x, writesTo x (sDeclare T x)
.


(* ASSUMPTIONS *)
Definition mWellDefined (C : C) (m : method) := 
  match m with Method T' m' pT px c s =>
    match c with Contract pre post =>
      let pre' := phiType (xUserDef px) pT :: phiType xthis (TClass C) :: pre in
      let post' := phiType (xUserDef px) pT :: phiType xthis (TClass C) :: phiType xresult T' :: post in
        incl (FV pre) [xUserDef px ; xthis] /\
        incl (FV post) [xUserDef px ; xthis ; xresult] /\
        hoare pre' s post' /\
        sfrmphi [] pre /\
        sfrmphi [] post /\
        (forall s', In s' s -> ~ writesTo (xUserDef px) s')
    end
  end.
Definition CWellDefined (c : cls) :=
  match c with Cls c fs ms =>
    (forall m, In m ms -> mWellDefined c m) /\
    (forall (f : f) T1 T2, In (Field T1 f) fs -> In (Field T2 f) fs -> T1 = T2)
  end.
Axiom pWellDefined : forall c, In c classes -> CWellDefined c.

End Semantics.


(*coq2latex: projT1 #x := #x *)
(*coq2latex: @Some #_ #x := #x *)
(*coq2latex: None := \bot *)
(*coq2latex: @existT #_ #_ #T #v := {#v}_{#T} *)
(*coq2latex: @eq #_ #a #b := #a = #b *)
(*coq2latex: @pair #_ #_ #a #b := (#a, #b) *)
(*coq2latex: @nil #_ := \emptyset *)
(*coq2latex: @In #_ #x #xs := #x \in #xs *)

