Load GradVer_Imports.

(*coq2latex: @listDistinct #_ #xs := x \neq y \wedge x \neq z' *)

(*coq2latex: @NotIn #_ #x #xs := #x \not \in #xs *)
Definition NotIn {T : Type} (x : T) (xs : list T) : Prop := ~(In x xs).

(* Figure 1: Syntax of a Java-like language for core language *)
Definition C := string.
Definition f := string.
Definition m := string.
Definition o := list string.
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

Inductive vex :=
(*coq2latex: vn #n := #n *)
| vn : nat -> vex
(*coq2latex: vnull := \vnull *)
| vnull : vex
.

Inductive v :=
(*coq2latex: ve #ve := #ve *)
| ve : vex -> v
(*coq2latex: vo #o := #o *)
| vo : o -> v
.

(*coq2latex: defaultValue' #T := \texttt{defaultValue}(#T) *)
Definition defaultValue' (T : T) : vex :=
  match T with
  | TPrimitiveInt => vn 0
  | TClass C => vnull
  end.
(*coq2latex: defaultValue #T := \texttt{defaultValue}(#T) *)
Definition defaultValue (T : T) : v := ve (defaultValue' T).

Inductive e :=
(*coq2latex: ev #v := \ev{$#v$} *)
| ev : vex -> e
(*coq2latex: ex #x := \ex{$#x$} *)
| ex : x -> e
(*coq2latex: edot #e #f := \edot{$#e$}{$#f$} *)
| edot : e -> f -> e.
Inductive phi' :=
(*coq2latex: phiTrue := \phiTrue *)
| phiTrue : phi'
(*coq2latex: phiEq #a #b := \phiEq {$#a$} {$#b$} *)
| phiEq : e -> e -> phi'
(*coq2latex: phiNeq #a #b := \phiNeq {$#a$} {$#b$} *)
| phiNeq : e -> e -> phi'
(*coq2latex: phiAcc #e #f := \phiAcc {$#e$} {$#f$} *)
| phiAcc : e -> f -> phi'.
Definition phi := list phi'.
Inductive s :=
(*coq2latex: sMemberSet #x #f #y := \sMemberSet {$#x$} {$#f$} {$#y$} *)
| sMemberSet : x -> f -> x -> s
(*coq2latex: sAssign #x #e := \sAssign {$#x$} {$#e$} *)
| sAssign : x -> e -> s
(*coq2latex: sAlloc #x #C := \sAlloc {$#x$} {$#C$} *)
| sAlloc : x -> C -> s
(*coq2latex: sCall #x #y #m #z := \sCall {$#x$} {$#y$} {$#m$} {$#z$} *)
| sCall : x -> x -> m -> x -> s
(*coq2latex: sReturn #x := \sReturn {$#x$} *)
| sReturn : x -> s
(*coq2latex: sAssert #p := \sAssert {$#p$} *)
| sAssert : phi -> s
(*coq2latex: sRelease #p := \sRelease {$#p$} *)
| sRelease : phi -> s
(*coq2latex: sDeclare #T #x := \sDeclare {$#T$} {$#x$} *)
| sDeclare : T -> x -> s.
Inductive contract :=
(*coq2latex: Contract #pre #post := \requires #pre;~\ensures #post; *)
| Contract : phi -> phi -> contract.
Inductive method :=
(*coq2latex: Method #Tr #m #Tp #xp #c #s := \method {$#Tr$} {$#m$} {$#Tp$} {$#xp$} {$#c$} {$#s$} *)
| Method : T -> m -> T -> x' -> contract -> list s -> method.
Inductive field :=
| Field : T -> f -> field.
Inductive cls :=
| Cls : C -> list field -> list method -> cls.
Inductive program :=
| Program : (list cls) -> (list s) -> program.

Definition H := o -> option (C * (f -> option v)).
Definition rho := x -> option v.
Definition Gamma := x -> option T.
Definition A'_s := prod e f.
Definition A_s := list A'_s.
Definition A'_d := prod o f.
Definition A_d := list A'_d.
Definition S := list (rho * A_d * list s).

(* equality *)

Definition C_dec := string_dec.
Definition C_decb := string_decb.
Definition f_dec := string_dec.
Definition f_decb := string_decb.
Definition m_dec := string_dec.
Definition m_decb := string_decb.
Hint Resolve list_eq_dec string_dec.

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

Definition vex_dec : ∀ n m : vex, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance vex_EqDec : EqDec vex eq := vex_dec.
Definition vex_decb := dec2decb vex_dec.
Hint Resolve vex_dec.
Hint Resolve list_eq_dec vex_dec.

Definition v_dec : ∀ n m : v, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance v_EqDec : EqDec v eq := v_dec.
Definition v_decb := dec2decb v_dec.
Hint Resolve v_dec.
Hint Resolve list_eq_dec v_dec.

Definition e_dec : ∀ n m : e, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance e_EqDec : EqDec e eq := e_dec.
Definition e_decb := dec2decb e_dec.
Hint Resolve e_dec.
Hint Resolve list_eq_dec e_dec.

Definition phi'_dec : ∀ n m : phi', {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance phi'_EqDec : EqDec phi' eq := phi'_dec.
Definition phi'_decb := dec2decb phi'_dec.
Hint Resolve phi'_dec.
Hint Resolve list_eq_dec phi'_dec.

Definition A'_s_dec : ∀ n m : A'_s, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance A'_s_EqDec : EqDec A'_s eq := A'_s_dec.
Definition A'_s_decb := dec2decb A'_s_dec.
Hint Resolve A'_s_dec.
Hint Resolve list_eq_dec A'_s_dec.

Definition A'_d_dec : ∀ n m : A'_d, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance A'_d_EqDec : EqDec A'_d eq := A'_d_dec.
Definition A'_d_decb := dec2decb A'_d_dec.
Hint Resolve A'_d_dec.
Hint Resolve list_eq_dec A'_d_dec.

Ltac undecb :=
  unfold
    equiv_decb,
    equiv_dec,
    A'_s_decb,
    A'_s_EqDec,
    A'_d_decb,
    A'_d_EqDec,
    vex_decb,
    vex_EqDec,
    v_decb,
    v_EqDec,
    T_decb,
    T_EqDec,
    x_decb,
    x_EqDec,
    o_decb,
    o_EqDec,
    m_decb,
    f_decb,
    C_decb,
    string_decb,
    dec2decb
      in *.

Definition GammaEmpty : Gamma := fun x => None.

(*coq2latex: GammaSet #x #T #G := #G, #x : #T *)
Definition GammaSet (x : x) (T : T) (G : Gamma) : Gamma :=
  fun x' => if x ==b x' then Some T else G x'.

Definition A_sexcept := except A'_s_decb.
(*coq2latex: Aexcept #A1 #A2 := #A1 \backslash #A2 *)
Definition Aexcept := except A'_d_decb.

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

Definition xSubsts (r : list (x * x)) (x' : x) : x :=
  match find (fun r => x_decb x' (fst r)) r with
  | Some (_, x') => x'
  | None => x'
  end.
Fixpoint eSubsts (r : list (x * x)) (ee : e) : e :=
  match ee with
  | ex x'' => ex (xSubsts r x'')
  | edot e'' f' => edot (eSubsts r e'') f'
  | _ => ee
  end.
Definition eSubst (x' x'' : x) (ee : e) : e :=
  eSubsts [(x', x'')] ee.

Definition phi'Substs (r : list (x * x)) (p : phi') : phi' :=
match p with
| phiEq  e1 e2 => phiEq  (eSubsts r e1) (eSubsts r e2)
| phiNeq e1 e2 => phiNeq (eSubsts r e1) (eSubsts r e2)
| phiAcc e f'' => phiAcc (eSubsts r e) f''
| phiTrue => p
end.

(*coq2latex: phiSubsts #m #phi := #phi[#m] *)
Definition phiSubsts (r : list (x * x)) (p : phi) : phi :=
  map (phi'Substs r) p.

(*coq2latex: phiSubst #x #e #phi := #phi[#e / #x] *)
Definition phiSubst (x' : x) (x'' : x) (p : phi) : phi :=
  phiSubsts [(x', x'')] p.
(*coq2latex: phiSubsts2 #x1 #e1 #x2 #e2 #phi := #phi[#e1, #e2 / #x1, #x2] *)
Definition phiSubsts2 (x1 : x) (x1' : x) (x2 : x) (x2' : x) (p : phi) : phi :=
  phiSubsts [(x1, x1') ; (x2, x2')] p.
(*coq2latex: phiSubsts3 #x1 #e1 #x2 #e2 #x3 #e3 #phi := #phi[#e1, #e2, #e3 / #x1, #x2, #x3] *)
Definition phiSubsts3 (x1 : x) (x1' : x) (x2 : x) (x2' : x) (x3 : x) (x3' : x) (p : phi) : phi :=
  phiSubsts [(x1, x1') ; (x2, x2') ; (x3, x3')] p.

(*coq2latex: HSubst #o #f #v #H := #H[#o \mapsto [#f \mapsto #v]] *)
Definition HSubst (o' : o) (f' : f) (v' : v) (h : H) : H :=
  fun o'' =>
    if o_decb o'' o'
      then 
      (
        match h o'' with
        | Some (C', ff') => 
          Some (C', fun f'' => 
              match ff' f'' with
              | Some v => Some (if f_decb f'' f' then v' else v)
              | None => None
              end)
        | None => None
        end
      )
      else h o''
.

(*coq2latex: HSubsts #o #m #H := #H[#o \mapsto [#m]] *)
Definition HSubsts (o' : o) (r : list (f * v)) (h : H) : H :=
  fold_left (fun a b => HSubst o' (fst b) (snd b) a) r h.

Definition Halloc (o : o) (C : C) (h : H) : H :=
  match fields C with
  | Some fs =>
      (fun o' => if o_decb o o' 
        then Some (C, (fun f => option_map (fun fs' => defaultValue (fst fs')) (find (fun fs' => f_decb f (snd fs')) fs)))
        else h o')
  | None => h
  end.

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
| WFField : forall A e f,
    In (e, f) A ->
    sfrme A e ->
    sfrme A (edot e f)
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
| WFAcc : forall A e f, sfrme A e -> sfrmphi' A (phiAcc e f)
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
  | ev v => Some (ve v)
  end.

(*coq2latex: evale #H #rho #e #v := \evalex #H #rho #e #v *)
Definition evale (H : H) (rho : rho) (e : e) (v : v) : Prop := evale' H rho e = Some v.

(* dynamic type derivation *)
(*coq2latex: hasDynamicType #H #v #T := #H \vdash #v : #T *)
Inductive hasDynamicType : H -> v -> T -> Prop :=
| DTValNum : forall H n, hasDynamicType H (ve (vn n)) TPrimitiveInt
| DTValNull : forall H C, hasDynamicType H (ve vnull) (TClass C)
| DTValObj : forall H C m o, H o = Some (C,m) -> hasDynamicType H (vo o) (TClass C)
.
Definition hasNoDynamicType (H : H) (rho : rho) (v : v) : Prop :=
  ~ exists T, hasDynamicType H v T.

Definition ehasDynamicType (H : H) (rho : rho) (e : e) (T : T) : Prop :=
  exists v, evale H rho e v /\ hasDynamicType H v T.


(* Figure 8: Definition of footprint meta-function *)
(*coq2latex: footprint' #H #r #p := \dynamicFP #H #r #p *)
Definition footprint' (h : H) (r : rho) (p : phi') : A_d :=
  match p with
  | phiAcc e' f' => 
      match evale' h r e' with
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
| EAAcc : forall H rho(*\*) (A : A_d) e (o : o) f v,
    evale H rho e (vo o) ->
    evale H rho (edot e f) v ->
    In (o, f) A ->
    evalphi' H rho A (phiAcc e f)
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
(*coq2latex: hasStaticType #G #x #T := #G \vdash #x : #T *)
Inductive hasStaticType : Gamma -> e -> T -> Prop :=
| STValNum : forall p n, 
  hasStaticType p (ev (vn n)) TPrimitiveInt
| STValNull : forall p C, 
  hasStaticType p (ev vnull) (TClass C)
| STVar : forall p T x, 
  p x = Some T -> 
  hasStaticType p (ex x) T
| STField : forall p e f C T, 
  hasStaticType p e (TClass C) ->
  fieldType C f = Some T ->
  hasStaticType p (edot e f) T
.

(*coq2latex: hasNoStaticType #G #x := #x \not\in \dom(#G) *)
Definition hasNoStaticType (G : Gamma) (e : e) : Prop :=
  ~ exists T, hasStaticType G e T.

(*coq2latex: fieldHasType #x #f #T := \vdash #x.#f : #T *)
Definition fieldHasType C f T := fieldType C f = Some T.

(* Figure 5: Hoare-based proof rules for core language *)
(*coq2latex: accListApp #x \overline{f} := \overline{\acc(#x, f_i)} *)
Definition accListApp (x : x) (f_bar : list f) : phi := 
        map
        (fun f => phiAcc (ex x) f)
        f_bar.


(*coq2latex: @incl phi' #p1 #p2 := #p1 \subseteq #p2 *)

(*coq2latex: @app phi' #p1 #p2 := \phiCons{$#p1$}{$#p2$} *)
(*coq2latex: @cons phi' #p1 (@nil phi') := \ensuremath{#p1} *)
(*coq2latex: @cons phi' #p1 #p2 := \phiCons{$#p1$}{$#p2$} *)

(*coq2latex: @app s #p1 #p2 := #p1\ttt{;} #p2 *)
(*coq2latex: @cons s #p1 (@nil s) := #p1 *)
(*coq2latex: @cons s #p1 #p2 := #p1 #p2 *)

(*coq2latex: @pair rho A_d #a #b := #a, #b *)
(*coq2latex: @In phi' #x #xs := #xs \implies #x *)
(*coq2latex: @cons #_ #p1 #p2 := #p1 \cdot #p2 *)

(*hacky: *)
(*coq2latex: snd cf' := f_i *)
(*coq2latex: Halloc #o #C #H := #H[#o \mapsto [\overline{f \mapsto \texttt{defaultValue}(T)}]] *)

(*coq2latex: FVe #e := FV(#e) *)
Fixpoint FVe (e : e) : list x :=
  match e with
  | ev v => []
  | ex x => [x]
  | edot e f => FVe e
  end.
Fixpoint FVeo (e : e) : option x := 
  match e with
  | ev _ => None
  | ex x => Some x
  | edot e _ => FVeo e
  end.
Definition FV' (phi : phi') : list x :=
  match phi with
  | phiTrue => []
  | phiEq e1 e2 => FVe e1 ++ FVe e2
  | phiNeq e1 e2 => FVe e1 ++ FVe e2
  | phiAcc e f => FVe e
  end.
Definition FV (phi : phi) : list x := flat_map FV' phi.

Definition FVA_s (A : A_s) : list x := flat_map FVe (map fst A).
(* Definition FVmTarg (m : list (x * e)) : list x := flat_map FVe (map snd m). *)


(*coq2latex: unfoldAcc #e := \accFor {#e} *)
Definition unfoldAcc (e : e) : phi :=
  match e with
  | edot e f => [phiAcc e f]
  | _ => []
  end.

(*coq2latex: GammaNotSetAt #G #x := #x \not\in \dom(#G) *)
Definition GammaNotSetAt (G : Gamma) (x : x) : Prop := G x = None.

(*coq2latex: hoare #G #p1 #s #p2 := #G \hoare #p1 #s #p2 *)
Inductive hoare : Gamma -> phi -> list s -> phi -> Prop :=
| HNewObj : forall G(*\Gamma*) phi(*\*) phi'(*\*) x (C : C) f_bar(*\overline{f}*),
    phiImplies phi phi' ->
    sfrmphi [] phi' ->
    NotIn x (FV phi') ->
    hasStaticType G (ex x) (TClass C) ->
    fieldsNames C = Some f_bar ->
    hoare
      G
      phi
      [sAlloc x C]
      (phi' ++ (phiNeq (ex x) (ev vnull) :: accListApp x f_bar))
| HFieldAssign : forall G(*\Gamma*) (phi(*\*) : phi) phi'(*\*) (x y : x) (f : f) C T,
    phiImplies phi (phiAcc (ex x) f :: phi') ->
    sfrmphi [] phi' ->
    (* NotIn x (FV phi') -> *)
    hasStaticType G (ex x) (TClass C) ->
    hasStaticType G (ex y) T ->
    fieldHasType C f T ->
    hoare G phi [sMemberSet x f y]
      (phi' ++ phiAcc (ex x) f ::
       phiNeq (ex x) (ev vnull) ::
       phiEq (edot (ex x) f) (ex y) :: [])
| HVarAssign : forall G(*\Gamma*) T phi(*\*) phi'(*\*) (x : x) (e : e),
    phiImplies phi phi' ->
    sfrmphi [] phi' ->
    NotIn x (FV phi') ->
    NotIn x (FVe e) ->
    hasStaticType G (ex x) T ->
    hasStaticType G e T ->
    incl (unfoldAcc e) phi' ->
    hoare G phi [sAssign x e] (phi' ++ [phiEq (ex x) e])
| HReturn : forall G(*\Gamma*) phi(*\*) phi'(*\*) (x : x) T,
    phiImplies phi phi' ->
    sfrmphi [] phi' ->
    NotIn xresult (FV phi') ->
    hasStaticType G (ex x) T ->
    hasStaticType G (ex xresult) T ->
    hoare G
      phi 
      [sReturn x]
      (phi' ++ phiEq (ex xresult) (ex x) :: [])
| HApp : forall G(*\Gamma*) underscore(*\_*) phi(*\phi*) phi_p(*\*) phi'(*\*) phi_q(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
    hasStaticType G (ex y) (TClass C) ->
    mmethod C m = Some (Method T_r m T_p z (Contract phi_pre phi_post) underscore) ->
    hasStaticType G (ex x) T_r ->
    hasStaticType G (ex z') T_p ->
    phiImplies phi (phiNeq (ex y) (ev vnull) :: phi_p ++ phi') ->
    sfrmphi [] phi' ->
    NotIn x (FV phi') ->
    listDistinct [x ; y ; z'] ->
    phi_p = phiSubsts2 xthis y (xUserDef z) z' phi_pre ->
    phi_q = phiSubsts3 xthis y (xUserDef z) z' xresult x phi_post ->
    hoare G phi [sCall x y m z'] (phi' ++ phi_q)
| HAssert : forall G(*\Gamma*) phi(*\*) phi'(*\*),
    phiImplies phi phi' ->
    hoare G phi [sAssert phi'] phi
| HRelease : forall G(*\Gamma*) phi(*\*) phi_r(*\*) phi'(*\*),
    phiImplies phi (phi_r ++ phi') ->
    sfrmphi [] phi' ->
    hoare G phi [sRelease phi_r] phi'
| HDeclare : forall s(*\overline{s}*) G(*\Gamma*) phi(*\*) phi'(*\*) x T,
    GammaNotSetAt G x ->
    hoare (GammaSet x T G)
      (phiEq (ex x) (ev (defaultValue' T)) :: phi)
      s
      phi' ->
    hoare G
      phi
      (sDeclare T x :: s)
      phi'
| HSec : forall s1(*\overline{s_1}*) s2(*\overline{s_2}*) G(*\Gamma*) p(*\phi_p*) q(*\phi_q*) r(*\phi_r*),
    hoare G p s1 q ->
    hoare G q s2 r ->
    hoare G p (s1 ++ s2) r
.



(*coq2latex: NotInFV #x #p := #x \not \in FV(#p) *)
Definition NotInFV (x : x) (p : phi) : Prop := NotIn x (FV p).

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
    H' = Halloc o C H ->
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
        incl (FV pre) [xUserDef px ; xthis] /\
        incl (FV post) [xUserDef px ; xthis ; xresult] /\
        hoare (GammaSet (xUserDef px) pT
              (GammaSet xthis (TClass C)
              (GammaSet xresult T'
               GammaEmpty))) pre s post /\
        sfrmphi [] pre /\
        sfrmphi [] post /\
        (forall s', In s' s -> ~ writesTo xthis s') /\
        (forall s', In s' s -> ~ writesTo (xUserDef px) s')
    end
  end.
Definition CWellDefined (c : cls) :=
  match c with Cls c fs ms =>
    (listDistinct (map (fun f => match f with Field _ x => x end) fs)) /\
    (listDistinct (map (fun m => match m with Method _ x _ _ _ _ => x end) ms)) /\
    (forall m, In m ms -> mWellDefined c m)
  end.
  
Axiom pWellDefined : forall c, In c classes -> CWellDefined c.

Lemma IsClassWellDef : forall c c',
  class c = Some c' ->
  CWellDefined c'.
Proof.
  intros.
  unfold class in H0.
  apply find_some in H0.
  inversion H0.
  apply (pWellDefined c').
  assumption.
Qed.

Lemma IsMethodWellDef : forall c m m',
  mmethod c m = Some m' ->
  mWellDefined c m'.
Proof.
  intros.
  unfold mmethod in H0.
  destruct (class c) eqn: cc; try discriminate.
  destruct c0.
  assert (c0 = c).
    unfold class in cc.
    apply find_some in cc.
    inversion cc.
    undecb.
    destruct (string_dec c0 c); try discriminate.
    assumption.
  subst.
  apply IsClassWellDef in cc.
  unfold CWellDefined in cc.
  apply find_some in H0.
  inversion H0.
  apply cc in H1.
  assumption.
Qed.

Definition A'_s2A'_d (H : H) (r : rho) (A : A'_s) : option A'_d :=
  option_bind (fun v =>
    match v with
    | vo o => Some (o, snd A)
    | _ => None
    end) (evale' H r (fst A)).
Definition evalA'_d (H : H) (A : A'_d) : option v :=
  option_bind (fun h => snd h (snd A)) (H (fst A)).
Definition evalA'_s (H : H) (r : rho) (A : A'_s) : option v :=
  option_bind (evalA'_d H) (A'_s2A'_d H r A).



End Semantics.


(*coq2latex: projT1 #x := #x *)
(*coq2latex: @Some #_ #x := #x *)
(*coq2latex: None := \bot *)
(*coq2latex: @existT #_ #_ #T #v := {#v}_{#T} *)
(*coq2latex: @eq #_ #a #b := #a = #b *)
(*coq2latex: @pair #_ #_ #a #b := (#a, #b) *)
(*coq2latex: @nil #_ := \emptyset *)
(*coq2latex: @In #_ #x #xs := #x \in #xs *)

