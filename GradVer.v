Require Import Coq.Unicode.Utf8 Arith Bool Ring Setoid String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Sets.Powerset.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Logic.Decidable.
Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
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
| xUserDef : x' -> x
| xthis : x
| xresult : x.
Inductive T :=
| TPrimitiveInt : T
| TClass : C -> T.

(*Inductive v :=
| vn : nat -> v
| vnull : v
| vo : o -> v.*)

Definition v'PrimitiveInt := nat.
Inductive v'Class (C' : C) :=
| v'null : v'Class C'
| v'o : o -> v'Class C'.
Definition v' (T' : T) : Set :=
  match T' with
  | TPrimitiveInt => v'PrimitiveInt
  | TClass C' => v'Class C'
  end.
Definition v := sigT v'.
Definition vnull (C : C) : v := existT v' (TClass C) (v'null C).
Definition vo (C : C) (o : o) : v := existT v' (TClass C) (v'o C o).
Definition vn (n : nat) : v := existT v' (TPrimitiveInt) n.

Definition defaultValue (T : T) : v :=
  match T with
  | TPrimitiveInt => vn 0
  | TClass C => vnull C
  end.


Inductive e :=
| ev : v -> e
| ex : x -> e
| edot : e -> f -> e.
Inductive phi' :=
| phiTrue : phi'
| phiEq : e -> e -> phi'
| phiNeq : e -> e -> phi'
| phiAcc : x -> f -> phi'
| phiType : x -> T -> phi'.
Definition phi := list phi'.
Inductive s :=
| sMemberSet : x -> f -> x -> s
| sAssign : x -> e -> s
| sAlloc : x -> C -> s
| sCall : x -> x -> m -> x -> s
| sReturn : x -> s
| sAssert : phi' -> s
| sRelease : phi' -> s
| sDeclare : T -> x -> s.
Inductive contract :=
| Contract : phi -> phi -> contract.
Inductive method :=
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

Definition v'_dec : ∀ (t : T) (n m : v' t), {n = m} + {n ≠ m}. destruct t; decide equality. Defined.
Definition v'_decb (t : T) := dec2decb (v'_dec t).
Hint Resolve v'_dec.
Hint Resolve list_eq_dec v'_dec.

Definition A_s'_decb (a b : x * f) : bool := x_decb (fst a) (fst b) && string_decb (snd a) (snd b).
Definition A_d'_decb (a b : o * f) : bool := o_decb (fst a) (fst b) && string_decb (snd a) (snd b).
Definition A_sexcept := except A_s'_decb.
Definition Aexcept := except A_d'_decb.

Module Semantics.

Parameter p : program.

(* accessors *)
Definition classes : list cls := match p with Program clss _ => clss end.
Definition class (C' : C) : option cls :=
    find (fun class => match class with Cls C'' _ _ => C_decb C'' C' end) classes.
Definition fields (C' : C) : option (list (T * f)) :=
  match class C' with
  | None => None
  | Some class => 
    match class with
    | Cls _ fs _ => Some (map (fun f => match f with Field T' f' => (T', f') end) fs)
    end
  end.
Definition fieldsNames (C' : C) : option (list f) :=
  option_map (fun l => map snd l) (fields C').
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
Definition mpre (C' : C) (m' : m) : option phi :=
  option_map
    (fun contr => match contr with Contract res _ => res end)
    (mcontract C' m').
Definition mpost (C' : C) (m' : m) : option phi :=
  option_map
    (fun contr => match contr with Contract _ res => res end)
    (mcontract C' m').
Definition mbody (C' : C) (m' : m) : option (list s) :=
  option_map
    (fun me => match me with Method _ _ _ _ _ instrs => instrs end)
    (mmethod C' m').
Definition mparam (C' : C) (m' : m) : option (T * x') :=
  option_map
    (fun me => match me with Method _ _ paramT paramx _ _ => (paramT, paramx) end)
    (mmethod C' m').
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

Definition phiSubsts (r : list (x * e)) (p : phi) : phi :=
  map (phi'Substs r) p.

Definition phiSubst (x' : x) (e' : e) (p : phi) : phi :=
  phiSubsts [(x', e')] p.
Definition phiSubsts2 (x1 : x) (e1 : e) (x2 : x) (e2 : e) (p : phi) : phi :=
  phiSubsts [(x1, e1) ; (x2, e2)] p.
Definition phiSubsts3 (x1 : x) (e1 : e) (x2 : x) (e2 : e) (x3 : x) (e3 : e) (p : phi) : phi :=
  phiSubsts [(x1, e1) ; (x2, e2) ; (x3, e3)] p.

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

Definition HSubsts (o' : o) (r : list (f * v)) (h : H) : H :=
  fold_left (fun a b => HSubst o' (fst b) (snd b) a) r h.

Definition Halloc (o : o) (fs : list (T * f)) (h : H) : H :=
  HSubsts o (map (fun x => (snd x, defaultValue (fst x))) fs) h.

Definition rhoSubst (x' : x) (v' : v) (r : rho) : rho :=
  fun x'' => if x_decb x'' x' then Some v' else r x''.

(* Figure 2: Static typing rules for expressions of the core language *)
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
Definition staticFootprint' (p : phi') : A_s := 
  match p with
  | phiAcc x' f' => [(x', f')]
  | _ => []
  end.
Definition staticFootprint (p : phi) : A_s := flat_map staticFootprint' p.

(* Figure 3: Static rules for syntactically self-framed formulas *)
Inductive sfrmphi' : A_s -> phi' -> Prop :=
| WFTrue : forall A, sfrmphi' A phiTrue
| WFEqual : forall A (e_1 e_2 : e), sfrme A e_1 -> sfrme A e_2 -> sfrmphi' A (phiEq e_1 e_2)
| WFNEqual : forall A (e_1 e_2 : e), sfrme A e_1 -> sfrme A e_2 -> sfrmphi' A (phiNeq e_1 e_2)
| WFAcc : forall A x f, sfrmphi' A (phiAcc x f)
| WFType : forall A x T, sfrmphi' A (phiType x T)
.
Fixpoint sfrmphi (a : A_s) (p : phi) : Prop :=
  match p with
  | [] => True
  | x :: xs => sfrmphi' a x /\ sfrmphi (staticFootprint' x ++ a) xs
  end.

(* static type derivation *)
Definition getType (phi : phi) (x : x) : option T :=
  hd_error (flat_map (fun p => 
    match p with
    | phiType x' t => if x_decb x' x then [t] else []
    | _ => []
    end) phi).
Fixpoint staticType (phi : phi) (e' : e) : option T :=
  match e' with
  | ev v => Some (projT1 v)
  | ex x => getType phi x
  | edot e' f' => 
    option_bind
      (fun t => 
        match t with
        | TPrimitiveInt => None
        | TClass C' => fieldType C' f'
        end)
      (staticType phi e')
  end.
Definition hasStaticType (phi : phi) (e : e) (T : T) : Prop :=
  staticType phi e = Some T.
Definition hasNoStaticType (phi : phi) (e : e) : Prop :=
  staticType phi e = None.

(* Figure 6: Evaluation of expressions for core language *)
Fixpoint evale' (H : H) (rho : rho) (e : e) : option v :=
  match e with
  | ex x' => rho x'
  | edot e'' f' =>
    match evale' H rho e'' with
    | Some (existT _ (TClass _) (v'o _ o')) => option_bind (fun x => snd x f') (H o')
    | _ => None
    end
  | ev v => Some v
  end.

Definition evale (H : H) (rho : rho) (e : e) (v : v) : Prop := evale' H rho e = Some v.

(* dynamic type derivation *)
Definition dynamicType (H : H) (rho : rho) (e' : e) : option T :=
  option_map (fun v : v => projT1 v) (evale' H rho e').
Definition hasDynamicType (H : H) (rho : rho) (e : e) (T : T) : Prop :=
  dynamicType H rho e = Some T.
Definition hasNoDynamicType (H : H) (rho : rho) (e : e) : Prop :=
  dynamicType H rho e = None.


(* NOTE: there are tons of calls like "evale h r (ex x)", wouldn't it be clearer to just say "r x"? or is that less consistent? *)

(* Figure 7: Evaluation of formulas for core language *)
Definition optionVisO (v : option v) (o : o) :=
  exists C, v = Some (existT _ (TClass C) (v'o C o)).
Inductive evalphi' : H -> rho -> A_d -> phi' -> Prop :=
| EATrue : forall Heap rho A,
    evalphi' Heap rho A phiTrue
| EAEqual : forall Heap rho A e_1 e_2 v_1 v_2,
    evale Heap rho e_1 v_1 ->
    evale Heap rho e_2 v_2 ->
    v_1 = v_2 ->
    evalphi' Heap rho A (phiEq e_1 e_2)
| EANEqual : forall Heap rho A e_1 e_2 v_1 v_2,
    evale Heap rho e_1 v_1 ->
    evale Heap rho e_2 v_2 ->
    v_1 <> v_2 ->
    evalphi' Heap rho A (phiNeq e_1 e_2)
| EAAcc : forall Heap rho (A : A_d) x (o : o) f,
    optionVisO (rho x) o ->
    In (o, f) A ->
    evalphi' Heap rho A (phiAcc x f)
| EAType : forall Heap rho (A : A_d) x T v,
    rho x = Some (existT _ T v) ->
    evalphi' Heap rho A (phiType x T)
.
Definition evalphi : H -> rho -> A_d -> phi -> Prop :=
  fun h r a p => forall p', In p' p -> evalphi' h r a p'.

(* implication on phi *)
Definition phiImplies (p1 p2 : phi) : Prop :=
  forall h r a, evalphi h r a p1 -> evalphi h r a p2.

(* Figure 5: Hoare-based proof rules for core language *)
Definition fieldHasType C f T := fieldType C f = Some T.
Inductive hoareSingle : phi -> s -> phi -> Prop :=
| HNewObj : forall phi x (C : C) f_bar,
    hasStaticType phi (ex x) (TClass C) ->
    fieldsNames C = Some f_bar ->
    hoareSingle
      phi
      (sAlloc x C)
      (fold_left 
        (fun arg1 arg2 => phiAcc x arg2 :: arg1)
        f_bar
        (phiNeq (ex x) (ev (vnull C)) :: phi))
| HFieldAssign : forall (phi : phi) (x y : x) (f : f) C T,
    hasStaticType phi (ex x) (TClass C) ->
    fieldHasType C f T ->
    hasStaticType phi (ex y) T ->
    In (phiAcc x f) phi ->
    In (phiNeq (ex x) (ev (vnull C))) phi ->
    hoareSingle phi (sMemberSet x f y) (appEnd phi (phiEq (edot (ex x) f) (ex y)))
| HVarAssign : forall T phi_1 phi_2 (x : x) (e : e),
    hasStaticType phi_1 (ex x) T ->
    hasStaticType phi_1 e T ->
    phi_1 = phiSubst x e phi_2 ->
    sfrmphi [] phi_1 ->
    sfrme (staticFootprint phi_1) e ->
    hoareSingle phi_1 (sAssign x e) phi_2
| HReturn : forall phi (x : x) T,
    hasStaticType phi (ex x) T ->
    hasStaticType phi (ex xresult) T ->
    hoareSingle phi (sReturn x) (appEnd phi (phiEq (ex xresult) (ex x)))
| HApp : forall underscore phi phi_p phi_r phi_q T_r T_p (C : C) (m : m) z (z' : x) (x y : x) phi_post phi_pre,
    hasStaticType phi (ex y) (TClass C) ->
    hasStaticType phi (ex x) T_r ->
    hasStaticType phi (ex z') T_p ->
    In (phiNeq (ex y) (ev (vnull C))) phi ->
    phiImplies phi (phi_p ++ phi_r) ->
    mmethod C m = Some (Method T_r m T_p z (Contract phi_pre phi_post) underscore) ->
    phi_p = phiSubsts2 xthis (ex y) (xUserDef z) (ex z') phi_pre ->
    phi_q = phiSubsts3 xthis (ex y) (xUserDef z) (ex z') xresult (ex x) phi_post ->
    hoareSingle phi (sCall x y m z') (phi_q ++ phi_r)
| HAssert : forall phi_1 phi_2,
    In phi_2 phi_1 ->
    hoareSingle phi_1 (sAssert phi_2) phi_1
| HRelease : forall phi_1 phi_2 phi_r,
    phiImplies phi_1 (phi_2 :: phi_r) ->
    sfrmphi [] phi_r ->
    hoareSingle phi_1 (sRelease phi_2) phi_r
| HDeclare : forall phi_1 phi_2 x T,
    hasNoStaticType phi_1 (ex x) ->
    phi_2 = appEnd phi_1 (phiType x T) ->
    hoareSingle phi_1 (sDeclare T x) phi_2
.

Inductive hoare : phi -> list s -> phi -> Prop :=
| HSec : forall (p q1 q2 r : phi) (s1 : s) (s2 : list s), (* w.l.o.g.??? *)
    hoareSingle p s1 q1 ->
    phiImplies q1 q2 ->
    hoare q2 s2 r ->
    hoare p (s1 :: s2) r
| HEMPTY : forall p, hoare p [] p
.


(* well-typedness *)
Definition wellTypedE (phi : phi) (e' : e) : Prop :=
  exists T', staticType phi e' = Some T'.
Definition wellTypedPhi' (G : phi) (p : phi') : Prop :=
  match p with
  | phiTrue => True
  | phiEq e1 e2 => wellTypedE G e1 /\ wellTypedE G e2 /\ staticType G e1 = staticType G e2
  | phiNeq e1 e2 => wellTypedE G e1 /\ wellTypedE G e2 /\ staticType G e1 = staticType G e2
  | phiAcc x' f => wellTypedE G (edot (ex x') f)
  | phiType x T => getType G x = Some T
  end.
Definition wellTypedPhi (G : phi) (p : phi) : Prop :=
  forall p', In p' p -> wellTypedPhi' G p'.
Definition wellTyped (G : phi) (s' : s) : Prop :=
  match s' with
  | sMemberSet x' f' y' => let e1 := (edot (ex x') f') in
                           let e2 := ex y' in 
                            wellTypedE G e1 /\ wellTypedE G e2 /\ staticType G e1 = staticType G e2
  | sAssign x' e' => True
  | sAlloc x' C' => getType G x' = Some (TClass C')
  | sCall x' y' f' z' => exists C' T' pT px contr s',
                getType G y' = Some (TClass C') /\
                mmethod C' f' = Some (Method T' f' pT px contr s') /\
                getType G x' = Some T' /\
                Some pT = getType G z' (* /\ anything with contr and s' ???*)
  | sReturn x' => wellTypedE G (ex x')
  | sAssert p => wellTypedPhi' G p
  | sRelease p => wellTypedPhi' G p
  | sDeclare T x => getType G x = Some T
  end.


(* Figure 8: Definition of footprint meta-function *)
Fixpoint footprint' (h : H) (r : rho) (p : phi') : A_d :=
  match p with
  | phiAcc x' f' => 
      match r x' with
      | Some (existT _ (TClass _) (v'o _ o')) => [(o', f')]
      | _ => [] (*???*)
      end
  | _ => []
  end.
Fixpoint footprint (h : H) (r : rho) (p : phi) : A_d :=
  flat_map (footprint' h r) p.

(* Figure 9: Dynamic semantics for core language *)
Definition rhoFrom2 (x1 : x) (v1 : v) (x2 : x) (v2 : v) : rho := 
  fun rx => if x_decb rx x1 then Some v1 else
           (if x_decb rx x2 then Some v2 else None).
Definition rhoFrom3 (x1 : x) (v1 : v) (x2 : x) (v2 : v) (x3 : x) (v3 : v) : rho := 
  fun rx => if x_decb rx x1 then Some v1 else
           (if x_decb rx x2 then Some v2 else
           (if x_decb rx x3 then Some v3 else None)).

Definition HeapNotSetAt (H : H) (o : o) : Prop := H o = None.

Definition execState : Set := H * S.
Inductive dynSem : execState -> execState -> Prop :=
| ESFieldAssign : forall Heap Heap' C (S : S) (s_bar : list s) (A : A_d) rho (x y : x) (v_y : v) (o : o) (f : f),
    evale Heap rho (ex x) (vo C o) ->
    evale Heap rho (ex y) v_y ->
    In (o, f) A ->
    Heap' = HSubst o f v_y Heap ->
    dynSem (Heap, (rho, A, sMemberSet x f y :: s_bar) :: S) (Heap', (rho, A, s_bar) :: S)
| ESVarAssign : forall Heap (S : S) (s_bar : list s) (A : A_d) rho rho' (x : x) (e : e) (v : v),
    evale Heap rho e v ->
    rho' = rhoSubst x v rho ->
    dynSem (Heap, (rho, A, sAssign x e :: s_bar) :: S) (Heap, (rho', A, s_bar) :: S)
| ESNewObj : forall Heap Heap' (S : S) (s_bar : list s) (A A' : A_d) rho rho' (x : x) (o : o) (C : C) Tfs,
    HeapNotSetAt Heap o ->
    fields C = Some Tfs ->
    rho' = rhoSubst x (vo C o) rho ->
    A' = A ++ map (fun cf' => (o, snd cf')) Tfs ->
    Heap' = Halloc o Tfs Heap ->
    dynSem (Heap, (rho, A, sAlloc x C :: s_bar) :: S) (Heap', (rho', A', s_bar) :: S)
| ESReturn : forall Heap (S : S) (s_bar : list s) (A : A_d) rho rho' (x : x) (v_x : v),
    evale Heap rho (ex x) v_x ->
    rho' = rhoSubst xresult v_x rho ->
    dynSem (Heap, (rho, A, sReturn x :: s_bar) :: S) (Heap, (rho', A, s_bar) :: S)
| ESApp : forall underscore2 phi Heap (S : S) (s_bar r_bar : list s) (A A' : A_d) T T_r (rho rho' : rho) w (x y z : x) (v : v) (m : m) (o : o) (C : C) underscore,
    evale Heap rho (ex y) (vo C o) ->
    evale Heap rho (ex z) v ->
    Heap o = Some (C, underscore) ->
    mmethod C m = Some (Method T_r m T w (Contract phi underscore2) r_bar) ->
    rho' = rhoFrom3 xresult (defaultValue T_r) xthis (vo C o) (xUserDef w) v ->
    evalphi Heap rho' A phi ->
    A' = footprint Heap rho' phi ->
    dynSem (Heap, (rho, A, sCall x y m z :: s_bar) :: S) (Heap, (rho', A', r_bar) :: (rho, Aexcept A A', sCall x y m z :: s_bar) :: S)
| ESAppFinish : forall underscore o phi Heap (S : S) (s_bar : list s) (A A' A'' : A_d) rho rho' (x : x) z (m : m) y (C : C) v_r,
    evale Heap rho (ex y) (vo C o) ->
    Heap o = Some (C, underscore) ->
    mpost C m = Some phi ->
    evalphi Heap rho' A' phi ->
    A'' = footprint Heap rho' phi ->
    evale Heap rho' (ex xresult) v_r ->
    dynSem (Heap, (rho', A', []) :: (rho, A, sCall x y m z :: s_bar) :: S) (Heap, (rhoSubst x v_r rho, A ++ A'', s_bar) :: S)
| ESAssert : forall Heap rho A phi s_bar S,
    evalphi' Heap rho A phi ->
    dynSem (Heap, (rho, A, sAssert phi :: s_bar) :: S) (Heap, (rho, A, s_bar) :: S)
| ESRelease : forall Heap rho A A' phi s_bar S,
    evalphi' Heap rho A phi ->
    A' = Aexcept A (footprint' Heap rho phi) ->
    dynSem (Heap, (rho, A, sRelease phi :: s_bar) :: S) (Heap, (rho, A', s_bar) :: S)
| ESDeclare : forall Heap rho rho' A s_bar S T x,
    rho' = rhoSubst x (defaultValue T) rho ->
    dynSem (Heap, (rho, A, sDeclare T x :: s_bar) :: S) (Heap, (rho', A, s_bar) :: S)
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


Fixpoint getVarsE (e : e) : list x :=
  match e with
  | ev _ => []
  | ex x => [x]
  | edot e _ => getVarsE e
  end.
Definition getVarsPhi' (phi : phi') : list x :=
  match phi with
  | phiTrue => []
  | phiEq e1 e2 => getVarsE e1 ++ getVarsE e2
  | phiNeq e1 e2 => getVarsE e1 ++ getVarsE e2
  | phiAcc x _ => [x]
  | phiType x _ => [x]
  end.
Definition getVarsPhi (phi : phi) : list x :=
  flat_map getVarsPhi' phi.

(* ASSUMPTIONS *)
Definition mWellDefined (m : method) := 
  match m with Method T' m' pT px c s =>
    match c with Contract pre post =>
      hoare pre s post /\
      sfrmphi [] pre /\
      sfrmphi [] post /\
      (forall x, In x (getVarsPhi pre) -> In x [xUserDef px ; xthis]) /\
      (forall x, In x (getVarsPhi pre) -> In x [xUserDef px ; xthis ; xresult])
    end
  end.
SearchAbout list.
Definition CWellDefined (c : cls) :=
  match c with Cls _ fs ms =>
    (forall m, In m ms -> mWellDefined m) /\
    (forall (f : f) T1 T2, In (Field T1 f) fs -> In (Field T2 f) fs -> T1 = T2)
  end.
Axiom pWellDefined : forall c, In c classes -> CWellDefined c.


(*TEST SCENARIO*)
End Semantics.

Open Scope string.
Definition C1 : C := "Class1".
Definition f1 : f := "f1".
Definition f2 : f := "f2".
Definition m1 : m := "m1".
Definition m2 : m := "m2".
Definition field1 : field := Field (TClass C1) f1.
Definition field2 : field := Field TPrimitiveInt f2.
Definition method1 : field := Field TPrimitiveInt f2.
Definition c1 : cls := Cls C1 [field1 ; field2] [method1].
Definition p : program = Program.



(* PROOF SECTION *)
Notation "'φ'" := phi.
Notation "'ρ'" := rho.

(* determinism? *)

Definition invHeapConsistent
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    forall x o C, rho x = Some (existT _ (TClass C) (v'o C o)) -> 
      exists res fs,
        fields C = Some fs /\
        Heap o = Some (C, res) /\
        (forall (T : T) (f : f), In (T, f) fs -> exists v, res f = Some (existT _ T v))
        .
Definition invPhiHolds
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    evalphi Heap rho A phi.
Definition invTypesHold
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    forall e T, staticType phi e = Some T -> dynamicType Heap rho e = Some T.

Definition invAll
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    invHeapConsistent
      Heap rho A phi /\
    invPhiHolds
      Heap rho A phi /\
    invTypesHold
      Heap rho A phi.

Ltac uninv :=
  unfold invAll in *;
  unfold invHeapConsistent in *;
  unfold invPhiHolds in *;
  unfold invTypesHold in *.

Lemma getTypeImpliesStaticType : forall phi x,
  getType phi x = staticType phi (ex x).
Proof. auto. Qed.

Lemma HnotTotal : forall (H' : H), exists x, H' x = None.
Admitted.

Ltac applyINV1 INV1 H :=
  try auto.

Ltac applyINV2 INV2 H :=
  apply INV2 in H;
  inversion H;
  clear H;
  subst.

Ltac applyINV3 INV3 H :=
  apply INV3 in H;
  unfold dynamicType in H;
  simpl in H.

Ltac inversionx H :=
  inversion H; clear H; subst.

Ltac emagicProgress :=
  repeat eexists;
  econstructor; econstructor;
  unfold evale; simpl; eauto.

Ltac common :=
  repeat match goal with
    | [ H : option_map _ ?T = _ |- _ ] =>
                        destruct T eqn: ?;
                        inversionx H
    | [ H : evale _ _ _ _ |- _ ] => unfold evale in H; simpl in H
  end.

Lemma evalPhiPrefix : forall h r a p1 p2,
   evalphi h r a (p1 ++ p2) -> evalphi h r a p1.
Proof.
  induction p1;
  intros.
  * unfold evalphi.
    intros.
    inversion H1.
  * specialize (IHp1 p2).
    unfold evalphi in *.
    intros.
    inversionx H1.
    + apply H0.
      constructor.
      tauto.
    + apply IHp1 in H2; auto.
      intros.
      apply H0.
      apply in_app_or in H1.
      apply in_or_app.
      inversionx H1; auto.
      constructor.
      apply in_cons.
      auto.
Qed.

Definition soundness : Prop :=
  forall pre s post initialHeap initialRho initialAccess S',
  hoare pre s post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s) :: S') (finalHeap, (finalRho, finalAccess, []) :: S') /\
    invAll finalHeap finalRho finalAccess post.

Lemma HSubstsLeavesUntouched : forall mm o0 o1 C m H,
  o0 <> o1 ->
  H o0 = Some (C, m) ->
  HSubsts o1 mm H o0 = Some (C, m).
Proof.
  unfold HSubsts; 
  induction mm; intros;
  simpl; auto.
  apply IHmm; auto.
  unfold HSubst.
  destruct (o_decb o0 o1) eqn: rec; auto.
  contradict H1.
  unfold o_decb in rec.
  unfold dec2decb in rec.
  destruct (o_dec o0 o1); auto.
  inversion rec.
Qed.

Lemma PropLift : forall (P : execState -> Prop),
  (forall a b, dynSem a b -> P a -> P b) ->
  (forall a b, dynSemStar a b -> P a -> P b).
Proof.
  intros.
  induction H1; try assumption.
  apply IHdynSemStar.
  eapply H0; eauto.
Qed.

Lemma lengthId : forall {A : Type} (a b : list A), a = b -> Datatypes.length a = Datatypes.length b.
Proof.
  intros.
  rewrite H0.
  tauto.
Qed.

Lemma HeapGetsMoreSpecific' : forall s1 s2 (H1 H2 : H) (C : C) m1 (o : o),
  dynSem (H1, s1) (H2, s2) ->
             H1 o = Some (C, m1) ->
  exists m2, H2 o = Some (C, m2).
Proof.
  intros.
  inversion H0; subst;
  try (eexists; eauto; fail).
  - unfold HSubst.
    destruct (o_decb o0 o1) eqn: oe;
    eexists;
    eauto.
    rewrite H3.
    eauto.
  - exists m1.
    unfold Halloc.
    unfold fieldsNames in H9.
    destruct (fields C1); simpl in H9; inversion H9.
    apply HSubstsLeavesUntouched; auto.
    destruct (o_dec o0 o1); auto.
    subst. rewrite H3 in H8.
    inversion H8.
Qed.

Lemma HeapGetsMoreSpecific : forall (C : C) (o : o) m1 s1 s2 (H1 H2 : H),
  dynSemStar (H1, s1) (H2, s2) ->
             H1 o = Some (C, m1) ->
  exists m2, H2 o = Some (C, m2).
Proof.
  specialize (HeapGetsMoreSpecific').
  intro.
  intro.
  intro.
  specialize (PropLift (fun x => exists m1, fst x o0 = Some (C0, m1))).
  intro.
  assert (∀ a b : execState,
      dynSem a b
      → (∃ m1 : f → option v, fst a o0 = Some (C0, m1))
        → ∃ m1 : f → option v, fst b o0 = Some (C0, m1)).
    clear H1.
    intros.
    destruct a, b.
    inversionx H2.
    eapply H0 in H1.
      inversionx H1.
      eexists; eassumption.

      eassumption.
  intuition.
  clear H0 H2.
  specialize (H3 (H1, s1) (H4, s2)).
  intuition.
  apply H0.
  eexists. eassumption.
Qed.

Lemma RhoGetsMoreSpecific' : forall r1 r2 a1 a2 s1 s2 S (H1 H2 : H) v1 (x : x),
  dynSem (H1, (r1, a1, s1) :: S) (H2, (r2, a2, s2) :: S) ->
             r1 x = Some v1 ->
  exists v2, r2 x = Some v2.
Proof.
  intros.
  inversion H0; clear H0; try subst;
  try (eexists; eauto; fail);
  try (unfold rhoSubst, x_decb, dec2decb;
    destruct (x_dec x0 x1); subst; eexists; eauto; fail).
  - unfold rhoSubst, x_decb, dec2decb.
    destruct (x_dec x0 xresult); subst; eexists; eauto.
  - apply lengthId in H13.
    simpl in H13.
    contradict H13.
    auto with arith.
  - apply lengthId in H14.
    simpl in H14.
    contradict H14.
    auto with arith.
Qed.

Lemma RhoGetsMoreSpecific : forall r1 r2 a1 a2 s1 s2 S (H1 H2 : H) v1 (x : x),
  dynSemStar (H1, (r1, a1, s1) :: S) (H2, (r2, a2, s2) :: S) ->
             r1 x = Some v1 ->
  exists v2, r2 x = Some v2.
Proof.
Admitted.

Lemma rhoPhiHelper'' : forall e r x1 x2 v0 o0 C0 H0 z rt v,
  r x1 = Some (vo C0 o0) ->
  r x2 = Some v0 ->
  (∀ x0 : x, In x0 (getVarsE e) → xUserDef z = x0 ∨ xthis = x0) ->
  evale H0 r (eSubsts [(xthis, ex x1); (xUserDef z, ex x2)] e) v ->
  evale H0
    (rhoFrom3 xresult (defaultValue rt) xthis (vo C0 o0) (xUserDef z) v0)
    e v.
Proof.
  unfold evale;
  induction e0; intros; simpl in *.
  - assumption.
  - unfold rhoFrom3.
    unfold x_decb, dec2decb in *.
    destruct (x_dec x0 xthis).
    * subst.
      destruct (x_dec xthis xresult); try inversion e0.
      simpl in H4.
      rewrite H1 in H4.
      assumption.
    * destruct (x_dec x0 (xUserDef z)).
      + subst.
        destruct (x_dec (xUserDef z) xresult); try inversion e0.
        simpl in H4.
        rewrite H2 in H4.
        assumption.
      + specialize (H3 x0).
        intuition.
  - destruct (evale' H0 r (eSubsts [(xthis, ex x1); (xUserDef z, ex x2)] e0)) eqn: eva;
    try (inversion H4; fail).
    destruct v2.
    eapply IHe0 in eva; eauto.
    erewrite eva.
    apply H4.
Qed.

Lemma rhoPhiHelper' : forall r x1 x2 p' z H0 a0 v0 C0 o0 rt,
  r x1 = Some (vo C0 o0) ->
  r x2 = Some v0 ->
  (∀ x0 : x, In x0 (getVarsPhi' p') → xUserDef z = x0 ∨ xthis = x0) ->
  evalphi' H0 r a0 (phi'Substs [(xthis, ex x1); (xUserDef z, ex x2)] p') ->
  evalphi' H0 (rhoFrom3 xresult (defaultValue rt) xthis (vo C0 o0) (xUserDef z) v0) a0 p'.
Proof.
  intros.
  inversionx H4;
  unfold phi'Substs in *.
  - destruct p'; simpl in H9; inversionx H9; try constructor.
    * destruct (x_decb x0 xthis); inversionx H5.
      destruct (x_decb x0 (xUserDef z)); inversionx H6.
    * destruct (x_decb x0 xthis); inversionx H5.
      destruct (x_decb x0 (xUserDef z)); inversionx H6.
  - destruct p'; simpl in H5; inversionx H5; try constructor.
    * econstructor.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold getVarsPhi'. apply in_or_app. auto.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold getVarsPhi'. apply in_or_app. auto.
      + tauto.
    * destruct (x_decb x0 xthis); inversionx H8.
      destruct (x_decb x0 (xUserDef z)); inversionx H5.
    * destruct (x_decb x0 xthis); inversionx H8.
      destruct (x_decb x0 (xUserDef z)); inversionx H5.
  - destruct p'; simpl in H5; inversionx H5; try constructor.
    * econstructor.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold getVarsPhi'. apply in_or_app. auto.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold getVarsPhi'. apply in_or_app. auto.
      + tauto.
    * destruct (x_decb x0 xthis); inversionx H8.
      destruct (x_decb x0 (xUserDef z)); inversionx H5.
    * destruct (x_decb x0 xthis); inversionx H8.
      destruct (x_decb x0 (xUserDef z)); inversionx H5.
  - destruct p'; simpl in H5; inversionx H5; try constructor.
    unfold x_decb, dec2decb in *.
    destruct (x_dec x3 xthis); inversionx H7.
    * econstructor; eauto.
      unfold optionVisO.
      inversion H6.
      exists x0.
      unfold rhoFrom3.
      unfold x_decb, dec2decb in *.
      destruct (x_dec xthis xresult); try inversion e0.
      destruct (x_dec xthis xthis); try (contradict n; tauto).
      rewrite H1 in H4.
      assumption.
    * destruct (x_dec x3 (xUserDef z)); inversionx H5.
      + econstructor; eauto.
        unfold optionVisO.
        inversion H6.
        exists x0.
        unfold rhoFrom3.
        unfold x_decb, dec2decb in *.
        destruct (x_dec (xUserDef z) xresult); try inversion e0.
        destruct (x_dec (xUserDef z) xthis); try inversion e0.
        destruct (x_dec (xUserDef z) (xUserDef z)); try (contradict n2; tauto).
        rewrite H2 in H4.
        assumption.
      + specialize (H3 x3).
        simpl in H3.
        intuition.
    * destruct (x_decb x3 xthis); inversionx H7.
      destruct (x_decb x3 (xUserDef z)); inversionx H5.
  - destruct p'; simpl in H5; inversionx H5.
    * destruct (x_decb x3 xthis); inversionx H6.
      destruct (x_decb x3 (xUserDef z)); inversionx H5.
    * specialize (H3 x3).
      simpl in H3.
      destruct v0.
      unfold vo in *.
      unfold rhoFrom3, x_decb, dec2decb in *.
      destruct (x_dec x3 xthis).
      + inversionx H6.
        destruct (x_dec xthis xresult); try inversion e0.
        rewrite H1 in H9.
        econstructor.
        destruct (x_dec xthis xresult). contradict n. assumption.
        destruct (x_dec xthis xthis). eassumption.
        contradict n1. tauto.
      + destruct (x_dec x3 (xUserDef z)); try intuition.
        subst.
        inversionx H6.
        econstructor.
        destruct (x_dec (xUserDef z) xresult). inversion e0.
        destruct (x_dec (xUserDef z) xthis). inversion e0.
        destruct (x_dec (xUserDef z) (xUserDef z)); try intuition.
        rewrite H2 in H9.
        eassumption.
Qed.

Lemma rhoPhiHelper : forall phi x1 x2 v0 o0 a z C0 rt r H,
  (∀ x : x, In x (getVarsPhi phi) → (xUserDef z) = x ∨ xthis = x) ->
  r x1 = Some (vo C0 o0) ->
  r x2 = Some v0 ->
  evalphi H r a (phiSubsts2 xthis (ex x1) (xUserDef z) (ex x2) phi) ->
  evalphi H (rhoFrom3 xresult (defaultValue rt) xthis (vo C0 o0) (xUserDef z) v0) a phi.
Proof.
  induction phi0; unfold evalphi; intros; inversionx H5.
  - clear IHphi0.
    assert (∀ x0 : x, In x0 (getVarsPhi' p') → (xUserDef z) = x0 ∨ xthis = x0).
      intros.
      apply H1.
      unfold getVarsPhi.
      apply in_flat_map.
      exists p'.
      intuition.
    clear H1.
    assert (evalphi' H0 r a0 (phi'Substs [(xthis, ex x1) ; (xUserDef z, ex x2)] p')).
      apply H4.
      unfold phiSubsts2, phiSubsts.
      apply in_map_iff. eexists. intuition.
    clear H4.
    eapply rhoPhiHelper'; eauto.
  - unfold evalphi in IHphi0.
    eapply IHphi0; eauto; intros.
    * apply (H1 x0).
      unfold getVarsPhi in *.
      apply in_flat_map.
      apply in_flat_map in H5.
      inversionx H5.
      exists x3.
      intuition.
    * apply H4.
      unfold phiSubsts2, phiSubst in *.
      unfold phiSubsts in *.
      apply in_map_iff.
      apply in_map_iff in H5.
      inversionx H5.
      exists x0.
      intuition.
Qed.

Theorem staSemProgress : forall (s'' : s) (s' : list s) (pre post : phi) initialHeap initialRho initialAccess S',
  hoareSingle pre s'' post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s'' :: s') :: S') (finalHeap, (finalRho, finalAccess, s') :: S')
.
  destruct s'';
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro HO;
  intro INV;

  uninv;
  inversion HO; clear HO; subst;

  inversion INV as [INV1 INVx]; clear INV;
  inversion INVx as [INV2 INV3]; clear INVx;
  try rewrite getTypeImpliesStaticType in *.
  - applyINV2 INV2 H8.
    applyINV2 INV2 H9.
    applyINV3 INV3 H3.
    applyINV3 INV3 H6.

    common.
    rewrite H2 in *.
    inversionx Heqo0.
    inversionx H10.
    inversionx H0.
    simpl in *.
    inversionx H1.
    inversionx H12.

    emagicProgress.

  - applyINV3 INV3 H2.
    applyINV3 INV3 H3.
    common.

    emagicProgress.

  - specialize (HnotTotal initialHeap). intros.
    inversionx H0.
    unfold fieldsNames in H5.
    destruct (fields c) eqn: fi; simpl in H5; inversionx H5.
    emagicProgress.
  - applyINV2 INV2 H7.
    applyINV3 INV3 H4.
    applyINV3 INV3 H5.
    applyINV3 INV3 H6.
    common.
    rewrite H2 in *.
    inversionx Heqo2.
    inversionx H15.

    destruct v2. simpl in *. subst.
    destruct v2. contradict H16. auto.

    assert (H1 := H2).
    apply INV1 in H1.
    inversionx H1.
    inversionx H0.
    inversionx H1.
    inversionx H3.

    (*get method*)
    unfold mparam in H12.
    destruct (mmethod C0 m0) eqn: mm; simpl in *; inversionx H12.
    destruct m1.
    inversionx H5.

    (*well def*)
    remember (Method t m1 (projT1 v0) z c l) as m2.
    assert (mm2 := mm).
    unfold mmethod in mm2.
    destruct (class C0) eqn: cc; try (inversion mm2; fail).
    specialize (pWellDefined c0). intros.
    unfold class in cc.
    apply find_some in cc.
    inversionx cc.
    destruct c0.
    unfold C_decb, string_decb, dec2decb in H6.
    destruct (string_dec c0 C0); inversionx H6.
    apply H3 in H5. clear H3.
    apply find_some in mm2.
    inversionx mm2.
    unfold m_decb, string_decb, dec2decb in H6.
    destruct (string_dec m1 m0); inversionx H6.
    unfold CWellDefined in H5.
    inversionx H5.
    apply H6 in H3. clear H6.
    unfold mWellDefined in H3.
    destruct c.
    intuition.
    rename H11 into varsPre.
    rename H13 into varsPost.
    
    (*unify method knowledge*)
    unfold mpre, mpost, mcontract in *.
    rewrite mm in *. simpl in *.
    inversionx H9.
    inversionx H10.

    remember (projT1 v1) as ret_type.
    remember (rhoFrom3 xresult (defaultValue ret_type) xthis (vo C0 o0) (xUserDef z) v0) as r'.
    remember (footprint initialHeap r' phi_pre) as fp.

    (*proof strategy*)
    assert (forall a b c d, dynSem a b -> dynSemStar b c -> dynSem c d -> dynSemStar a d)
           as strat.
      intros.
      econstructor; eauto.
      eapply dynSemStarBack; eauto.

    (*Part 1: make the call*)
    assert (dynSem 
              (initialHeap, (initialRho, initialAccess, sCall x0 x1 m0 x2 :: s') :: S')
              (initialHeap, (r', fp, l) :: (initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s') :: S')
           ).
      econstructor; unfold evale; simpl; eauto.
        unfold mbody.
        rewrite mm. simpl.
        eauto.

        unfold mparam.
        rewrite mm. simpl.
        eauto.

        unfold mpre.
        unfold mcontract.
        rewrite mm. simpl.
        eauto.

        clear INV1 INV3.
        unfold phiImplies in H8.
        apply H8 in INV2. clear H8.
        apply evalPhiPrefix in INV2.
        rewrite Heqr'.
        eapply rhoPhiHelper; eauto.
        intros.
        specialize (varsPre x5).
        intuition.

    (*Part 2: method body (assumes soundness, termination, ... for method body)*)
    assert soundness as sdn. admit.
    unfold soundness in sdn.
    remember ((initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s') :: S') as S''.
    specialize (sdn phi_pre l phi_post initialHeap r' fp S'').
    apply sdn in H5. clear sdn.
    inversion H5; clear H5.
    inversion H10; clear H10.
    inversion H5; clear H5.
    inversion H10; clear H10.
    Focus 2.
      admit. (*that follows from preservation proof of Part 1!*)

    (*Part 3: call finish*)
    assert (exists initialRh', dynSem
              (x5, (x6, x7, []) :: (initialRho, Aexcept initialAccess fp , sCall x0 x1 m0 x2 :: s') :: S')
              (x5,                 (initialRh', Aexcept initialAccess fp ++ footprint x5 x6 phi_post, s') :: S')
           ).
      assert (dss := H5).

      (*heap*)
      eapply HeapGetsMoreSpecific in H5; try eassumption.
      inversion H5; clear H5.

      (*rho*)
      eapply RhoGetsMoreSpecific in dss.
      Focus 2.
        instantiate (2 := xresult).
        rewrite Heqr'.
        unfold rhoFrom3, x_decb, dec2decb.
        simpl. eauto.
      inversion dss; clear dss.

      eexists. econstructor; eauto.
        unfold mpost, mcontract.
        rewrite mm. simpl. tauto.

        uninv. apply H11.
    inversion H10; clear H10.
    
    (*marriage*)
    subst.
    repeat eexists.
    eapply strat; eauto.
  - applyINV3 INV3 H1.
    common.
    emagicProgress.
  - emagicProgress.
  - emagicProgress.
    unfold phiImplies in H1.
    apply H1 in INV2.
    unfold evalphi in INV2.
    apply INV2.
    constructor.
    tauto.
  - emagicProgress.
Proof.


Theorem staSemSoundness : forall (s'' : s) (s' : list s) (pre post : phi) initialHeap initialRho initialAccess S',
  hoareSingle pre s'' post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s'' :: s') :: S') (finalHeap, (finalRho, finalAccess, s') :: S') /\
    invAll finalHeap finalRho finalAccess post
.
  destruct s'';
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro HO;
  intro INV;

  uninv;
  inversion HO; clear HO; subst;

  inversion INV as [INV1 INVx]; clear INV;
  inversion INVx as [INV2 INV3]; clear INVx;
  try rewrite getTypeImpliesStaticType in *.
  - applyINV2 INV2 H8.
    applyINV2 INV2 H9.
    applyINV3 INV3 H3.
    applyINV3 INV3 H6.

    common.
    rewrite H2 in *.
    inversionx Heqo0.
    inversionx H10.
    inversionx H0.
    simpl in *.
    inversionx H1.
    inversionx H12.
    clear H13.
    destruct v0.
    simpl in *.

    do 3 eexists.
    constructor;
    try (econstructor; econstructor; unfold evale; simpl; eauto; fail).

    (*PRESERVATION*)
    intuition.
    * destruct (o_dec o0 o1).
      + subst.
        assert (C0 = C1).
          apply INV1 in H0.
          apply INV1 in H2.
          inversionx H0.
          inversionx H1.
          inversionx H2.
          inversionx H1.
          intuition.
          rewrite H2 in H3.
          inversion H3.
          tauto.
        subst.
        apply INV1 in H0. inversionx H0. inversionx H1.
        exists (fun f => if f_decb f f0 then Some (existT v' x2 v0) else x4 f).
        exists x5.
        intuition.
          unfold HSubst.
          unfold o_decb, f_decb, dec2decb.
          destruct (o_dec o1 o1); try (contradict n; tauto).
          rewrite H0.
          tauto.

          unfold f_decb, string_decb, dec2decb in *.
          destruct (string_dec f1 f0).
            subst.
            unfold fieldType in H4.
            unfold fields in H1.
            destruct (class C1) eqn: cc; try (inversion H1; fail).
            destruct c.
            common.
            apply find_some in Heqo0.
            destruct f1.
            inversionx Heqo0.
            unfold f_decb, string_decb, dec2decb in *.
            destruct (string_dec f1 f0); inversionx H6.
            subst.
            inversionx H1.
            apply in_map_iff in H3.
            inversionx H3.
            inversionx H1.
            destruct x2.
            inversionx H3.
            specialize (pWellDefined (Cls c l l0)).
            intros.
            unfold class in cc.
            apply find_some in cc.
            intuition.
            unfold C_decb, string_decb, dec2decb in *.
            destruct (string_dec c C1); inversionx H7.
            unfold CWellDefined in H8.
            intuition.
            eapply H7 in H4; eauto.
            subst.
            exists v0.
            tauto.

            apply H5 in H3.
            inversionx H3.
            eexists. eauto.
      + apply INV1 in H0.
        inversionx H0.
        inversionx H1.
        intuition.
        exists x4.
        exists x5.
        intuition.
        unfold HSubst.
        unfold o_decb, dec2decb.
        destruct (o_dec o1 o0); intuition.
    * unfold evalphi in *.
      intros. specialize (INV2 p').
      unfold appEnd in *.
      apply in_app_iff in H0.
      inversionx H0.
      + intuition.
        
Proof.


Lemma phiImpliesRefl : forall x, phiImplies x x.
Proof.
  unfold phiImplies.
  auto.
Qed.
Hint Resolve phiImpliesRefl.

Lemma AexceptReverse : forall a1 a2, Aexcept (a1 ++ a2) a2 = a1.
Admitted.

Lemma evalPhiImplies : forall H' r A' q1 q2,
  phiImplies q1 q2 -> evalphi H' r A' q1 -> evalphi H' r A' q2.
Proof.
  intros.
  unfold phiImplies in H0.
  specialize (H0 H' r A').
  intuition.
Qed.

Lemma InAexcept : forall x a a', In x (Aexcept a a') -> In x a.
Proof.
  unfold Aexcept.
  unfold except.
  induction a; intros.
  - compute in H0.
    inversion H0.
  - simpl.
    simpl filter in H0.
    destruct (existsb (A_d'_decb a) a'); simpl in H0.
    * apply IHa in H0.
      auto.
    * inversion H0; auto.
      apply IHa in H1.
      auto.
Qed.

Lemma mapSplitFst : forall {A B : Type} (x : list (A * B)), map fst x = fst (split x).
Admitted.
Lemma mapSplitSnd : forall {A B : Type} (x : list (A * B)), map snd x = snd (split x).
Admitted.

(*
Lemma phiTrueSubst : forall a b p, phiTrue = phiSubst a b p -> p = phiTrue.
Proof.
  intros.
  destruct p; auto;
  unfold phiSubst in H0; inversion H0.
Qed.
Lemma phiTrueSubsts : forall a p, phiTrue = phiSubsts a p -> p = phiTrue.
Proof.
  induction a; intros.
  - simpl in H0.
    auto.
  - simpl in H0.
    apply IHa in H0.
    symmetry in H0.
    apply phiTrueSubst in H0.
    assumption.
Qed.
Lemma phiEqSubsts : forall a p e1 e2, phiEq e1 e2 = phiSubsts a p -> exists e1' e2', p = phiEq e1' e2' /\ e1 = eSubsts a e1' /\ e2 = eSubsts a e2'.
Proof.
  induction a; intros.
  - repeat eexists.
    simpl in H0.
    subst.
    auto.
  - simpl in H0.
    apply IHa in H0.
    inversion H0; clear H0.
    inversion H1; clear H1.
    intuition.
    subst.
    destruct p; simpl in H1; inversion H1.
    repeat eexists.
    * admit.
    * admit.
Admitted.

Lemma eSubstsVal : forall x v, eSubsts x (ev v) = (ev v).
Proof.
  induction x0; intros.
  - simpl; tauto.
  - specialize (IHx0 v0).
    assert (eSubsts (a :: x0) (ev v0) = eSubsts x0 (ev v0)).
    * admit.
    * rewrite IHx0 in H0.
      assumption.
Admitted.

Lemma phiImpliesConj : forall a b c, phiImplies a (phiConj b c) -> phiImplies a b.
Admitted.*)

Ltac tmp := repeat eexists; econstructor; econstructor; eauto.
Ltac unfWT := 
  unfold wellTyped in *;
  unfold wellTypedPhi in *;
  unfold wellTypedE in *;
  simpl getType in *.

Lemma evaleTClass : forall G e' C' h r, getType G e' = Some (TClass C') -> (let res := evale h r e' in res = Some vnull \/ exists o', res = Some (vo o')).
Admitted. (* TODO: entangle *)

Definition consistent (H' : H) (r : rho) := forall x' o' res, r x' = Some (vo o') -> H' o' = Some res.

Lemma exists_forall : forall {A : Type} (b : A -> Prop) (c : Prop), ((exists a, b a) -> c) -> (forall a, b a -> c).
Proof.
  intros.
  apply H0.
  eauto.
Qed.
  

Lemma rhoVSeSubst : forall e'' e''' h r e' x' v', 
 evale h r e' = Some v' ->
 eSubst x' e' e'' = e''' ->
  evale h (rhoSubst x' v' r) e'' =
  evale h r e'''.
Proof.
  induction e''; intros; subst.
  - simpl. auto.
  - simpl eSubst. simpl. unfold rhoSubst.
    case_eq (x_decb x0 x'); intros; simpl; try tauto.
    rewrite H0.
    tauto.
Qed.

Lemma rhoVSphiSubst1 : forall e'' e''' h r e' x' v' a, 
 evale h r e' = Some v' ->
 phi'Subst x' e' e'' = e''' ->
  (evalphi' h (rhoSubst x' v' r) a e'' ->
  evalphi' h r a e''').
Proof.
  induction e''; intros; subst; intros; try constructor; simpl in *.
  - inversion H2; clear H2; subst.
    econstructor.
    * erewrite rhoVSeSubst in H4; eauto.
    * erewrite rhoVSeSubst in H8; eauto.
    * tauto.
  - inversion H2; clear H2; subst.
    econstructor.
    * erewrite rhoVSeSubst in H4; eauto.
    * erewrite rhoVSeSubst in H8; eauto.
    * tauto.
  - inversion H2; clear H2; subst.
    econstructor.
    * erewrite rhoVSeSubst in H7; eauto.
    * tauto.
Qed.
Lemma rhoVSphiSubst2 : forall e'' e''' h r e' x' v' a, 
 evale h r e' = Some v' ->
 phi'Subst x' e' e'' = e''' ->
  (evalphi' h r a e''' ->
  evalphi' h (rhoSubst x' v' r) a e'').
Proof.
  induction e''; intros; subst; intros; try constructor; simpl in *.
  - inversion H2; clear H2; subst.
    specialize (rhoVSeSubst e0 (eSubst x' e' e0) h r e' x' v').
    intros.
    specialize (rhoVSeSubst e1 (eSubst x' e' e1) h r e' x' v').
    intros.
    intuition.
    rewrite H8, H4 in *.
    econstructor; eauto.
  - inversion H2; clear H2; subst.
    specialize (rhoVSeSubst e0 (eSubst x' e' e0) h r e' x' v').
    intros.
    specialize (rhoVSeSubst e1 (eSubst x' e' e1) h r e' x' v').
    intros.
    intuition.
    rewrite H8, H4 in *.
    econstructor; eauto.
  - inversion H2; clear H2; subst.
    specialize (rhoVSeSubst e0 (eSubst x' e' e0) h r e' x' v').
    intros.
    intuition.
    rewrite H7 in *.
    econstructor; eauto.
Qed.


(* playground *)
Open Scope string_scope.

Notation "AA '⊢sfrme' ee" := (sfrme AA ee) (at level 90).

Print sfrme.
Print dynSem.

Notation "classes 'main:' main" := (Program classes main) (at level 100).
Notation "'class' c { fs ms }" := (Cls c fs ms).

Check (Cls "a" [] []).



