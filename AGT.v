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

(**Helpers (probably out there but I was too stupid to find)**)
Definition obind {t u : Type} (a : option t) (b : t -> option u) : option u := 
match a with
| None => None
| Some x => b x
end.

Ltac unfeq := unfold equiv_decb, equiv_dec in *.

(**Types**)
Inductive primitive_type : Set :=
| Int : primitive_type
| Bool : primitive_type.
Definition primitive_type_dec : ∀ n m : primitive_type, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance primitive_type_EqDec : EqDec primitive_type eq := primitive_type_dec.
Hint Resolve primitive_type_dec.

Inductive type_leaf : Set :=
| TPrim : primitive_type -> type_leaf.
Definition type_leaf_dec : ∀ n m : type_leaf, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance type_leaf_EqDec : EqDec type_leaf eq := type_leaf_dec.
Hint Resolve type_leaf_dec.

Inductive gtype_leaf : Set :=
| GPrim : primitive_type -> gtype_leaf
| GUnk : gtype_leaf.
Definition gtype_leaf_dec : ∀ n m : gtype_leaf, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance gtype_leaf_EqDec : EqDec gtype_leaf eq := gtype_leaf_dec.
Hint Resolve gtype_leaf_dec.

Inductive unk_leaf_type (TLeaf : Set) : Type :=
| Leaf : TLeaf -> unk_leaf_type TLeaf
| Func : unk_leaf_type TLeaf -> unk_leaf_type TLeaf -> unk_leaf_type TLeaf.

Definition type := unk_leaf_type type_leaf.
Definition type_dec : ∀ n m : type, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance type_EqDec : EqDec type eq := type_dec.
Hint Resolve type_dec.
Hint Unfold type_EqDec.

Definition gtype := unk_leaf_type gtype_leaf.
Definition gtype_dec : ∀ n m : gtype, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance gtype_EqDec : EqDec gtype eq := gtype_dec.

Definition ptype := type -> bool.

(*convenience*)
Definition TLeaf := Leaf type_leaf.
Definition TFunc := Func type_leaf.
Definition TPrimitive := fun x => TLeaf (TPrim x).
Definition TInt := TPrimitive Int.
Definition TBool := TPrimitive Bool.

Definition GLeaf := Leaf gtype_leaf.
Definition GFunc := Func gtype_leaf.
Definition GPrimitive := fun x => GLeaf (GPrim x).
Definition GInt := GPrimitive Int.
Definition GBool := GPrimitive Bool.
Definition GUnknown := GLeaf GUnk.

Definition PEmpty : ptype := fun t => false.
Definition PTotal : ptype := fun t => true.
Definition PSingleton (t' : type) : ptype := fun t => t' ==b t.
Definition PLift (a b : ptype) : ptype := fun t =>
match t with
| Func _ a' b' => andb (a a') (b b')
| _ => false
end.
Definition PisEmpty (pt : ptype) := forall t, pt t = PEmpty t.
Definition PisTotal (pt : ptype) := forall t, pt t = PTotal t.
Definition PisSingleton (pt : ptype) (t' : type) := forall t, pt t = PSingleton t' t.
Definition PisLift (pt : ptype) (a b : ptype) := forall t, pt t = PLift a b t.

Lemma ptSingleton : forall x t, PSingleton t x = true <-> t = x.
Proof.
  split; intros.
  - unfold PSingleton in H.
    unfeq.
    destruct (type_EqDec t x).
    auto.
    inversion H.
  - rewrite H.
    unfold PSingleton.
    unfeq.
    destruct (type_EqDec x x); intuition.
Qed.

(**Operations**)
Definition dom {a : Set} (t : unk_leaf_type a) : option (unk_leaf_type a) := match t with
| Leaf _ _ => None
| Func _ a _ => Some a
end.
Definition cod {a : Set} (t : unk_leaf_type a) : option (unk_leaf_type a) := match t with
| Leaf _ _ => None
| Func _ _ a => Some a
end.

Definition tequate (a b : type) : option type := if a == b then Some a else None.

Fixpoint gequate (a b : gtype) : option gtype := match (a, b) with
| (Leaf _ GUnk, _) => Some a
| (_, Leaf _ GUnk) => Some b
| (Func _ a1 b1, Func _ a2 b2) => obind (gequate a1 a2) (fun a => 
                                  obind (gequate b1 b2) (fun b => Some (Func gtype_leaf a b)))
| (x, y) => if x == y then Some x else None
end.


(**Other Relations**)
(*Consistency on types (tilde)*)
Inductive class_gtype_cons : gtype -> gtype -> Prop :=
| GTypeConsRefl : forall t, class_gtype_cons t t
| GTypeConsUL : forall t, class_gtype_cons GUnknown t
| GTypeConsUR : forall t, class_gtype_cons t GUnknown
| GTypeConsAbs : forall t11 t12 t21 t22, 
  class_gtype_cons t11 t21 ->
  class_gtype_cons t12 t22 ->
  class_gtype_cons (GFunc t11 t12) (GFunc t21 t22).

Theorem class_gtype_cons1 :
(class_gtype_cons
   (GFunc (GPrimitive Int) GUnknown)
   (GFunc GUnknown (GPrimitive Bool))).
Proof.
  apply GTypeConsAbs.
  apply GTypeConsUR.
  apply GTypeConsUL.
Qed.

Theorem class_gtype_cons2 :
~ (class_gtype_cons
   (GFunc (GPrimitive Int) (GPrimitive Int))
   (GFunc (GPrimitive Int) (GPrimitive Bool))).
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H5.
Qed.

(*naive subtyping relation (<:)*)
Inductive class_gsubt : gtype -> gtype -> Prop :=
| SubtUnknown : forall t, class_gsubt t GUnknown
| SubtRefl : forall t, class_gsubt t t
| SubtLift : forall t11 t12 t21 t22, 
  class_gsubt t11 t21 -> class_gsubt t12 t22 -> class_gsubt (GFunc t11 t12) (GFunc t21 t22)
.


(**TFL**)
Definition tfl_Var := string.
Inductive tfl_t (tfl_T : Set) : Set :=
| TflTermNat : nat -> tfl_t tfl_T
| TflTermBool : bool -> tfl_t tfl_T
| TflTermVar : tfl_Var -> tfl_t tfl_T
| TflTermAbs : tfl_Var -> tfl_T -> tfl_t tfl_T -> tfl_t tfl_T
| TflTermApp : tfl_t tfl_T -> tfl_t tfl_T -> tfl_t tfl_T
| TflTermPlus : tfl_t tfl_T -> tfl_t tfl_T -> tfl_t tfl_T
| TflTermIf : tfl_t tfl_T -> tfl_t tfl_T -> tfl_t tfl_T -> tfl_t tfl_T
| TflTermAssert : tfl_t tfl_T -> tfl_T -> tfl_t tfl_T.

Definition tfl_T_context (tfl_T : Set) := tfl_Var -> option tfl_T.

Definition tfl_Var_decb (a : tfl_Var) (b : tfl_Var) : bool := 
  if string_dec a b then true else false.

Definition tfl_T_context_empty (tfl_T : Set) : tfl_T_context tfl_T := fun x' => None.
Definition tfl_T_context_set (tfl_T : Set) (x : tfl_Var) (t : tfl_T) (c : tfl_T_context tfl_T) : tfl_T_context tfl_T :=
  fun x' => if string_dec x x' then Some t else c x'.

Check (fun (a b : tfl_t type) => a = b).

Inductive tfl_term_type 
  (t_leaf : Set) 
  (mk_prim : primitive_type -> unk_leaf_type t_leaf)
  (cons : unk_leaf_type t_leaf → unk_leaf_type t_leaf → Prop)
  (equate : unk_leaf_type t_leaf → unk_leaf_type t_leaf → option (unk_leaf_type t_leaf))
   : tfl_T_context (unk_leaf_type t_leaf) -> tfl_t (unk_leaf_type t_leaf) -> (unk_leaf_type t_leaf) -> Prop :=
| TflTx : forall (c : tfl_T_context (unk_leaf_type t_leaf)) x t, 
    c x t -> tfl_term_type t_leaf mk_prim cons equate c (TflTermVar (unk_leaf_type t_leaf) x) t
| TflTn : forall c n, 
    tfl_term_type t_leaf mk_prim cons equate c (TflTermNat (unk_leaf_type t_leaf) n) (mk_prim Int)
| TflTb : forall c b, 
    tfl_term_type t_leaf mk_prim cons equate c (TflTermBool (unk_leaf_type t_leaf) b) (mk_prim Bool)
| TflTapp : forall c t1 tt1 t2 tt2 ttx,
    tfl_term_type t_leaf mk_prim cons equate c t1 tt1 ->
    tfl_term_type t_leaf mk_prim cons equate c t2 tt2 ->
    dom tt1 = Some tt2 ->
    cod tt1 = Some ttx ->
    tfl_term_type t_leaf mk_prim cons equate c (TflTermApp (unk_leaf_type t_leaf) t1 t2) ttx
| TflTplus : forall c t1 tt1 t2 tt2,
    tfl_term_type t_leaf mk_prim cons equate c t1 tt1 ->
    tfl_term_type t_leaf mk_prim cons equate c t2 tt2 ->
    cons tt1 (mk_prim Int) ->
    cons tt2 (mk_prim Int) ->
    tfl_term_type t_leaf mk_prim cons equate c (TflTermPlus (unk_leaf_type t_leaf) t1 t2) (mk_prim Int)
| TflTif : forall c t1 tt1 t2 tt2 t3 tt3 ttx,
    tfl_term_type t_leaf mk_prim cons equate c t1 tt1 ->
    tfl_term_type t_leaf mk_prim cons equate c t2 tt2 ->
    tfl_term_type t_leaf mk_prim cons equate c t3 tt3 ->
    cons tt1 (mk_prim Bool) ->
    equate tt2 tt3 = Some ttx ->
    tfl_term_type t_leaf mk_prim cons equate c (TflTermIf (unk_leaf_type t_leaf) t1 t2 t3) ttx
| TflTlambda : forall (c : tfl_T_context (unk_leaf_type t_leaf)) t tt1 tt2 (x : tfl_Var),
    tfl_term_type t_leaf mk_prim cons equate (tfl_T_context_set (unk_leaf_type t_leaf) x tt1 c) t tt2 ->
    tfl_term_type t_leaf mk_prim cons equate c (TflTermAbs (unk_leaf_type t_leaf) x tt1 t) (Func t_leaf tt1 tt2)
| TflTassert : forall c t tt tt1,
    tfl_term_type t_leaf mk_prim cons equate c t tt ->
    cons tt tt1 ->
    tfl_term_type t_leaf mk_prim cons equate c (TflTermAssert (unk_leaf_type t_leaf) t tt1) tt1
.

(*STFL*)
Definition stfl_T := type.
Definition stfl_Tcons := fun (a b : stfl_T) => a = b.
Definition stfl_t : Set := tfl_t stfl_T.
Definition stfl_T_context := tfl_T_context stfl_T.

Definition stfl_term_type := tfl_term_type type_leaf TPrimitive stfl_Tcons tequate.

(*GTFL*)
Definition gtfl_T := gtype.
Definition gtfl_Tcons := class_gtype_cons.
Definition gtfl_t : Set := tfl_t gtfl_T.
Definition gtfl_T_context := tfl_T_context gtfl_T.

Definition gtfl_term_type := tfl_term_type gtype_leaf GPrimitive gtfl_Tcons gequate.



(*subset*)
Definition ptSpt (a b : ptype) : Prop := forall x, (a x) = true -> (b x) = true.

Theorem ptSptRefl : forall a, ptSpt a a.
Proof.
  compute.
  intuition.
Qed.
Theorem ptSptTotal : forall a, ptSpt a PTotal.
Proof.
  compute.
  intuition.
Qed.
Theorem ptSptEmpty : forall a, ptSpt PEmpty a.
Proof.
  compute.
  intuition.
Qed.
Theorem ptSptFuncLift : forall t11 t12 t21 t22,
  ptSpt t11 t12 -> ptSpt t21 t22 -> ptSpt (PLift t11 t21) (PLift t12 t22).
Proof.
  compute.
  intuition.
  induction x; intuition.
  specialize (H x1).
  specialize (H0 x2).
  destruct (t11 x1); intuition.
  rewrite H2, H0 in *. 
  auto.
Qed.

(*Definition 1 - Concretization (gamma)*)
Fixpoint gt2pt (t : gtype) : ptype := match t with
| Leaf _ GUnk => PTotal
| Leaf _ (GPrim pt) => PSingleton (TPrimitive pt)
| Func _ a b => PLift (gt2pt a) (gt2pt b)
end.

(*lift type*)
Fixpoint t2gt (t : type) : gtype := match t with
| Leaf _ (TPrim pt) => GPrimitive pt
| Func _ a b => GFunc (t2gt a) (t2gt b)
end.
Definition t2pt (t : type) : ptype := PSingleton t.

(*Definition 2 - Type Precision (\sqsubseteq)*)
Definition gtSgt (a : gtype) (b : gtype) : Prop := ptSpt (gt2pt a) (gt2pt b).

(*Definition 3 - Predicate Lifting*)
Definition plift (pred : type -> type -> Prop) (a b : ptype) : Prop :=
exists a' b', pred a' b' /\ a a' = true /\ b b' = true.
Definition glift (pred : type -> type -> Prop) (a b : gtype) : Prop :=
plift pred (gt2pt a) (gt2pt b).

(*Definition 4 - Collecting Function*)
Definition pliftF (f : type -> option type) (a b : ptype) : Prop :=
forall b', b b' = true <-> exists a', a a' = true /\ f a' = Some b'.

(*Definition 5 - alpha*)
Definition pt2gtSingleton (t : ptype) (t' : type) (p : PisSingleton t t') : gtype := t2gt t'.
Inductive pt2gt : ptype -> gtype -> Prop :=
| PGSingleton : forall t t', PisSingleton t t' -> pt2gt t (t2gt t')
| PGLift : forall t, ~ PisEmpty t -> forall a b, PisLift t a b -> forall a', pt2gt a a' -> forall b', pt2gt b b' -> pt2gt t (GFunc a' b')
| PGTotal : forall t, ~ PisEmpty t -> 
(forall t', ~ PisSingleton t t') -> 
(forall a b, ~ PisLift t a b) -> 
pt2gt t GUnknown
.

(*TACTIC*)
Ltac unfConv :=
  unfold TInt in *;
  unfold TBool in *;
  unfold TPrimitive in *;
  unfold TFunc in *;
  unfold TLeaf in *;
  unfold GUnknown in *;
  unfold GInt in *;
  unfold GBool in *;
  unfold GPrimitive in *;
  unfold GFunc in *;
  unfold GLeaf in *;
  unfold PLift in *;
  unfold PSingleton in *;
  unfold PTotal in *;
  unfold PEmpty in *.
Ltac fConv :=
  fold TInt in *;
  fold TBool in *;
  fold TPrimitive in *;
  fold TFunc in *;
  fold TLeaf in *;
  fold GUnknown in *;
  fold GInt in *;
  fold GBool in *;
  fold GPrimitive in *;
  fold GFunc in *;
  fold GLeaf in *;
  fold PLift in *;
  fold PSingleton in *;
  fold PTotal in *;
  fold PEmpty in *.

Ltac unf :=
  unfConv;
  try (unfold t2pt in *);
  try (unfold gtSgt in *);
  try (unfold ptSpt in *);
  try (unfold gt2pt in *);
  unfConv;
  unfeq;
  try (unfold type_EqDec in *);
  try (unfold gtype_EqDec in *)
.
Ltac unf2 :=
  unfConv;
  try (unfold t2pt in *);
  try (unfold gtSgt in *);
  try (unfold ptSpt in *);
  unfConv;
  unfeq;
  try (unfold type_EqDec in *);
  try (unfold gtype_EqDec in *)
.

Theorem PSPmembership : forall t pt,
  ptSpt (t2pt t) pt <-> pt t = true.
Proof.
  intuition.
  - unfold ptSpt in H.
    specialize (H t).
    assert (t2pt t t = true).
    unf.
    destruct (type_dec t t); auto.
    auto.
  - unfold ptSpt.
    intros.
    unfold t2pt in H0.
    apply ptSingleton in H0.
    rewrite H0 in *. auto.
Qed.

Ltac un_type_dec := destruct (type_dec _ _); auto; try congruence; try intuition.

Ltac helpTac := 
  unfold gtSgt, gt2pt;
  split;
  intros;
  try inversion H;
  try apply SubtRefl;
  try apply SubtUnknown;
  try apply ptSptRefl;
  try apply ptSptTotal.

Lemma gt2ptPrimitive : forall p, gt2pt (GPrimitive p) (TPrimitive p) = true.
Proof.
  intros.
  unf.
  un_type_dec.
Qed.
Lemma gt2ptUnknown : forall x, gt2pt GUnknown x = true.
Proof.
  intros.
  unf.
  auto.
Qed.
Lemma gt2ptId : forall a, gt2pt (t2gt a) a = true.
Proof.
  induction a; simpl t2gt.
  - destruct t.
    apply gt2ptPrimitive.
  - unf2. simpl gt2pt in *.
    intuition.
Qed.
Lemma gt2ptIdNot : forall a b, gt2pt (t2gt a) b = false <-> a <> b.
Proof.
  induction a; simpl t2gt; split; intros.
  - destruct t, b.
    * destruct t.
      destruct p, p0; intuition; inversion H0.
    * intuition. inversion H0.
  - destruct t, b; try intuition.
    * destruct t.
      destruct p, p0; intuition; inversion H0.
  - destruct b; try intuition; try inversion H0.
    rewrite H2 in *.
    rewrite H3 in *.
    clear H2 H3 a1 a2 H0.
    simpl gt2pt in H.
    assert (gt2pt (t2gt b1) b1 = true). apply gt2ptId.
    assert (gt2pt (t2gt b2) b2 = true). apply gt2ptId.
    rewrite H0 in H.
    rewrite H1 in H.
    intuition.
  - destruct b; try intuition.
    simpl gt2pt in *.
    apply andb_false_iff.
    specialize (IHa1 b1).
    specialize (IHa2 b2).
    rewrite IHa1.
    rewrite IHa2.
    clear IHa1 IHa2.
    destruct (a1 == b1).
    * rewrite e in *.
      destruct (a2 == b2).
      rewrite e0 in *; intuition.
      assert (a2 = b2 → False).
      intuition.
      intuition.
    * assert (a1 = b1 → False).
      intuition.
      intuition.
Qed.
Lemma gt2ptFail1 : forall x a b, gt2pt (GPrimitive x) (TFunc a b) = false.
Proof.
  intros.
  unf.
  auto.
Qed.
Lemma gt2ptFail2 : forall x a b, gt2pt (GFunc a b) (TPrimitive x) = false.
Proof.
  intros.
  unf.
  auto.
Qed.

Lemma gtHas : forall gt, exists t, gt2pt gt t = true.
Proof.
  intros.
  induction gt.
  - destruct t.
    * exists (TPrimitive p). unf. un_type_dec.
    * exists TInt. unf. auto.
  - elim IHgt1. intros.
    elim IHgt2. intros.
    exists (TFunc x x0).
    unf2.
    unfold gt2pt.
    fold gt2pt.
    unfold PLift.
    intuition.
Qed.

Lemma gtSgtUnknown : forall x, gtSgt x GUnknown.
Proof.
  intros.
  unf2.
  intros.
  apply gt2ptUnknown.
Qed.

Lemma gtSgtRefl : forall x, gtSgt x x.
Proof.
  intros.
  unf2.
  intros.
  auto.
Qed.

Lemma gtSgtLift : forall a1 b1 a2 b2, gtSgt (GFunc a1 b1) (GFunc a2 b2) -> gtSgt a1 a2 /\ gtSgt b1 b2.
Proof.
  induction a1, b1, a2, b2; 
  intros; split; fConv.
  - induction g0; try apply gtSgtUnknown.
    assert (t = GPrim p).
    unf2. fConv.
    destruct t.
    specialize (gtHas (GLeaf g)); intros. elim H0; intros.
    specialize (H (TFunc (TPrimitive p0) x)); unf2. fConv.
    assert (gt2pt (GFunc (GLeaf (GPrim p0)) (GLeaf g)) (TFunc (TLeaf (TPrim p0)) x) = true).
    simpl gt2pt in *.
    rewrite H1.
    unf2. un_type_dec.
    intuition.
    simpl gt2pt in *.
    assert (PSingleton (TPrimitive p) (TLeaf (TPrim p0)) = true).
Admitted.

(*Proposition 1 - Type Precision == naive subtyping relation*)
Theorem typePrecision : forall t1 t2, gtSgt t1 t2 <-> class_gsubt t1 t2.
Proof.
  induction t1, t2.
  - destruct t, g; unf; split; intros; try constructor.
    * specialize (H (TPrimitive p)).
      un_type_dec.
      un_type_dec.
      inversion e0.
      constructor.
    * inversion H.
      rewrite H3 in *. assumption.
    * specialize (H (TFunc (TPrimitive p) (TPrimitive p))).
      intuition.
    * inversion H.
  - split; intros; try inversion H.
    unf2.
    destruct t.
    * specialize (H (TPrimitive p)).
      specialize (gt2ptPrimitive p).
      intros.
      intuition.
    * specialize (H TInt).
      specialize (gt2ptUnknown TInt).
      intros.
      intuition.
  - split; intros; try inversion H.
    unf2.
    destruct g; try constructor.
    specialize (gtHas (Func gtype_leaf t1_1 t1_2)).
    intros. elim H0. intros.
    specialize (H x).
    intuition.
    destruct x.
    * specialize (gt2ptFail2 p t1_1 t1_2); intros. intuition.
    * specialize (gt2ptFail1 p x1 x2); intros. intuition.
    * apply gtSgtUnknown.
  - split; intros; try inversion H.
    * specialize (IHt1_1 t2_1).
      specialize (IHt1_2 t2_2).
      apply gtSgtLift in H.
      inversion H.
      apply IHt1_1 in H0.
      apply IHt1_2 in H1.
      constructor; assumption.
    * apply gtSgtRefl.
    * specialize (IHt1_1 t2_1).
      specialize (IHt1_2 t2_2).
      apply IHt1_1 in H3.
      apply IHt1_2 in H5.
      clear H0 H1 H2 H4 t11 t12 t21 t22 IHt1_1 IHt1_2 H.
      unf2.
      intros.
      simpl gt2pt in *.
      destruct x; inversion H.
      clear H.
      specialize (H3 x1).
      specialize (H5 x2).
      unfold andb in *.
      destruct (gt2pt t1_1 x1); try intuition.
      rewrite H1.
      clear H1 t1_1 t1_2.
      simpl. intuition.
Qed.

(*
Inductive class_gtype_cons : gtype -> gtype -> Prop :=
| GTypeConsRefl : forall t, class_gtype_cons t t
| GTypeConsUL : forall t, class_gtype_cons GUnknown t
| GTypeConsUR : forall t, class_gtype_cons t GUnknown
| GTypeConsAbs : forall t11 t12 t21 t22, 
  class_gtype_cons t11 t21 ->
  class_gtype_cons t12 t22 ->
  class_gtype_cons (GFunc t11 t12) (GFunc t21 t22).*)

Require Import Coq.Logic.FunctionalExtensionality.

Lemma decb2eq : forall (a b : type) c, equiv_decb a b = c <-> (a = b <-> c = true).
Proof.
  intros.
  unf.
  un_type_dec.
  rewrite H0 in *; intuition.
  destruct c; auto.
Qed.

Lemma funcLift1 : forall a a' b b',
t2pt (TFunc a b) = PLift (gt2pt a') (gt2pt b')
->
(a' = t2gt a).
Proof.
  intros.
  pose proof (equal_f H).
  clear H.
  assert (∀ c1 c2 : type, c1 <> a /\ c2 <> b -> t2pt (TFunc a b) (TFunc c1 c2) = PLift (gt2pt a') (gt2pt b') (TFunc c1 c2)).
  intuition.
  specialize (H0 (TFunc a b)).
  unfold t2pt in *.
  unfold PSingleton in *.
  unfold equiv_decb in H0.
  unfold equiv_dec in H0.
  unfold type_EqDec in H0.
  un_type_dec.
  clear e.
Admitted.
Lemma funcLift2 : forall a a' b b',
t2pt (TFunc a b) =  PLift (gt2pt a') (gt2pt b')
->
(b' = t2gt b).
Proof.
Admitted.

Lemma funcLift : forall a a' b b',
t2pt (TFunc a b) =  PLift (gt2pt a') (gt2pt b')
<->
(a' = t2gt a /\ b' = t2gt b).
Proof.
  split.
    split.
    apply funcLift1 in H. assumption.
    apply funcLift2 in H. assumption.
  intros.
  inversion H.
  unfold t2pt.
  rewrite H0, H1.
  apply functional_extensionality.
  intros.
  unf2.
  destruct (type_dec (Func type_leaf a b) x); intuition.
  - symmetry in e.
    rewrite e.
    symmetry.
    apply andb_true_intro.
    split; apply gt2ptId.
  - destruct x; try congruence.
    symmetry.
    apply andb_false_iff.
    destruct (a == x1).
    rewrite e in *.
    destruct (b == x2).
    rewrite e0 in *.
    * intuition.
    * assert (b <> x2).
      intuition.
      apply gt2ptIdNot in H.
      intuition.
    * assert (a <> x1).
      intuition.
      apply gt2ptIdNot in H.
      intuition.
Qed.

Lemma ptSptLift : forall a b x, ptSpt a b -> a x = true -> b x = true.
Proof.
  intros.
  unf.
  intuition.
Qed.

Lemma ptSptTrans : forall a b, ptSpt a b -> forall c, ptSpt b c -> ptSpt a c.
Proof.
  intros.
  unf.
  intuition.
Qed.

(*Lemma ptSptGfunc1 : forall x t1_1 t1_2 t2_1 t2_2,
ptSpt (t2pt x) (g2pt (GFunc t1_1 t1_2)) ->
ptSpt (t2pt x) (g2pt (GFunc t2_1 t2_2)) ->
exists a' b' : type, stfl_Tcons a' b' ∧ ptSpt (t2pt a') (g2pt t1_1) ∧ ptSpt (t2pt b') (g2pt t2_1).
Proof.
  intros.
  inversion H; inversion H0; clear H H0.
    clear H1 H2 a a0.
    apply eqGfunc in H3.
    apply eqGfunc in H5.
    rewrite H3 in H5.
    inversion H5.
    exists (pt2t (g2pt t1_1)).
    exists (pt2t (g2pt t2_1)).
    split. congruence. split; apply drawSample.

    clear H1 a.
    apply ptSptLift in H6.
    apply ptSptLift in H7.
    elim H6. intros.
    elim H7. intros.
    inversion H.
    inversion H0.
    clear H H0 H6 H7.
    exists x0.
    exists x0.
    split. 
      constructor.
      split.
        rewrite H3 in H2.
        inversion H2.
        congruence.
        assumption.

    clear H6 a.
    apply ptSptLift in H4.
    apply ptSptLift in H5.
    elim H4. intros.
    elim H5. intros.
    inversion H.
    inversion H0.
    clear H H0 H4 H5.
    exists x0.
    exists x0.
    split. 
      constructor.
      split.
        assumption.
        rewrite H8 in H1.
        inversion H1.
        congruence.

    symmetry in H2. rewrite H2 in *.
    symmetry in H3. rewrite H3 in *.
    symmetry in H7. rewrite H7 in *.
    symmetry in H8. rewrite H8 in *.
    clear H2 H3 H7 H8 t2_1 t2_2 t1_1 t1_2.
    symmetry in H6.
    rewrite H6 in H1. 
    inversion H1.
    rewrite H0 in *.
    rewrite H2 in *.
    clear H6 H1 H0 H2.
    exists (pt2t t0).
    exists (pt2t t0).
    split. 
      constructor.

      assert (ptSpt (t2pt (pt2t t0)) t0).
      apply drawSample.
      split.
        specialize (ptSptTrans (t2pt (pt2t t0)) t0 t12). intuition.
        specialize (ptSptTrans (t2pt (pt2t t0)) t0 t1). intuition.
Qed.

Lemma ptSptGfunc2 : forall x t1_1 t1_2 t2_1 t2_2,
ptSpt (t2pt x) (g2pt (GFunc t1_1 t1_2)) ->
ptSpt (t2pt x) (g2pt (GFunc t2_1 t2_2)) ->
exists a' b' : type, stfl_Tcons a' b' ∧ ptSpt (t2pt a') (g2pt t1_2) ∧ ptSpt (t2pt b') (g2pt t2_2).
Proof.
  intros.
  inversion H; inversion H0; clear H H0.
    clear H1 H2 a a0.
    apply eqGfunc in H3.
    apply eqGfunc in H5.
    rewrite H3 in H5.
    inversion H5.
    exists (pt2t (g2pt t1_2)).
    exists (pt2t (g2pt t2_2)).
    split. congruence. split; apply drawSample.

    clear H1 a.
    apply ptSptLift in H6.
    apply ptSptLift in H7.
    elim H6. intros.
    elim H7. intros.
    inversion H.
    inversion H0.
    clear H H0 H6 H7.
    exists x1.
    exists x1.
    split. 
      constructor.
      split.
        rewrite H3 in H2.
        inversion H2.
        congruence.
        assumption.

    clear H6 a.
    apply ptSptLift in H4.
    apply ptSptLift in H5.
    elim H4. intros.
    elim H5. intros.
    inversion H.
    inversion H0.
    clear H H0 H4 H5.
    exists x1.
    exists x1.
    split. 
      constructor.
      split.
        assumption.
        rewrite H8 in H1.
        inversion H1.
        congruence.

    symmetry in H2. rewrite H2 in *.
    symmetry in H3. rewrite H3 in *.
    symmetry in H7. rewrite H7 in *.
    symmetry in H8. rewrite H8 in *.
    clear H2 H3 H7 H8 t2_1 t2_2 t1_1 t1_2.
    symmetry in H6.
    rewrite H6 in H1. 
    inversion H1.
    rewrite H0 in *.
    rewrite H2 in *.
    clear H6 H1 H0 H2.
    exists (pt2t t2).
    exists (pt2t t2).
    split.
      constructor.

      assert (ptSpt (t2pt (pt2t t2)) t2).
      apply drawSample.
      split.
        specialize (ptSptTrans (t2pt (pt2t t2)) t2 t22). intuition.
        specialize (ptSptTrans (t2pt (pt2t t2)) t2 t3). intuition.
Qed.*)

(*Proposition 2 - consistency as lifted equality*)
Theorem consistencyAsLiftedEq : forall t1 t2, glift (stfl_Tcons) t1 t2 <-> class_gtype_cons t1 t2.
Proof.
  unfold glift, plift;
  induction t1, t2;
  intros;
  split;
  intros.

  - destruct t, g; 
    try apply GTypeConsRefl;
    unfold gt2pt in H;
    try constructor.
    destruct p, p0;
    try constructor;
    elim H; intros;
    elim H0; intros;
    rewrite ptSingleton in H1;
    rewrite ptSingleton in H1;
    inversion H1;
    inversion H3;
    symmetry in H4, H5;
    rewrite H4, H5 in H2;
    inversion H2.
  - inversion H; 
    specialize (gtHas t0); 
    intros HX; 
    elim HX; 
    intro x; 
    intros HY;
    exists x;
    exists x;
    split;
    try constructor;
    try apply gt2ptUnknown;
    clear HX.
    * rewrite H2, H0 in *; clear H2 H0 t0.
      auto.
    * rewrite H2, H0 in *; clear H2 H0 t0.
      auto.
    * symmetry in H1.
      rewrite H1, H0 in *; clear H1 H0 t0.
      auto.
    * symmetry in H2.
      rewrite H2, H0 in *; clear H2 H0 t0.
      auto.
  - destruct t; try constructor.
    elim H. intros.
    elim H0. intros.
    inversion H1.
    inversion H3.
    inversion H2.
    rewrite H6 in *.
    clear H H0 H1 H2 H3 H6 x.
    destruct x0.
    * destruct t.
      specialize (gt2ptFail2 p0 t2_1 t2_2).
      intuition.
    * specialize (gt2ptFail1 p x0_1 x0_2).
      intuition.
  - inversion H.
    specialize (gtHas (Func gtype_leaf t2_1 t2_2)).
    intros.
    elim H2. intros.
    exists x. exists x.
    split; try constructor; try apply gt2ptUnknown.
    assumption.
  - destruct g; try constructor.
    elim H. intros.
    elim H0. intros.
    inversion H1.
    inversion H3.
    inversion H2.
    rewrite H6 in *.
    clear H H0 H1 H2 H3 H6 x.
    destruct x0.
    * destruct t.
      specialize (gt2ptFail2 p0 t1_1 t1_2).
      intuition.
    * specialize (gt2ptFail1 p x0_1 x0_2).
      intuition.
  - inversion H.
    specialize (gtHas (Func gtype_leaf t1_1 t1_2)).
    intros.
    elim H1. intros.
    exists x. exists x.
    split; try constructor; try apply gt2ptUnknown.
    assumption.
  - specialize (IHt1_1 t2_1).
    specialize (IHt1_2 t2_2).
    elim IHt1_1. intros.
    elim IHt1_2. intros.
    clear IHt1_1 IHt1_2.
    elim H. intros.
    elim H4. intros.
    inversion H5.
    inversion H7.
    clear H H4 H5 H7.
    inversion H6.
    rewrite H in *.
    clear H6 H H1 H3.
    simpl gt2pt in *.
    unfold PLift in *.
    destruct x0; try intuition.
    apply andb_prop in H8.
    apply andb_prop in H9.
    inversion H8.
    inversion H9.
    clear H8 H9.
    constructor.
    * apply H0.
      exists x0_1. exists x0_1.
      split; try constructor; try assumption.
    * apply H2.
      exists x0_2. exists x0_2.
      split; try constructor; try assumption.
  - inversion H.
    * specialize (gtHas (Func gtype_leaf t2_1 t2_2)).
      intros. elim H1. intros.
      exists x. exists x.
      split; try constructor; try assumption.
    * apply (IHt1_1 t2_1) in H3.
      apply (IHt1_2 t2_2) in H5.
      clear H0 H1 H2 H4 IHt1_1 IHt1_2 t11 t12 t21 t22 H.
      elim H3. intros. elim H. intros.
      elim H5. intros. elim H1. intros.
      clear H3 H5 H H1.
      inversion H0.
      inversion H1.
      inversion H2.
      inversion H6.
      clear H0 H1 H2 H6.
      inversion H.
      inversion H5.
      rewrite H0, H1 in *.
      clear H0 H1 H5 H x x1.
      exists (TFunc x0 x2).
      exists (TFunc x0 x2).
      split; try constructor; simpl gt2pt; intuition.
Qed.


(*Proposition 3 - alpha sound*)
Theorem soundnessAlpha : forall pt gt, pt2gt pt gt -> ptSpt pt (gt2pt gt).
Proof.
  intro pt.
  intro gt.
  generalize pt. clear pt.
  induction gt.
  - intros. destruct t; intros; fConv; simpl gt2pt in *; try constructor.
    inversion H.
    clear H H1 t.
    destruct t'.
    * destruct t.
      simpl t2gt in *.
      inversion H0.
      rewrite H1 in *.
      clear H0 H1 p0.
      unfold PisSingleton in H2.
      unfold ptSpt.
      intros.
      specialize (H2 x).
      rewrite H in H2.
      symmetry in H2.
      fConv.
      unfold TPrimitive.
      rewrite H2.
      auto.
    * unfold t2gt in H0. inversion H0.
  - intros.
    inversion H.
    * unfold PisSingleton in H2.
      unfold ptSpt.
      intros.
      specialize (H2 x).
      rewrite H3 in H2.
      unfold PSingleton in H2.
      symmetry in H2.
      unf2.
      un_type_dec.
      rewrite e.
      apply gt2ptId.
    * clear H0 H4 a' b' H1 t.
      specialize (IHgt1 a).
      specialize (IHgt2 b).
      apply IHgt1 in H5.
      apply IHgt2 in H6.
      clear IHgt1 IHgt2 H.
      simpl gt2pt.
      unfold ptSpt.
      intros.
      unfold PisLift in H3.
      specialize (H3 x).
      rewrite H in H3. clear H.
      unfold PLift.
      destruct x; try (unf2; intuition).
      specialize (H5 x1).
      specialize (H6 x2).
      symmetry in H3.
      apply andb_prop in H3.
      inversion H3.
      intuition.
Qed.

Lemma ptSingletonOrEmpty : forall pt t, ptSpt pt (PSingleton t) <-> pt = PSingleton t \/ pt = PEmpty.
Proof.
  intros.
  split.

  case (pt t == true); intros.
  - assert (forall x, pt x = PSingleton t x).
    intros.
    case (t == x).
    * intuition. rewrite e0, e in *. symmetry. apply ptSingleton. auto.
    * intuition.
      unf2.
      specialize (H x).
      un_type_dec.
      destruct (pt x); intuition.

    * apply functional_extensionality in H0.
      intuition.
  - assert (forall x, pt x = PEmpty x).
    intros.
    compute.
    case (t == x); intuition.
    * rewrite e in *. destruct (pt x); intuition.
    * unf2.
      specialize (H x).
      un_type_dec.
      destruct (pt x); intuition.
    * apply functional_extensionality in H0.
      intuition.

  - intuition; rewrite H0.
    * apply ptSptRefl.
    * apply ptSptEmpty.
Qed.

Lemma pt2gtNotEmpty : forall a b, pt2gt a b -> ~ PisEmpty a.
Proof.
  unfold not.
  intros.
  inversion H; auto.
  assert (a t' = true).
  unfold PisSingleton in H1.
  specialize (H1 t').
  rewrite H1.
  rewrite ptSingleton. tauto.
  unfold PisEmpty in H0.
  specialize (H0 t').
  compute in H0.
  rewrite H0 in H4.
  intuition.
Qed.

Theorem equivEq1 : forall (a b : bool), a === b <-> a = b.
Proof.
  intros.
  split; intros; rewrite H; intuition.
Qed.

Theorem equivEq2 : forall {A : Type} (a b : A), complement Equivalence.equiv a b <-> a <> b.
Proof.
  intros.
  compute.
  tauto.
Qed.

Theorem equivEq2' : forall (a b : bool), complement Equivalence.equiv a b <-> a = negb b.
Proof.
  intros.
  destruct a, b; compute; intuition.
Qed.

Definition PDouble (a b : type) : ptype := fun t => if type_dec t a then true else (if type_dec t b then true else false).

Theorem helpPDoubleHas : forall b c, ∃ a, pt2gt (PDouble b c) a.
Proof.
  induction b, c.
  - destruct (t == t0).
    * rewrite e.
      exists (t2gt (TLeaf t0)).
      constructor.
      unfold PisSingleton.
      unfold PDouble.
      intros.
      unf2.
      repeat un_type_dec.
    * exists GUnknown.
      constructor.
        unfold not.
        unfold PisEmpty.
        intros.
        specialize (H (TLeaf t)).
        unfold PDouble in H.
        unf2.
        repeat un_type_dec.

        unfold not.
        unfold PisSingleton.
        intros.
        pose proof (H (TLeaf t)).
        pose proof (H (TLeaf t0)).
        unfold PDouble in *.
        unf2.
        repeat un_type_dec.

        unfold not.
        unfold PisLift.
        intros.
        specialize (H (TLeaf t)).
        unfold PDouble in H.
        unf2.
        repeat un_type_dec.
  - exists GUnknown.
    constructor.
    * unfold not.
      unfold PisEmpty.
      intros.
      specialize (H (TLeaf t)).
      unfold PDouble in H.
      unf2.
      repeat un_type_dec.

    * unfold not.
      unfold PisSingleton.
      intros.
      pose proof (H (TLeaf t)).
      pose proof (H (Func type_leaf c1 c2)).
      unfold PDouble in *.
      unf2.
      repeat un_type_dec.

    * unfold not.
      unfold PisLift.
      intros.
      specialize (H (TLeaf t)).
      unfold PDouble in H.
      unf2.
      repeat un_type_dec.
  - exists GUnknown.
    constructor.
    * unfold not.
      unfold PisEmpty.
      intros.
      specialize (H (TLeaf t)).
      unfold PDouble in H.
      unf2.
      repeat un_type_dec.

    * unfold not.
      unfold PisSingleton.
      intros.
      pose proof (H (TLeaf t)).
      pose proof (H (Func type_leaf b1 b2)).
      unfold PDouble in *.
      unf2.
      repeat un_type_dec.

    * unfold not.
      unfold PisLift.
      intros.
      specialize (H (TLeaf t)).
      unfold PDouble in H.
      unf2.
      repeat un_type_dec.
  - specialize (IHb1 c1). specialize (IHb2 c2).
    destruct ((Func type_leaf b1 b2) == (Func type_leaf c1 c2)).
    * rewrite e.
      exists (GFunc (t2gt b1) (t2gt b2)).
      specialize (PGSingleton (PDouble (Func type_leaf c1 c2) (Func type_leaf c1 c2)) (Func type_leaf b1 b2)).
      intros.
      assert (PisSingleton (PDouble (Func type_leaf c1 c2) (Func type_leaf c1 c2)) (Func type_leaf b1 b2)).
      unfold PDouble.
      unfold PisSingleton.
      intros.
      unf2.
      repeat un_type_dec.
      intuition.
    * rewrite equivEq2 in c.
      destruct (b1 == c1).
        rewrite e in *. clear e b1.
        destruct (b2 == c2). rewrite e in *. intuition.
        rewrite equivEq2 in c0.
        
        elim IHb1. intros. clear IHb1.
        elim IHb2. intros. clear IHb2.
        exists (GFunc x x0). 

        specialize (PGLift (PDouble (Func type_leaf c1 b2) (Func type_leaf c1 c2))).
        intros.
        assert (¬ PisEmpty (PDouble (Func type_leaf c1 b2) (Func type_leaf c1 c2))).
        unfold not.
        unfold PisEmpty.
        intros.
        specialize (H2 (Func type_leaf c1 b2)).
        unfold PDouble in H2.
        unf2.
        repeat un_type_dec.
        intuition.
        specialize (H3 (PSingleton c1) (PDouble b2 c2)).
        assert (PisLift (PDouble (Func type_leaf c1 b2) (Func type_leaf c1 c2)) (PSingleton c1) (PDouble b2 c2)).
        unfold PisLift.
        intros.
        unfold PDouble.
        unfold PLift.
        destruct t; auto.
        un_type_dec.
          inversion e.
          un_type_dec.
          assert (PSingleton c1 c1 = true). apply ptSingleton. auto. rewrite H1. auto.
        un_type_dec. inversion e. rewrite H4, H5 in *.
          un_type_dec.
          un_type_dec.
          assert (PSingleton c1 c1 = true). apply ptSingleton. auto. rewrite H1. auto.
        destruct (c1 == t1).
          destruct (c2 == t2).
          rewrite e, e0 in *. assert (Func type_leaf t1 t2 = Func type_leaf t1 t2). tauto. intuition.
          destruct (b2 == t2).
            repeat un_type_dec.
            repeat un_type_dec. symmetry. apply andb_false_r. 
          assert (PSingleton c1 t1 = false).
            unf. un_type_dec. rewrite H1. symmetry. apply andb_false_l.
        
        intuition.
        specialize (H4 (t2gt c1)).
        assert (pt2gt (PSingleton c1) (t2gt c1)).
        constructor. unfold PisSingleton. tauto.
        intuition.
        specialize (H5 GUnknown).
        assert (pt2gt (PDouble b2 c2) GUnknown).
        constructor. 
          unfold PisEmpty. unfold not. intros. specialize (H4 b2). unfold PDouble in H4. unf2. un_type_dec.
          intros. unfold not. unfold PisSingleton. intros.
            pose proof (H4 b2).
            pose proof (H4 c2). unfold PDouble in *. unf2. repeat un_type_dec.
Admitted.


Theorem gt2ptPDouble : forall a b, a <> b -> pt2gt (PDouble a b) GUnknown \/ (exists a' b', pt2gt (PDouble a b) (GFunc a' b')).
Proof.
  intros.
  destruct a.
  - constructor.
    constructor; unfold not; intros.
    * unfold PisEmpty in H0.
      specialize (H0 b).
      unf2.
      unfold PDouble in *.
      repeat un_type_dec.
    * unfold PisSingleton in H0.
      pose proof (H0 (TLeaf t)).
      pose proof (H0 b).
      unfold PDouble in *.
      unf2.
      repeat un_type_dec.
    * unfold PisLift in H0.
      pose proof (H0 (TLeaf t)).
      unfold PDouble in *.
      repeat un_type_dec.
  - destruct b.
    constructor.
    constructor; unfold not; intros.
    * unfold PisEmpty in H0.
      pose proof (H0 (TLeaf t)).
      unf2.
      unfold PDouble in *.
      repeat un_type_dec.
    * unfold PisSingleton in H0.
      pose proof (H0 (TLeaf t)).
      pose proof (H0 (Func type_leaf a1 a2)).
      unfold PDouble in *.
      unf2.
      repeat un_type_dec.
    * unfold PisLift in H0.
      pose proof (H0 (TLeaf t)).
      unfold PDouble in *.
      repeat un_type_dec.
    * assert (∃ a' b' : unk_leaf_type gtype_leaf, pt2gt (PDouble (Func type_leaf a1 a2) (Func type_leaf b1 b2)) (GFunc a' b')).
      assert (∃ a, pt2gt (PDouble a1 b1) a). apply helpPDoubleHas.
      assert (∃ b, pt2gt (PDouble a2 b2) b). apply helpPDoubleHas.
      elim H0. intros. elim H1. intros.
      exists x. exists x0.
      
Admitted.


(*Proposition 4 - alpha optimal*)
Theorem optimalAlpha : forall gt gt' pt, pt2gt pt gt' -> ptSpt pt (gt2pt gt) -> gtSgt gt' gt.
Proof.
  induction gt.
  - intros.
    destruct t; try constructor.
    simpl gt2pt in H0.
    unfold gtSgt.
    apply ptSingletonOrEmpty in H0.
    apply ptSingletonOrEmpty.
    specialize (pt2gtNotEmpty pt gt').
    intuition.
    * rewrite H2 in H. inversion H; clear H0 H H2.
        clear H4 gt'.
        unfold PisSingleton in *.
        specialize (H1 (TPrimitive p)).
        unfold PSingleton in H1.
        unfeq. unfold type_EqDec in *.
        un_type_dec.
        un_type_dec.
        rewrite e0.
        simpl.
        auto.

        clear H7 gt' H1.
        unfold PisLift in H3.
        specialize (H3 (TPrimitive p)).
        inversion H3.
        unf2.
        un_type_dec.

        clear H6 gt' H1.
        specialize (H3 (TPrimitive p)).
        contradict H3.
        unfold PisSingleton.
        tauto.
    * try (rewrite H2 in H0; compute in H0; intuition).
  - intros.
    unfold gtSgt.
    simpl gt2pt in *.
    Print ptSpt.
    unfold ptSpt in H0.
    unfold PLift in H0.
    destruct gt'; try destruct g.
    * inversion H.
      destruct t'; try destruct t0; simpl t2gt in H1; inversion H1.
      rewrite H5 in *. clear H2 H5 p0 t H1 H.
      specialize (H0 (TPrimitive p)).
      unfold PisSingleton in H3.
      specialize (H3 (TPrimitive p)).
      rewrite H3 in *.
      rewrite ptSingleton in H0.
      intuition.
    * inversion H; try (destruct t'; try destruct t0; simpl t2gt in H1; inversion H1).
      clear H4 t H. fConv.

      specialize (H3 (gt2pt gt1) (gt2pt gt2)).
      contradict H3.
      unfold PisLift.
      unfold PLift.
      intros.
      destruct t.
        pose proof (H0 (TLeaf t)) as Hx.
        simpl in Hx.
        fConv.
        destruct (pt (TLeaf t)); intuition.

        pose proof (H0 (Func type_leaf t1 t2)) as Hx.
        destruct (pt (Func type_leaf t1 t2) == true); try (rewrite equivEq1 in e; rewrite e in *); intuition.
        rewrite equivEq2' in c.
        rewrite c in *.
        simpl in *.
        clear Hx.

        symmetry.
        apply andb_false_iff.

        destruct (gt2pt gt1 t1 == true); destruct (gt2pt gt2 t2 == true); try rewrite equivEq1 in *; try rewrite equivEq2' in *; intuition.

        (*gen new x*)
        apply not_all_ex_not in H1.
        elim H1. intros.
        clear H1.
        compute in H.
        assert (pt x = true). destruct (pt x); tauto. clear H.

        (*spec new x*)
        pose proof (H0 x) as Hx. intuition.
        destruct x; try inversion H. clear H4.
        apply andb_prop in H.
        inversion H. clear H.


        (*gen new x*)
        specialize (H2 (Func type_leaf x1 x2)).
        apply not_all_ex_not in H2.
        elim H2. intros.
        clear H2.
        assert (x <> (Func type_leaf x1 x2)).
        unfold not.
        intros.
        rewrite H2 in *.
        assert (PSingleton (Func type_leaf x1 x2) (Func type_leaf x1 x2) = true).
        apply ptSingleton. tauto.
        rewrite H1, H5 in H.
        auto. 
        assert (PSingleton (Func type_leaf x1 x2) x = false).
        unfold PSingleton. unfeq. unfold type_EqDec. un_type_dec.
        rewrite H5 in H. clear H5.
        assert (pt x = true). destruct (pt x); intuition. clear H.

        (*spec new x*)
        pose proof (H0 x) as Hx. intuition.
        destruct x; try inversion H. clear H7.
        apply andb_prop in H.
        inversion H. clear H.

        clear H0.

        (*inequality*)
        assert (t1 <> x1 \/ t2 <> x2).
        destruct (t1 == x1).
        rewrite e1 in *.
        destruct (t2 == x2).
        rewrite e2 in *.
        rewrite H1 in c. intuition.
        rewrite equivEq2 in c0. intuition.
        rewrite equivEq2 in c0. intuition.

        (*contradict using IH*)
        specialize (IHgt1 GUnknown (PDouble t1 x1)).
        specialize (IHgt2 GUnknown (PDouble t2 x2)).
        
        assert (pt2gt (PDouble t1 x1) gt1).
Admitted.

(*collecting lifting defs*)
Definition pdom : ptype -> ptype -> Prop := pliftF dom.
Definition pcod : ptype -> ptype -> Prop := pliftF cod.

(*Proposition 5 - codom*)
Theorem Fdom : forall (a b : gtype), dom a = Some b <-> exists c, a = GFunc b c.
Proof.
  intros.
  unfold dom.
  split; intros.
  - destruct a; inversion H. exists a2. tauto.
  - destruct a; elim H; intros; inversion H0. tauto.
Qed.


(*STFL -> GTFL*)
Fixpoint term2gterm (t : stfl_t) : gtfl_t := match t with
  | TflTermNat _ n
 => TflTermNat _ n
  | TflTermBool _ b
 => TflTermBool _ b
  | TflTermVar _ v
 => TflTermVar _ v
  | TflTermAbs _ v t x
 => TflTermAbs _ v (t2gt t) (term2gterm x)
  | TflTermApp _ a b
 => TflTermApp _ (term2gterm a) (term2gterm b)
  | TflTermPlus _ a b
 => TflTermPlus _ (term2gterm a) (term2gterm b)
  | TflTermIf _ a b c
 => TflTermIf _ (term2gterm a) (term2gterm b) (term2gterm c)
  | TflTermAssert _ x t
 => TflTermAssert _ (term2gterm x) (t2gt t)
end.

Definition t2gtContext (c : stfl_T_context) : gtfl_T_context :=
fun s => 

(*Proposition 9 - Equivalence for fully-annotated terms*)
Theorem EqFAT : forall c t T, stfl_term_type c t T <-> gtfl_term_type c (t2gt t) (term2gterm T).


