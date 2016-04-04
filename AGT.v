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

Ltac unfeq := unfold equiv_decb, equiv_decb, equiv_dec in *.

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

Lemma ptSingleton : forall x t, PSingleton t x = true -> t = x.
Proof.
  intros.
  unfold PSingleton in H.
  unfeq.
  destruct (type_EqDec t x).
  auto.
  inversion H.
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

(*subset*)
Definition ptSpt (a b : ptype) : Prop := forall x, (a x) = true -> (b x) = true.

Theorem PSPrefl : forall a, ptSpt a a.
Proof.
  compute.
  intuition.
Qed.
Theorem PSPtot : forall a, ptSpt a PTotal.
Proof.
  compute.
  intuition.
Qed.
Theorem PSPlift : forall t11 t12 t21 t22,
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
exists a' b', pred a' b' /\ ptSpt (t2pt a') a /\ ptSpt (t2pt b') b.
Definition glift (pred : type -> type -> Prop) (a b : gtype) : Prop :=
plift pred (gt2pt a) (gt2pt b).

(*Definition 4 - Collecting Function*)
Definition pliftF (f : type -> option type) (a b : ptype) : Prop :=
forall b', b b' = true <-> exists a', a a' = true /\ f a' = Some b'.

(*Definition 5 - alpha*)
Definition pt2gtSingleton (t : ptype) (t' : type) (p : PisSingleton t t') : gtype := t2gt t'.
Definition pt2gtTotal (t : ptype) (p : PisTotal t) : gtype := GUnknown.
Inductive pt2gt : ptype -> gtype -> Prop :=
| PGSingleton : forall t t', PisSingleton t t' -> pt2gt t (t2gt t')
| PGTotal : pt2gt PTotal GUnknown
| PGLift : forall t a b a' b', PisLift t a b /\ pt2gt a a' /\ pt2gt b b' -> pt2gt t (GFunc a' b')
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
  try apply PSPrefl;
  try apply PSPtot.

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

Lemma funcEta : forall {A B : Type} (a b : A -> B), a = b -> forall (c : A), a c = b c.
Proof.
  intros.
  rewrite H.
  congruence.
Qed.

Lemma funcLift1 : forall a a' b b',
t2pt (TFunc a b) = PLift (gt2pt a') (gt2pt b')
->
(a' = t2gt a).
Proof.
  intros.
  specialize (funcEta (t2pt (TFunc a b)) (PLift (gt2pt a') (gt2pt b'))). intros.
  intuition. clear H.
  unf2. fConv.
  destruct (type_dec (TFunc a b) c).
  specialize (H1 (TFunc a b)).
  un_type_dec.
  simpl in H1.
  symmetry in H1.
  apply andb_prop in H1.
  inversion H1.
  unfold gt2pt in H.
  unfold andb in H1.
  assert (gt2pt a' a = true).
  intuition.

  inversion H.
  intuition.
  induction a, a', b, b'; 
  intros; 
  try (compute in *; congruence);
  specialize (IHa1 a'1 a2 a'2);
  specialize (IHa2 a'2 a1 a'1);
  unfold t2pt in H; simpl g2pt in H; inversion H; symmetry in H1, H2;
  try (destruct p, p0);
  try (compute in *; congruence);
  simpl;
  apply f_equal2;
  try (
    unfold t2gt;
    try (apply IHa1);
    try (apply IHa2);
    unfold t2pt;
    rewrite H1, H2;
    simpl g2pt;
    congruence).
Qed.
Lemma funcLift2 : forall a a' b b',
t2pt (TFunc a b) = PTypeMFunc (g2pt a') (g2pt b')
->
(b' = t2gt b).
Proof.
  induction b, b', a, a'; 
  intros; 
  try (compute in *; congruence);
  specialize (IHb1 b'1);
  specialize (IHb2 b'2);
  unfold t2pt in H; simpl g2pt in H; inversion H; symmetry in H3, H2;
  try (destruct p, p0);
  try (compute in *; congruence);
  simpl;
  apply f_equal2;
  try (
    try (apply IHb1);
    try (apply IHb2);
    unfold t2pt;
    simpl g2pt;
    apply f_equal2;
    congruence).
Qed.

Lemma funcLift : forall a a' b b',
t2pt (TFunc a b) = PTypeMFunc (g2pt a') (g2pt b')
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
  simpl t2gt.
  simpl g2pt.
  apply f_equal2; congruence.
Qed.

Lemma drawSample : forall p, ptSpt (t2pt (pt2t p)) p.
Proof.
  intros.
  induction p.
    compute. constructor.
    compute. constructor.

    simpl pt2t.
    unfold t2pt in *.
    simpl t2gt.
    simpl g2pt.
    apply PSPlift;
    congruence.
Qed.

Lemma eqCycle : forall x, x = pt2t (g2pt (t2gt x)).
Proof.
  intros.
  induction x.
    compute; congruence.
    simpl t2gt.
    simpl g2pt.
    simpl pt2t.
    symmetry in IHx1.
    symmetry in IHx2.
    rewrite IHx1.
    rewrite IHx2.
    congruence.
Qed.

Lemma eqGfunc : forall x t1 t2, t2pt x = PTypeMFunc t1 t2 -> x = TFunc (pt2t t1) (pt2t t2).
Proof.
  intros.
  induction x.
    compute in H. congruence.

    apply f_equal2; inversion H; apply eqCycle.
Qed.

Lemma ptSptLift : forall a b, ptSpt a b -> exists x, ptSpt (t2pt x) a /\ ptSpt (t2pt x) b.
Proof.
  induction a.
    intros.
    inversion H. 
      exists (TPrimitive p). split; compute; constructor.
      exists (TPrimitive p). split; compute; constructor.

    intros.
    inversion H; exists (TPrimitive Bool); split; compute; constructor.

    intros.
    inversion H. 
      exists (TFunc (pt2t a1) (pt2t a2)).
      split; unfold t2pt; simpl t2gt; simpl g2pt; apply PSPlift; apply drawSample.

      exists (TFunc (pt2t a1) (pt2t a2)).
      split; unfold t2pt; simpl t2gt; simpl g2pt; try (apply PSPlift; apply drawSample); try constructor.

      symmetry in H0. symmetry in H1. rewrite H0 in *. rewrite H1 in *. symmetry in H3. rewrite H3 in *.
      clear H H3 H0 H1.
      specialize (IHa1 t12 H2).
      specialize (IHa2 t22 H4).
      clear H2 H4 b.
      elim IHa1. intros.
      elim IHa2. intros.
      inversion H.
      inversion H0.
      clear IHa1 IHa2 H H0.
      exists (TFunc x x0).
      split; unfold t2pt; simpl t2gt; simpl g2pt; apply PSPlift; assumption.
Qed.

Lemma ptSptTrans : forall a b c, ptSpt a b /\ ptSpt b c -> ptSpt a c.
Proof.
  induction a, b, c; firstorder; inversion H; inversion H0; try congruence.
  constructor.
  clear H1 H2 H3 H5 H7 H8 H9 H11 t0 t1 t2 t3 t11 t12 t21 t22 H H0.
  specialize (IHa1 b1 c1).
  specialize (IHa2 b2 c2).
  intuition.
  constructor; assumption.
Qed.

Lemma ptSptGfunc1 : forall x t1_1 t1_2 t2_1 t2_2,
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
Qed.

(*Proposition 2 - consistency as lifted equality*)
Theorem consistencyAsLiftedEq : forall t1 t2, glift (stfl_Tcons) t1 t2 <-> class_gtype_cons t1 t2.
Proof.
  unfold glift, plift;
  induction t1, t2;
  firstorder.

  destruct p, p0; 
  try apply GTypeConsRefl;
  unfold g2pt in H0, H1;
  inversion H0; inversion H1;
  congruence.

  inversion H.
  exists (TPrimitive p0).
  exists (TPrimitive p0).
  split.
  congruence.
  split; apply PSPrefl.

  unfold g2pt in H0, H1;
  inversion H0; inversion H1;
  congruence.

  inversion H.

  apply GTypeConsUR.

  inversion H.
  exists (TPrimitive p).
  exists (TPrimitive p).
  split.
  congruence.
  split; 
  try constructor.

  unfold g2pt in H0, H1;
  inversion H0; inversion H1;
  congruence.

  inversion H.

  constructor; try (apply IHt1_1); try (apply IHt1_2); clear IHt1_1 IHt1_2.
    inversion H.
    rewrite H2 in *; clear H2 x H.
    specialize (ptSptGfunc1 x0 t1_1 t1_2 t2_1 t2_2).
    auto.
    inversion H.
    rewrite H2 in *; clear H2 x H.
    specialize (ptSptGfunc2 x0 t1_1 t1_2 t2_1 t2_2).
    auto.

  inversion H. 
    rewrite H2 in *. rewrite H3 in *. clear H H2 H3 H0. clear t t1_1 t1_2.
    specialize (IHt1_1 t2_1).
    specialize (IHt1_2 t2_2).
    assert (class_gtype_cons t2_1 t2_1). constructor.
    assert (class_gtype_cons t2_2 t2_2). constructor.
    apply IHt1_1 in H.
    apply IHt1_2 in H0.
    elim H; intros.
    elim H1; intros.
    elim H0; intros.
    elim H3; intros.
    inversion H2.
    inversion H6.
    inversion H4.
    inversion H10.
    clear H H0 H1 H2 H3 H4 H6 H10 IHt1_1 IHt1_2.
    exists (TFunc x x1).
    exists (TFunc x0 x2).
    unfold t2pt.
    simpl t2gt.
    simpl g2pt.
    split.
      congruence.
      split; constructor; unfold t2pt in *; congruence.

    clear H0 H1 H2 H4 t11 t12 t21 t22.
    apply IHt1_1 in H3.
    apply IHt1_2 in H5.
    clear IHt1_1 IHt1_2 H.
    elim H3. intros. elim H. intros.
    elim H5. intros. elim H1. intros.
    exists (TFunc x x1).
    exists (TFunc x0 x2).
    unfold t2pt.
    simpl t2gt.
    simpl g2pt.
    inversion H0.
    inversion H2.
    inversion H6.
    inversion H8.
    clear H0 H2 H6 H8.
    split.
      congruence.
      split; constructor; unfold t2pt in *; congruence.

  constructor.

  inversion H.
  exists (pt2t (g2pt (GFunc t1_1 t1_2))).
  exists (pt2t (g2pt (GFunc t1_1 t1_2))).
  split.
  congruence.
  split.
  apply drawSample.
  constructor.

  constructor.

  inversion H.
  exists (TPrimitive p).
  exists (TPrimitive p).
  split.
  congruence.
  split; 
  try constructor.

  constructor.

  inversion H.
  exists (pt2t (g2pt (GFunc t2_1 t2_2))).
  exists (pt2t (g2pt (GFunc t2_1 t2_2))).
  split.
  congruence.
  split.
  constructor.
  apply drawSample.

  constructor.

  exists (TPrimitive Bool).
  exists (TPrimitive Bool).
  split.
  congruence.
  split; 
  try constructor.
Qed.


(*Proposition 3 - alpha sound*)
Theorem soundnessAlpha : forall pt, ptSpt pt (g2pt (pt2g pt)).
Proof.
  apply ptype_ind.
  intros.
  apply PSPrefl.
  apply PSPrefl.
  intros.
  simpl.
  apply PSPlift; congruence.
Qed.

(*Proposition 4 - alpha optimal*)
Theorem optimalAlpha : forall pt gt, ptSpt pt (g2pt gt) -> gtSgt (pt2g pt) gt.
Proof.
  unfold gtSgt.
  induction pt; firstorder.
  compute. fold g2pt. fold pt2g.
  induction gt; simpl pt2g; inversion H; firstorder.
    compute. fold g2pt. fold pt2g.
    specialize (IHpt1 gt1).
    specialize (IHpt2 gt2).
    symmetry in H2. rewrite H2 in *.
    symmetry in H3. rewrite H3 in *.
    clear H2 H3 H H0 a IHgt1 IHgt2.
    constructor; try (apply IHpt1); try (apply IHpt2); constructor.

    compute. fold g2pt. fold pt2g.
    specialize (IHpt1 gt1).
    specialize (IHpt2 gt2).
    symmetry in H2. rewrite H2 in *.
    symmetry in H4. rewrite H4 in *.
    clear H2 H4 H IHgt1 IHgt2 H0 H1 t11 t21.
    constructor; firstorder.

    constructor.
Qed.


(*strict predicate lifting (to simulate partial function lifting)*)
Definition pliftF (pred : type -> type -> Prop) (a b : ptype) : Prop :=
forall b', ptSpt (t2pt b') b <-> exists a', pred a' b' /\ ptSpt (t2pt a') a.
Definition gliftF (pred : type -> type -> Prop) (a b : gtype) : Prop :=
exists x, pliftF pred (g2pt a) x /\ b = pt2g x.

(*collecting lifting defs*)
Definition pdom : ptype -> ptype -> Prop := pliftF tdom.
Definition pcod : ptype -> ptype -> Prop := pliftF tcod.
Definition gdom2 : gtype -> gtype -> Prop := gliftF tdom.
Definition gcod2 : gtype -> gtype -> Prop := gliftF tcod.

Theorem liftCod1 : forall a, pcod (g2pt GUnknown) a -> gcod GUnknown (pt2g a).
Proof.
  firstorder.
  assert ((pt2g a) = GUnknown).
  destruct a; compute.
  compute in H; fold g2pt in H; fold t2gt in H.
  specialize (H (TFunc (TPrimitive Bool) (TPrimitive Bool))).
  inversion H.
  contradict H1.
  clear.
  unfold not.
  firstorder.
  specialize (H (TFunc (TFunc (TPrimitive Bool) (TPrimitive Bool)) (TFunc (TPrimitive Bool) (TPrimitive Bool)))).
  assert (tcod
      (TFunc (TFunc (TPrimitive Bool) (TPrimitive Bool))
         (TFunc (TPrimitive Bool) (TPrimitive Bool)))
      (TFunc (TPrimitive Bool) (TPrimitive Bool))
    ∧ ptSpt
        (g2pt
           (t2gt
              (TFunc
                 (TFunc (TPrimitive Bool) (TPrimitive Bool))
                 (TFunc (TPrimitive Bool) (TPrimitive Bool)))))
        PTypeTotal).
  split.
  apply (TCod (TFunc (TFunc (TPrimitive Bool) (TPrimitive Bool)) (TFunc (TPrimitive Bool) (TPrimitive Bool))) (TFunc (TPrimitive Bool) (TPrimitive Bool)) (TFunc (TPrimitive Bool) (TPrimitive Bool))). auto.
  constructor.
  intuition.
  inversion H0.

  constructor.
  contradict H.
  unfold not.
  firstorder.
  compute in H; fold g2pt in H; fold t2gt in H.
  specialize (H (TPrimitive Bool)).
  inversion H.
  contradict H1.
  clear.
  unfold not.
  firstorder.
  specialize (H (TFunc (TPrimitive Bool) (TPrimitive Bool))).
  assert (tcod (TFunc (TPrimitive Bool) (TPrimitive Bool)) (TPrimitive Bool)
    ∧ ptSpt (g2pt (t2gt (TFunc (TPrimitive Bool) (TPrimitive Bool)))) PTypeTotal).
  split.
  apply (TCod (TFunc (TPrimitive Bool) (TPrimitive Bool)) (TPrimitive Bool) (TPrimitive Bool)). auto.
  constructor.
  intuition.
  compute in H0. inversion H0.

  rewrite H0.
  constructor.
Qed.

Theorem liftCod2 : forall a, pcod (g2pt GUnknown) a -> pt2g a = pt2g PTypeTotal.
Proof.
  firstorder.
  compute in H; fold g2pt in H; fold t2gt in H.
  destruct a; try congruence.

  specialize (H (TFunc (TPrimitive Bool) (TPrimitive Bool))).
  inversion H.
  contradict H1.
  clear.
  unfold not.
  firstorder.
  specialize (H (TFunc (TFunc (TPrimitive Bool) (TPrimitive Bool)) (TFunc (TPrimitive Bool) (TPrimitive Bool)))).
  assert (tcod
      (TFunc (TFunc (TPrimitive Bool) (TPrimitive Bool))
         (TFunc (TPrimitive Bool) (TPrimitive Bool)))
      (TFunc (TPrimitive Bool) (TPrimitive Bool))
    ∧ ptSpt
        (g2pt
           (t2gt
              (TFunc
                 (TFunc (TPrimitive Bool) (TPrimitive Bool))
                 (TFunc (TPrimitive Bool) (TPrimitive Bool)))))
        PTypeTotal).
  split.
  apply (TCod (TFunc (TFunc (TPrimitive Bool) (TPrimitive Bool)) (TFunc (TPrimitive Bool) (TPrimitive Bool))) (TFunc (TPrimitive Bool) (TPrimitive Bool)) (TFunc (TPrimitive Bool) (TPrimitive Bool))). auto.
  constructor.
  intuition.
  inversion H0.

  specialize (H (TPrimitive Bool)).
  inversion H.
  contradict H1.
  clear.
  unfold not.
  firstorder.
  specialize (H (TFunc (TPrimitive Bool) (TPrimitive Bool))).
  assert (tcod (TFunc (TPrimitive Bool) (TPrimitive Bool)) (TPrimitive Bool)
    ∧ ptSpt (g2pt (t2gt (TFunc (TPrimitive Bool) (TPrimitive Bool)))) PTypeTotal).
  split.
  apply (TCod (TFunc (TPrimitive Bool) (TPrimitive Bool)) (TPrimitive Bool) (TPrimitive Bool)). auto.
  constructor.
  intuition.
  compute in H0. inversion H0.
Qed.

Theorem liftCod' : forall a, ~ pcod (g2pt (GPrimitive Int)) a.
Proof.
  unfold not.
  firstorder.
  compute in H; fold g2pt in H; fold t2gt in H.
  
  specialize (H (pt2t a)).
  inversion H.
  contradict H0.
  clear.
  unfold not.
  firstorder.
  assert (ptSpt (g2pt (t2gt (pt2t a))) a).
  apply drawSample.
  intuition.
  elim H1. intros.
  inversion H.

  inversion H3.
  destruct x.
    inversion H6.
    rewrite H7 in *.
    inversion H2.
    inversion H5.

    inversion H6.
Qed.

Lemma tdomhelp1 : forall a b, ~ tdom (TPrimitive a) b.
Proof.
  unfold not.
  intros.
  destruct b; 
  inversion H;
  inversion H0.
Qed.

(*Lemma gdom2help1 : forall a b, ~ gdom2 (GPrimitive a) b.
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H0.
  clear H H0 H2 b.
  compute in H1. fold g2pt in H1. fold t2gt in H1.
  elim H1.
  intros.

  specialize (H (pt2t x)).
  assert (ptSpt (g2pt (t2gt (pt2t x))) x). apply drawSample.
  intuition.
  clear H0 H1.
  destruct x0.

  compute in H3.
  inversion H.
  inversion H0.

  compute in H3.
  inversion H3.
Qed.*)

Lemma tdomhelp : forall a b c, tdom (TFunc a b) c -> a = c.
Proof.
  intros.
  inversion H.
  inversion H0.
  auto.
Qed.

Lemma g2ptEq : forall a b, g2pt a = g2pt b -> a = b.
Proof.
  induction a, b;
  intros;
  compute in H;
  inversion H;
  try congruence.
  fold g2pt in *.
  specialize (IHa1 b1).
  specialize (IHa2 b2).
  intuition.
  apply f_equal2; auto.
Qed.

(*Proposition 5 codom*)
Theorem Fdom : forall a b, gdom a b <-> exists c, a = GFunc b c.
Proof.
  intros.
  split; intros.
  inversion H.
  exists b0.
  assumption.
  exists b.
  .

  rewrite H0.
  split.
  assumption.





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

Definition tfl_T_context (tfl_T : Set) := tfl_Var -> tfl_T -> Prop.

Definition tfl_T_context_empty (tfl_T : Set) : tfl_T_context tfl_T := fun x' t' => False.
Definition tfl_T_context_set (tfl_T : Set) (x : tfl_Var) (t : tfl_T) (c : tfl_T_context tfl_T) : tfl_T_context tfl_T :=
  fun x' t' => (x = x' /\ t = t') \/ c x' t'.

(**STFL**)
Definition stfl_T := type.
Definition stfl_Tcons := fun (a b : stfl_T) => a = b.
Definition stfl_t : Set := tfl_t stfl_T.
Definition stfl_T_context := tfl_T_context stfl_T.

Inductive stfl_term_type : stfl_T_context -> stfl_t -> stfl_T -> Prop :=
| StflTx : forall (c : stfl_T_context) (x : tfl_Var) (t : stfl_T), 
    c x t -> stfl_term_type c (TflTermVar stfl_T x) t
| StflTn : forall c n, 
    stfl_term_type c (TflTermNat stfl_T n) (TPrimitive Int)
| StflTb : forall c b, 
    stfl_term_type c (TflTermBool stfl_T b) (TPrimitive Bool)
| StflTapp : forall c t1 tt1 t2 tt2 ttx,
    stfl_term_type c t1 tt1 ->
    stfl_term_type c t2 tt2 ->
    dom tt1 = Some tt2 ->
    cod tt1 = Some ttx ->
    stfl_term_type c (TflTermApp stfl_T t1 t2) ttx
| StflTplus : forall c t1 t2,
    stfl_term_type c t1 (TPrimitive Int) ->
    stfl_term_type c t2 (TPrimitive Int) ->
    stfl_term_type c (TflTermPlus stfl_T t1 t2) (TPrimitive Int)
| StflTif : forall c t1 t2 tt2 t3 tt3 ttx,
    stfl_term_type c t1 (TPrimitive Bool) ->
    stfl_term_type c t2 tt2 ->
    stfl_term_type c t3 tt3 ->
    tequate tt2 tt3 = Some ttx ->
    stfl_term_type c (TflTermIf stfl_T t1 t2 t3) ttx
| StflTlambda : forall (c : stfl_T_context) t tt1 tt2 (x : tfl_Var),
    stfl_term_type (tfl_T_context_set stfl_T x tt1 c) t tt2 ->
    stfl_term_type c (TflTermAbs stfl_T x tt1 t) (TFunc tt1 tt2)
| StflTassert : forall c t tt,
    stfl_term_type c t tt ->
    stfl_term_type c (TflTermAssert stfl_T t tt) tt
.

(**GTFL**)
Definition gtfl_T := gtype.
Definition gtfl_Tcons := class_gtype_cons.
Definition gtfl_t : Set := tfl_t gtfl_T.
Definition gtfl_T_context := tfl_T_context gtfl_T.

Inductive gtfl_term_type : gtfl_T_context -> gtfl_t -> gtfl_T -> Prop :=
| GtflTx : forall (c : gtfl_T_context) x t, 
    c x t -> gtfl_term_type c (TflTermVar gtfl_T x) t
| GtflTn : forall c n, 
    gtfl_term_type c (TflTermNat gtfl_T n) (GPrimitive Int)
| GtflTb : forall c b, 
    gtfl_term_type c (TflTermBool gtfl_T b) (GPrimitive Bool)
| GtflTapp : forall c t1 tt1 t2 tt2 ttx,
    gtfl_term_type c t1 tt1 ->
    gtfl_term_type c t2 tt2 ->
    dom tt1 = Some tt2 ->
    cod tt1 = Some ttx ->
    gtfl_term_type c (TflTermApp gtfl_T t1 t2) ttx
| GtflTplus : forall c t1 tt1 t2 tt2,
    gtfl_term_type c t1 tt1 ->
    gtfl_term_type c t2 tt2 ->
    gtfl_Tcons tt1 (GPrimitive Int) ->
    gtfl_Tcons tt2 (GPrimitive Int) ->
    gtfl_term_type c (TflTermPlus gtfl_T t1 t2) (GPrimitive Int)
| GtflTif : forall c t1 tt1 t2 tt2 t3 tt3 ttx,
    gtfl_term_type c t1 tt1 ->
    gtfl_term_type c t2 tt2 ->
    gtfl_term_type c t3 tt3 ->
    gtfl_Tcons tt1 (GPrimitive Bool) ->
    gequate tt2 tt3 = Some ttx ->
    gtfl_term_type c (TflTermIf gtfl_T t1 t2 t3) ttx
| GtflTlambda : forall (c : gtfl_T_context) t tt1 tt2 (x : tfl_Var),
    gtfl_term_type (tfl_T_context_set gtfl_T x tt1 c) t tt2 ->
    gtfl_term_type c (TflTermAbs gtfl_T x tt1 t) (GFunc tt1 tt2)
| GtflTassert : forall c t tt tt1,
    gtfl_term_type c t tt ->
    gtfl_Tcons tt tt1 ->
    gtfl_term_type c (TflTermAssert gtfl_T t tt1) tt1
.

