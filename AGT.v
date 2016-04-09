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
Definition PisFuncs (pt : ptype) (a b : ptype) := 
(forall p, pt (TLeaf p) = false) /\ 
(forall a', a a' = true <-> exists b', pt (TFunc a' b') = true) /\ 
(forall b', b b' = true <-> exists a', pt (TFunc a' b') = true).

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

Ltac un_type_dec := 
  try (destruct (type_EqDec _ _)); 
  try (destruct (gtype_EqDec _ _)); 
  try (destruct (type_dec _ _)); 
  try (destruct (gtype_dec _ _)); 
  auto; try congruence; try intuition.

(**Defitions**)
(*subset*)
Definition ptSpt (a b : ptype) : Prop := forall x, (a x) = true -> (b x) = true.

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
| PGSingleton : 
forall t t', PisSingleton t t' -> pt2gt t (t2gt t')
| PGLift : 
forall t, ~ PisEmpty t -> 
forall a b, PisFuncs t a b -> forall a', pt2gt a a' -> forall b', pt2gt b b' -> pt2gt t (GFunc a' b')
| PGTotal : 
forall t, ~ PisEmpty t -> 
(forall t', ~ PisSingleton t t') -> 
(forall a b, ~ PisFuncs t a b) -> 
pt2gt t GUnknown
.

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
| (Leaf _ GUnk, _) => Some b
| (_, Leaf _ GUnk) => Some a
| (Func _ a1 b1, Func _ a2 b2) => obind (gequate a1 a2) (fun a => 
                                  obind (gequate b1 b2) (fun b => Some (Func gtype_leaf a b)))
| (x, y) => if x == y then Some x else None
end.

Theorem t2gtId : forall a b, t2gt a = t2gt b <-> a = b.
Proof.
  induction a; intros.
  - destruct t. split; intros.
    * simpl in H. destruct b; try destruct t; simpl in H; inversion H.
      tauto.
    * rewrite H. tauto.
  - split; intros.
    * simpl in H. destruct b; try destruct t; simpl in H; inversion H.
      specialize (IHa1 b1).
      specialize (IHa2 b2).
      intuition. rewrite H6, H0.
      tauto.
    * rewrite H. tauto.
Qed.
  
Theorem gequateId : forall a, gequate a a = Some a.
Proof.
  intros.
  induction a; try destruct t; simpl.
  - unfeq. un_type_dec.
  - tauto.
  - rewrite IHa1, IHa2. simpl. tauto.
Qed.

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

Inductive tfl_term_type 
  (t_leaf : Set) 
  (mk_prim : primitive_type -> unk_leaf_type t_leaf)
  (cons : unk_leaf_type t_leaf → unk_leaf_type t_leaf → Prop)
  (equate : unk_leaf_type t_leaf → unk_leaf_type t_leaf → option (unk_leaf_type t_leaf))
   : tfl_T_context (unk_leaf_type t_leaf) -> tfl_t (unk_leaf_type t_leaf) -> (unk_leaf_type t_leaf) -> Prop :=
| TflTx : forall (c : tfl_T_context (unk_leaf_type t_leaf)) x t, 
    c x = Some t -> tfl_term_type t_leaf mk_prim cons equate c (TflTermVar (unk_leaf_type t_leaf) x) t
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

Theorem sConsByEquate : forall a b, stfl_Tcons a b <-> exists c, tequate a b = Some c.
Proof.
  unfold stfl_Tcons. unfold tequate. unfeq. unfold type_EqDec.
  intros.
  un_type_dec.
  - exists a. tauto.
  - elim H. intros. inversion H0.
Qed.

(*GTFL*)
Definition gtfl_T := gtype.
Definition gtfl_Tcons := class_gtype_cons.
Definition gtfl_t : Set := tfl_t gtfl_T.
Definition gtfl_T_context := tfl_T_context gtfl_T.

Definition gtfl_term_type := tfl_term_type gtype_leaf GPrimitive gtfl_Tcons gequate.

Theorem gConsByEquate : forall a b, gtfl_Tcons a b <-> exists c, gequate a b = Some c.
Proof.
  unfold gtfl_Tcons.
  induction a.
  - intros. destruct t; split; intros.
    * exists (Leaf gtype_leaf (GPrim p)). simpl. unfeq. inversion H.
        un_type_dec. simpl. tauto.
    * elim H. intros. simpl in H0. unfeq. destruct b; try destruct g; try un_type_dec.
        rewrite e. constructor.
        constructor.
    * exists b. constructor.
    * constructor.
  - intros. split; intros; try inversion H.
    * exists (Func gtype_leaf a1 a2).
      apply gequateId.
    * exists (Func gtype_leaf a1 a2). constructor.
    * specialize (IHa1 t21). specialize (IHa2 t22). intuition.
      elim H9. intros. elim H5. intros.
      exists (GFunc x x0).
      simpl. rewrite H8, H10. 
      simpl. tauto.
    * destruct b; try destruct g; try inversion H0. constructor.
      specialize (IHa1 b1). specialize (IHa2 b2). intuition.
      destruct (gequate a1 b1); simpl in H2; inversion H2.
      destruct (gequate a2 b2); simpl in H2; inversion H2.
      constructor; try apply H3; try apply H5.
        exists g. tauto.
        exists g0. tauto.
Qed.

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
Theorem ptSptLift : forall t11 t12 t21 t22, 
  ~ PisEmpty t11 -> ~ PisEmpty t12 -> ~ PisEmpty t21 -> ~ PisEmpty t22 ->
  (ptSpt t11 t12 /\ ptSpt t21 t22 <-> ptSpt (PLift t11 t21) (PLift t12 t22)).
Proof.
  split; intros.
  - inversion H3. apply ptSptFuncLift; assumption.
  - Print PLift.
    compute in *.
    apply not_all_ex_not in H.
    apply not_all_ex_not in H0.
    apply not_all_ex_not in H1.
    apply not_all_ex_not in H2.
    inversion H.
    inversion H0.
    inversion H1.
    inversion H2.
    clear H H0 H1 H2.
    apply not_false_is_true in H4.
    apply not_false_is_true in H5.
    apply not_false_is_true in H6.
    apply not_false_is_true in H7.
    intuition.
    * specialize (H3 (TFunc x3 x1)). simpl in H3. rewrite H, H6 in H3. intuition.
      destruct (t12 x3); tauto.
    * specialize (H3 (TFunc x x3)). simpl in H3. rewrite H4, H in H3. intuition.
      destruct (t22 x3); try tauto.
      destruct (t12 x); try tauto.
Qed.

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

Lemma gt2ptNotEmpty : forall t, ~ PisEmpty (gt2pt t).
Proof.
  unfold not.
  intros.
  unfold PisEmpty in H. unfold PEmpty in H.
  contradict H.
  apply ex_not_not_all.
  induction t.
  - destruct t.
    * exists (TPrimitive p). simpl gt2pt. unfold PSingleton. unfeq. un_type_dec.
    * exists TInt. compute. intuition.
  - inversion IHt1.
    inversion IHt2.
    exists (TFunc x x0).
    apply not_false_is_true in H.
    apply not_false_is_true in H0.
    simpl.
    rewrite H, H0. intuition.
Qed.

Lemma gtSgtLift : forall a1 b1 a2 b2, gtSgt (GFunc a1 b1) (GFunc a2 b2) <-> gtSgt a1 a2 /\ gtSgt b1 b2.
Proof.
  split; generalize a1, b1, a2, b2; clear a1 b1 a2 b2; unfold gtSgt; simpl gt2pt; intros.
  - apply ptSptLift; try apply gt2ptNotEmpty.
    assumption.
  - inversion H. clear H.
    unfold ptSpt in *.
    intros.
    unfold PLift in *.
    destruct x; inversion H.
    specialize (H0 x1).
    specialize (H1 x2).
    apply andb_prop in H.
    inversion H.
    rewrite H2, H4 in *.
    intuition.
Qed.

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

Lemma ptSptLift' : forall a b x, ptSpt a b -> a x = true -> b x = true.
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
      unfold PisFuncs in H3.
      inversion H3. inversion H1. clear H3 H1.
      destruct x. specialize (H0 t). unfold TLeaf in H0. rewrite H0 in H. intuition.
      
      unfold PLift.
      try (unf2; intuition). fConv.
      specialize (H5 x1).
      specialize (H6 x2).
      specialize (H4 x1).
      specialize (H7 x2).
      apply andb_true_intro.
      rewrite H5.
      rewrite H6.
      + tauto.
      + apply H7. exists x1. assumption.
      + apply H4. exists x2. assumption.
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


Fixpoint PDouble2gt (a : type) (b : type) : gtype :=
match a with
| Leaf _ (TPrim pa) =>
  match b with
  | Leaf _ (TPrim pb) => if pa == pb then GPrimitive pa else GUnknown
  | Func _ _ _ => GUnknown
  end
| Func _ a1 a2 =>
  match b with
  | Leaf _ _ => GUnknown
  | Func _ b1 b2 => GFunc (PDouble2gt a1 b1) (PDouble2gt a2 b2)
  end
end.

Lemma PDouble2gtId : forall x, PDouble2gt x x = t2gt x.
Proof.
  induction x; intros; try destruct t; simpl.
  - unfeq. destruct (primitive_type_EqDec p p); try tauto.
    intuition.
  - rewrite IHx1, IHx2. tauto.
Qed.

Ltac unfP' := 
  try unfold PisLift;
  try unfold PisSingleton;
  try unfold PisEmpty;
  try unfold PisTotal;
  try unfold PLift;
  try unfold PSingleton;
  try unfold PEmpty;
  try unfold PTotal;
  try unfold PDouble.

Ltac unfP := 
  try unfold PisLift in *;
  try unfold PisSingleton in *;
  try unfold PisEmpty in *;
  try unfold PisTotal in *;
  try unfold PLift in *;
  try unfold PSingleton in *;
  try unfold PEmpty in *;
  try unfold PTotal in *;
  try unfold PDouble in *.

Lemma PisEmptyPDouble : forall a b, ~ PisEmpty (PDouble a b).
Proof.
  unfold not. unfold PisEmpty.
  intros.
  specialize (H a).
  unfP.
  un_type_dec.
Qed.

Lemma PDouble2gtWorksHelp : forall t1 x1 t2 x2, pt2gt (PDouble t1 x1) (PDouble2gt t1 x1) -> pt2gt (PDouble t2 x2) (PDouble2gt t2 x2) -> pt2gt (PDouble (Func type_leaf t1 t2) (Func type_leaf x1 x2)) (GFunc (PDouble2gt t1 x1) (PDouble2gt t2 x2)).
Proof.
  intros.
  destruct ((Func type_leaf t1 t2) == (Func type_leaf x1 x2)).
  - inversion e. rewrite H2, H3 in *.
    specialize (PGSingleton (PDouble (Func type_leaf x1 x2) (Func type_leaf x1 x2)) (TFunc x1 x2)).
    simpl. repeat rewrite PDouble2gtId. intros.
    apply H1.
    unfold PisSingleton.
    intros.
    unfold PDouble.
    unfold PSingleton. unfeq.
    un_type_dec.
  - specialize (PGLift (PDouble (Func type_leaf t1 t2) (Func type_leaf x1 x2))).
    unfold not. unfold PisEmpty.
    intros.
    assert (~ ∀ t : type, PDouble (Func type_leaf t1 t2) (Func type_leaf x1 x2) t = PEmpty t).
      unfold not. intros. specialize (H2 (Func type_leaf t1 t2)).
      unfold PDouble in H2. un_type_dec.
    intuition. clear H2.
    specialize (H3 (PDouble t1 x1) (PDouble t2 x2)).
    unfold PisFuncs in *.
    assert ((∀ p : type_leaf, PDouble (Func type_leaf t1 t2) (Func type_leaf x1 x2) (TLeaf p) = false)
     ∧ (∀ a' : type,
        PDouble t1 x1 a' = true
        ↔ (∃ b' : unk_leaf_type type_leaf, PDouble (Func type_leaf t1 t2) (Func type_leaf x1 x2) (TFunc a' b') = true))
       ∧ (∀ b' : type,
          PDouble t2 x2 b' = true
          ↔ (∃ a' : unk_leaf_type type_leaf, PDouble (Func type_leaf t1 t2) (Func type_leaf x1 x2) (TFunc a' b') = true))).
    * repeat split; intros.
      + unfP. un_type_dec.
          exists t2. rewrite e. repeat un_type_dec.
          exists x2. un_type_dec. rewrite e. repeat un_type_dec.
      + inversion H1. unfP. repeat un_type_dec;
        inversion e; intuition.
      + unfP. un_type_dec.
          exists t1. rewrite e. repeat un_type_dec.
          exists x1. un_type_dec. rewrite e. repeat un_type_dec.
      + inversion H1. unfP. repeat un_type_dec;
        inversion e; intuition.
    * intuition.
Qed.

Lemma PDouble2gtWorks : forall t x, pt2gt (PDouble t x) (PDouble2gt t x).
Proof.
  induction t; try destruct t; intros; simpl.
  - destruct x; try destruct t.
    * destruct (p == p0).
      + rewrite e.
        specialize (PGSingleton (PDouble (Leaf type_leaf (TPrim p0)) (Leaf type_leaf (TPrim p0))) (TPrimitive p0)).
        simpl. intros.
        apply H.
        unfold PisSingleton.
        intros.
        unfold PDouble.
        unfold PSingleton. unfeq.
        un_type_dec.
      + constructor; unfold not; intros.
          unfold PisEmpty in H.
          specialize (H (TPrimitive p)).
          unfold PDouble in H.
          unfold PEmpty in H. un_type_dec.

          unfold PisSingleton in H.
          pose proof (H (TPrimitive p)).
          pose proof (H (TPrimitive p0)).
          unfold PDouble in *.
          unfold PSingleton in *. unfeq. repeat un_type_dec.
          rewrite e in *. inversion e1.
          intuition.

          unfold PisFuncs in H. intuition.
          specialize (H0 (TPrim p)).
          unfold PDouble in *. repeat un_type_dec.
    * constructor; unfold not; intros.
      + unfold PisEmpty in H.
        specialize (H (TPrimitive p)).
        unfold PDouble in H.
        unfold PEmpty in H. un_type_dec.

      + unfold PisSingleton in H.
        pose proof (H (TPrimitive p)).
        pose proof (H (Func type_leaf x1 x2)).
        unfold PDouble in *.
        unfold PSingleton in *. unfeq. repeat un_type_dec.

      + unfold PisFuncs in H. intuition.
        specialize (H0 (TPrim p)).
        unfold PDouble in *. repeat un_type_dec.
  - destruct x; try destruct t.
    * constructor; unfold not; intros.
      + unfold PisEmpty in H.
        specialize (H (TPrimitive p)).
        unfold PDouble in H.
        unfold PEmpty in H. repeat un_type_dec.

      + unfold PisSingleton in H.
        pose proof (H (TPrimitive p)).
        pose proof (H (Func type_leaf t1 t2)).
        unfold PDouble in *.
        unfold PSingleton in *. unfeq. repeat un_type_dec.
        rewrite e in *. inversion e1.

      + unfold PisFuncs in H. intuition.
        specialize (H0 (TPrim p)).
        unfold PDouble in *. repeat un_type_dec.
    * apply PDouble2gtWorksHelp.
      + apply IHt1.
      + apply IHt2.
Qed.

Theorem helpPDoubleHas : forall b c, ∃ a, pt2gt (PDouble b c) a.
Proof.
  intros. exists (PDouble2gt b c). apply PDouble2gtWorks.
Qed.

Theorem gt2ptPDouble : forall a b, a <> b -> pt2gt (PDouble a b) GUnknown \/ (exists a' b', pt2gt (PDouble a b) (GFunc a' b')).
Proof.
  intros.
  specialize (PDouble2gtWorks a b). intros.
  destruct (PDouble2gt a b); try destruct g.
  - inversion H0.
    destruct t'; try destruct t0; simpl in H1; inversion H1.
    rewrite H5 in *.
    unfP.
    pose proof (H3 a).
    pose proof (H3 b).
    unfeq.
    repeat un_type_dec.
  - intuition.
  - apply or_intror. exists g1. exists g2. intuition.
Qed.

Theorem notPisFuncsGivesPrimitive : ∀ pt, (∀ a b : ptype, ¬ PisFuncs pt a b) -> exists t, pt (TPrimitive t) = true.
Proof.

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

        clear H7 gt' H1 t H6.
        unfold PisFuncs in H3. intuition.
        specialize (H (TPrim p)).
        unfP. unfeq. un_type_dec.
        compute in c. tauto.

        clear H6 gt' H1.
        specialize (H3 (TPrimitive p)).
        contradict H3.
        unfold PisSingleton.
        tauto.
    * rewrite H2 in H0. unfP. intuition.
  - unfold gtSgt, ptSpt in *.
    induction gt'; try destruct t; intros;
    simpl gt2pt in *;
    unfP; unfeq.
    * inversion H.
      destruct t'; try destruct t0; simpl in H2; inversion H2.
      clear H2. rewrite H6 in *. clear H6.
      unfP. specialize (H4 (TPrimitive p)).
      unfeq. unf2. repeat un_type_dec. fConv.
      specialize (H0 (TPrimitive p)).
      intuition.
    * inversion H.
      + destruct t'; try destruct t0; simpl in H2; inversion H2.
      + apply notPisFuncsGivesPrimitive in H4. inversion H4.
        specialize (H0 (TPrimitive x0)).
        intuition.
    * destruct x; intuition.
      specialize (IHgt1 gt'1).
      specialize (IHgt2 gt'2).
      inversion H; clear H.
      + clear t H3.
        destruct t'; try destruct t; simpl in H2; inversion H2.
        clear H2. unfP. unfeq.
        pose proof (H4 (Func type_leaf t'1 t'2)).
        un_type_dec. clear e.
        specialize (IHgt1 (PSingleton t'1)).
        specialize (IHgt2 (PSingleton t'2)).
        symmetry in H3, H5.
        rewrite H3, H5 in *. clear H3 H5.
          assert (pt2gt (PSingleton t'1) (t2gt t'1)).
          constructor. unfP'. tauto.
          assert (pt2gt (PSingleton t'2) (t2gt t'2)).
          constructor. unfP'. tauto.
        intuition.
        pose proof (H0 (Func type_leaf t'1 t'2)). intuition. apply andb_prop in H8. inversion H8.
          assert (∀ x : type, PSingleton t'1 x = true → gt2pt gt1 x = true).
          intros. unfP. unfeq. un_type_dec.
          assert (∀ x : type, PSingleton t'2 x = true → gt2pt gt2 x = true).
          intros. unfP. unfeq. un_type_dec.
        intuition.
        specialize (H8 x1).
        specialize (H5 x2).
        apply andb_prop in H1. inversion H1.
        intuition.
      + clear H2 H3 a' b' t H6.
        specialize (IHgt'1 a).
        specialize (IHgt'2 b).
        intuition.
        apply andb_prop in H1. inversion H1. clear H1.
        specialize (IHgt1 a).
        specialize (IHgt2 b).
        intuition.
        unfold PisFuncs in H5. intuition.
          assert (∀ x : type, a x = true → gt2pt gt1 x = true).
          intros.
          specialize (H5 x). apply H5 in H11. inversion H11.
          specialize (H0 (TFunc x x0)). intuition. simpl in H15. apply andb_prop in H15. intuition.
          assert (∀ x : type, b x = true → gt2pt gt2 x = true).
          intros.
          specialize (H12 x). apply H12 in H13. inversion H13.
          specialize (H0 (TFunc x0 x)). intuition. simpl in H16. apply andb_prop in H16. intuition.
        intuition.
Qed.

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
fun s => option_map t2gt (c s).

Lemma contextSetLift : forall t t0 c, t2gtContext (tfl_T_context_set (unk_leaf_type type_leaf) t t0 c) = tfl_T_context_set (unk_leaf_type gtype_leaf) t (t2gt t0) (t2gtContext c).
Proof.
  intros.
  apply functional_extensionality. intros.
  unfold tfl_T_context_set. unfold t2gtContext. unfold option_map.
  destruct (string_dec t x); try tauto.
Qed.

Open Scope string_scope.

Lemma existsTerm : forall T, exists t, forall c, gtfl_term_type c (term2gterm t) (t2gt T).
Proof.
  induction T; intros.
  - destruct t.
    destruct p.
    * exists (TflTermNat type 3). constructor.
    * exists (TflTermBool type false). constructor.
  - inversion IHT1. inversion IHT2.
    exists (TflTermAbs type "x" T1 x0).
    intros.
    apply TflTlambda.
    fold term2gterm. fold t2gt.
    apply H0.
Qed.

Lemma t2gtUnknown : forall t, t2gt t <> GUnknown.
Proof.
  unfold not.
  intros.
  destruct t; try destruct t; simpl t2gt in H; inversion H.
Qed.

Lemma contextStaysClean : forall t t0 c, exists d, t2gtContext d = tfl_T_context_set gtype t (t2gt t0) (t2gtContext c).
Proof.
  intros.
  exists (tfl_T_context_set type t t0 c).
  apply functional_extensionality.
  intros.
  unfold t2gtContext.
  unfold tfl_T_context_set.
  destruct (string_dec t x); try tauto.
Qed.

Inductive canReceiveGUnknownFrom : gtype -> Prop :=
| CRUBase : canReceiveGUnknownFrom GUnknown
| CRUReturn : forall u t, canReceiveGUnknownFrom t -> canReceiveGUnknownFrom (GFunc u t)
.

Lemma cannotReceiveGUnknownFromConv : forall g t, t2gt t = g -> ~ canReceiveGUnknownFrom g.
Proof.
  induction g; unfold not; intros.
  - destruct t.
    * inversion H0.
    * apply t2gtUnknown in H. inversion H.
  - destruct t; try destruct t; simpl in H; inversion H.
    inversion H0.
    apply IHg2 in H3.
    intuition.
Qed.

Lemma cannotReceiveGUnknownFromContext : forall g t c, t2gtContext c t = Some g -> exists tt, g = t2gt tt.
Proof.
  induction g; unfold not; intros.
  - compute in H. destruct (c t0); try inversion H.
    destruct s; try destruct t1.
    * exists (TPrimitive p). tauto.
    * exists (TFunc s1 s2). compute. tauto.
  - compute in H. destruct (c t); try inversion H.
    clear H.
    destruct s; try destruct t0; inversion H1. clear H1.
    exists (TFunc s1 s2). compute. tauto.
Qed.

Lemma cannotReceiveGUnknownFromT2GT : forall t g, g = t2gt t -> ~ canReceiveGUnknownFrom g.
Proof.
  induction t; unfold not; intros.
  - destruct t. compute in H. rewrite H in H0. inversion H0.
  - simpl in H. rewrite H in H0. inversion H0.
    specialize (IHt2 t). intuition. rewrite H3 in H4. intuition.
Qed.

Definition isMoreSpecific a b := gequate a b = Some a.

Lemma gequateUnkL : forall x, gequate GUnknown x = Some x.
Proof.
  simpl. tauto.
Qed.
Lemma gequateUnkR : forall x, gequate x GUnknown = Some x.
Proof.
  induction x.
  - destruct t; simpl; tauto.
  - simpl. tauto.
Qed.

Lemma IMSunk : forall x, isMoreSpecific x GUnknown.
Proof.
  intros.
  unfold isMoreSpecific.
  apply gequateUnkR.
Qed.

Lemma IMSid : forall x, isMoreSpecific x x.
Proof.
  intros.
  unfold isMoreSpecific.
  apply gequateId.
Qed.

Lemma IMSlift : forall a1 b1 a2 b2, isMoreSpecific a1 a2 -> isMoreSpecific b1 b2 -> isMoreSpecific (GFunc a1 b1) (GFunc a2 b2).
Proof.
  intros.
  unfold isMoreSpecific in *.
  simpl gequate.
  rewrite H, H0.
  simpl. tauto.
Qed.

Lemma gequateMakesSpecific : forall a b c, gequate a b = Some c -> isMoreSpecific c a /\ isMoreSpecific c b.
Proof.
  induction a; try destruct t.
  - intros. 
    destruct b; try destruct g; simpl in H; 
    unfeq; un_type_dec; inversion H; try apply IMSid.
    * inversion e. apply IMSid.
    * apply IMSunk.
  - intros. split.
    * apply IMSunk.
    * rewrite gequateUnkL in H. inversion H. apply IMSid.
  - intros.
    destruct b; try destruct g; simpl in H; inversion H.
    * split.
      + apply IMSid.
      + apply IMSunk.
    * specialize (IHa1 b1).
      specialize (IHa2 b2).
      destruct (gequate a1 b1); simpl in H; inversion H.
      destruct (gequate a2 b2); simpl in H; inversion H.
      specialize (IHa1 g).
      specialize (IHa2 g0).
      intuition; apply IMSlift; assumption.
Qed.

Lemma cruf : forall a b, isMoreSpecific a b -> canReceiveGUnknownFrom a -> canReceiveGUnknownFrom b.
Proof.
  unfold isMoreSpecific.
  induction a; intros.
  - inversion H0. symmetry in H2. rewrite H2 in *. simpl in H. inversion H. constructor.
  - inversion H0. inversion H.
    destruct b; try destruct g; try constructor.
    * unfeq. un_type_dec.
    * specialize (IHa2 b2).
      destruct (gequate a1 b1); simpl in H5; inversion H5.
      destruct (gequate a2 b2); simpl in H5; inversion H5.
      rewrite H8 in *.
      intuition.
Qed.

Lemma gtfl_term_type_Unknown : forall t g c, gtfl_term_type (t2gtContext c) (term2gterm t) g -> ~ canReceiveGUnknownFrom g.
Proof.
  unfold not.
  induction t, g; intros; inversion H; inversion H0; clear H H0.
  - symmetry in H4. rewrite H4 in *. inversion H5.
  - symmetry in H4. rewrite H4 in *. inversion H5.
  - symmetry in H6. rewrite H6 in *.
    compute in H3. destruct (c t); try inversion H3.
    destruct s; try destruct t1; inversion H0.
  - clear c0 H2 x H1 u H5 t0 H4 t1 H7.
    apply cannotReceiveGUnknownFromContext in H3. inversion H3.
    apply cannotReceiveGUnknownFromT2GT in H.
    contradict H.
    constructor. assumption.
  - clear u H8 t3 H10 tt2 H7 t2 H5 x H1 c0 H2 tt1 H4 g1 H6.
    specialize (contextStaysClean t t0 c). intros. inversion H. symmetry in H0. unfold gtype in H0. rewrite H0 in *.
    apply IHt in H3; intuition.
  - destruct tt1; try inversion H6. inversion H8.
    rewrite H0, H9 in *. clear H0 H9 tt1_1 tt1_2. symmetry in H10. rewrite H10 in *.
    clear H10 g H7 ttx c0 t0 t3 H5 H1 H2 H6 H8.
    apply IHt1 in H3; intuition. repeat constructor.
  - destruct tt1; try inversion H6. inversion H8.
    rewrite H0, H12 in *. clear H0 H12 tt1_1 tt1_2 u t H9 H11.
    clear H7 ttx c0 t0 t3 H5 H1 H2 H6 H8.
    apply IHt1 in H3; intuition. repeat constructor. assumption.
  - symmetry in H3. rewrite H3 in *. inversion H10.
  - symmetry in H12. rewrite H12 in *.
    clear H12 g H8 ttx H1 H2 H3 H6 c0 t0 t4 t5.
    unfold gequate in H10.
    destruct tt2; try destruct g.
    * destruct tt3; try destruct g.
      + unfeq. un_type_dec.
      + inversion H10.
      + unfeq. un_type_dec.
    * apply IHt2 in H5; try constructor; inversion H5.
    * destruct tt3; try destruct g.
      + unfeq. un_type_dec.
      + apply IHt3 in H7; try constructor; inversion H7.
      + fold gequate in *.
        destruct (gequate tt2_1 tt3_1); try inversion H10.
        destruct (gequate tt2_2 tt3_2); try inversion H0.
  - clear u t H11 H13 c0 t0 t4 t5 H1 H2 H3 H6 H8 ttx.
    unfold gequate in H10.
    destruct tt2; try destruct g.
    * destruct tt3; try destruct g.
      + unfeq. un_type_dec.
      + inversion H10.
      + unfeq. un_type_dec.
    * apply IHt2 in H5; try constructor; inversion H5.
    * destruct tt3; try destruct g.
      + unfeq. un_type_dec.
      + apply IHt3 in H7; try constructor; inversion H7.
      + fold gequate in *.
        apply IHt3 in H7. inversion H7.
        clear IHt1 IHt2 IHt3 H4 H5 H7 H9 tt1 c t1 t2 t3.
        destruct (gequate tt2_1 tt3_1); try inversion H10.
        clear H10.
        unfold obind in H0.
        constructor.
        apply (cruf g2 tt3_2); try assumption.
        apply (gequateMakesSpecific tt2_2 tt3_2 g2).
        destruct (gequate tt2_2 tt3_2); inversion H0.
        tauto.
  - symmetry in H8. rewrite H8 in *. apply t2gtUnknown in H4. inversion H4.
  - destruct t0; try destruct t0; simpl in H4; inversion H4.
    apply cannotReceiveGUnknownFromConv in H10. intuition.
Qed.

Lemma gequateT2GT : forall a x y, gequate (t2gt x) (t2gt y) = Some a -> x = y /\ a = t2gt x.
Proof.
  induction a; intros.
  - destruct t.
    * destruct x, y; try destruct t; try destruct t0; simpl gequate in H; unfeq; un_type_dec.
      + inversion e. inversion H. symmetry in H2. tauto.
      + inversion H. tauto.
      + destruct (gequate (t2gt x1) (t2gt y1)); simpl in H; inversion H.
        destruct (gequate (t2gt x2) (t2gt y2)); simpl in H; inversion H.
      + destruct (gequate (t2gt x1) (t2gt y1)); simpl in H; inversion H.
        destruct (gequate (t2gt x2) (t2gt y2)); simpl in H; inversion H.
    * destruct x, y; try destruct t; try destruct t0; simpl gequate in H; unfeq; un_type_dec.
      + destruct (gequate (t2gt x1) (t2gt y1)); simpl in H; inversion H.
        destruct (gequate (t2gt x2) (t2gt y2)); simpl in H; inversion H.
      + destruct (gequate (t2gt x1) (t2gt y1)); simpl in H; inversion H.
        destruct (gequate (t2gt x2) (t2gt y2)); simpl in H; inversion H.
  - destruct x, y; try destruct t; try destruct t0; simpl gequate in H; unfeq; un_type_dec; try inversion H
    ; specialize (IHa1 x1 y1); specialize (IHa2 x2 y2)
    ; destruct (gequate (t2gt x1) (t2gt y1)); simpl in H1; inversion H1
    ; destruct (gequate (t2gt x2) (t2gt y2)); simpl in H1; inversion H1
    ; rewrite H3, H4 in *; intuition.
    * try rewrite H5, H7. try tauto.
    * try rewrite H6, H8. try tauto.
Qed.

Lemma tequateVSgequate : forall a b c, tequate a b = Some c <-> gequate (t2gt a) (t2gt b) = Some (t2gt c).
Proof.
  induction a; split; intros; unfold tequate in *; unfeq; un_type_dec.
  - rewrite e in *. inversion H. apply gequateId.
  - rewrite e in *. destruct b; try destruct t0; simpl in H; unfeq; un_type_dec. inversion H.
    destruct c; try destruct t0; simpl in H1; inversion H1; tauto.
  - destruct t. simpl in H.
    destruct b; try destruct t; simpl in H; unfeq; un_type_dec.
    inversion e.
    rewrite H1 in *.
    intuition.
  - symmetry in e. rewrite e in *.
    simpl in *. repeat rewrite gequateId.
    inversion H.
    simpl.
    tauto.
  - symmetry in e. rewrite e in *.
    rewrite gequateId in H.
    inversion H.
    destruct c; try destruct t; simpl in H1; inversion H1.
    apply t2gtId in H2.
    apply t2gtId in H3.
    rewrite H2, H3.
    tauto.
  - destruct b; try destruct t; simpl in H; inversion H.
    clear H.
    specialize (IHa1 b1).
    specialize (IHa2 b2).
    destruct (gequate (t2gt a1) (t2gt b1)); simpl in H1; inversion H1.
    destruct (gequate (t2gt a2) (t2gt b2)); simpl in H1; inversion H1.
    destruct c; try destruct t; simpl in H2; inversion H2.
    specialize (IHa1 c1).
    specialize (IHa2 c2).
    intuition.
    assert (Some g = Some (t2gt c1)). rewrite H3. tauto.
    assert (Some g0 = Some (t2gt c2)). rewrite H4. tauto.
    intuition.
    repeat un_type_dec.
Qed.

Lemma gequateT2GT' : forall a b c, gequate (t2gt a) (t2gt b) = Some c -> exists d, c = t2gt d.
Proof.
  induction a; intros.
  - destruct t. destruct b; try destruct t; simpl in H; unfeq; un_type_dec.
    exists (TPrimitive p).
    inversion H.
    simpl. tauto.
  - destruct b; try destruct t; simpl in H; inversion H.
    case_eq (gequate (t2gt a1) (t2gt b1)); intros; rewrite H0 in *; simpl in H; inversion H.
    case_eq (gequate (t2gt a2) (t2gt b2)); intros; rewrite H2 in *; simpl in H3; inversion H3.
    apply IHa1 in H0.
    apply IHa2 in H2.
    inversion H0. inversion H2.
    exists (TFunc x x0).
    rewrite H4, H6.
    simpl.
    tauto.
Qed.

Lemma simplifyType : forall t T c, gtfl_term_type (t2gtContext c) (term2gterm t) T -> exists T', T = t2gt T'.
Proof.
  induction t; intros; simpl in H; inversion H; clear H.
  - exists TInt.
    tauto.
  - exists TBool.
    tauto.
  - unfold t2gtContext in H2.
    destruct (c t); simpl in H2; inversion H2.
    exists s. tauto.
  - specialize (contextStaysClean t t0 c).
    intros. inversion H. symmetry in H6. unfold gtype in H6. rewrite H6 in *.
    apply IHt in H5.
    inversion H5.
    exists (TFunc t0 x1).
    rewrite H7. tauto.
  - apply IHt1 in H2.
    apply IHt2 in H3.
    inversion H2. inversion H3.
    destruct tt1; try destruct g; simpl in H5, H7; inversion H5; inversion H7.
    destruct x; try destruct t; inversion H.
    exists x2.
    rewrite H11 in *. auto.
  - exists TInt.
    tauto.
  - apply IHt1 in H3.
    apply IHt2 in H4.
    apply IHt3 in H6.
    inversion H3.
    inversion H4.
    inversion H6.
    clear IHt1 IHt2 IHt3 H3 H4 H6 c0 t0 t4 t5 H5 H0 H1 H2 ttx H7.
    rewrite H, H10, H11 in *.
    destruct x0; try destruct t; destruct x1; try destruct t; 
    simpl in H9;
    unfeq;
    un_type_dec.
    * inversion H9. exists (TPrimitive p). tauto.
    * clear tt1 tt2 tt3 H H10 H11.
      case_eq (gequate (t2gt x0_1) (t2gt x1_1)); intros; rewrite H in *; simpl in H9; inversion H9.
      case_eq (gequate (t2gt x0_2) (t2gt x1_2)); intros; rewrite H0 in *; simpl in H1; inversion H1.
      clear H1 H9 H3.
      apply gequateT2GT' in H.
      apply gequateT2GT' in H0.
      inversion H.
      inversion H0.
      exists (TFunc x0 x1).
      rewrite H1, H2.
      simpl.
      tauto.
  - exists t0. tauto.
Qed.

(*Proposition 9 - Equivalence for fully-annotated terms*)
Theorem EqFAT : forall c t T, stfl_term_type c t T <-> gtfl_term_type (t2gtContext c) (term2gterm t) (t2gt T).
Proof.
  intros.
  generalize c. clear c.
  generalize T. clear T.
  generalize t. clear t.
  induction t; simpl.
  - split; intros; inversion H; try constructor.
    destruct T; simpl in H3; inversion H3. destruct t. inversion H3.
    constructor.
  - split; intros; inversion H; try constructor.
    destruct T; simpl in H3; inversion H3. destruct t. inversion H3.
    constructor.
  - split; intros; inversion H; try constructor.
    * unfold t2gtContext. rewrite H2. simpl. tauto.
    * unfold t2gtContext in H2. destruct (c t); unfold option_map in H2; inversion H2.
      apply t2gtId in H5. rewrite H5. tauto.
  - split; intros; inversion H; try constructor. fold t2gt.
    * rewrite IHt in H5.
      rewrite contextSetLift in H5.
      assumption.
    * specialize (contextSetLift t t0 c). intros. symmetry in H6. rewrite H6 in H2.
      destruct T; try destruct t3; simpl t2gt in H5; inversion H5. rewrite H9 in H2.
      apply IHt in H2.
      apply t2gtId in H8. rewrite H8 in *.
      constructor. assumption.
  - split; intros; inversion H; try constructor.
    * clear H0 H4 H1 H6 c0 t0 t3 ttx.
      destruct tt1; try destruct t; simpl dom in *; simpl cod in *; inversion H5; inversion H7.
      rewrite H1, H4 in *.
      clear H5 H7 H1 H4 tt1_1 tt1_2.
      apply IHt1 in H2.
      apply IHt2 in H3.
      apply (TflTapp gtype_leaf GPrimitive gtfl_Tcons gequate (t2gtContext c) (term2gterm t1) (GFunc (t2gt tt2) (t2gt T)) (term2gterm t2) (t2gt tt2) (t2gt T));
      try assumption;
      simpl; tauto.
    * clear H0 H4 H1 H6 c0 t0 t3 ttx.
      destruct tt1; try destruct t; simpl dom in *; simpl cod in *; inversion H5; inversion H7.
      rewrite H1, H4 in *.
      clear H5 H7 H1 H4 tt1_1 tt1_2 H.
      assert (H2' := H2).
      assert (H3' := H3).
      apply simplifyType in H2'.
      apply simplifyType in H3'.
      inversion H2'.
      inversion H3'.

      specialize (IHt1 x).
      specialize (IHt2 x0).
      symmetry in H, H0.
      rewrite H, H0 in *.
      apply IHt1 in H2.
      apply IHt2 in H3.
      clear H2' H3' IHt1 IHt2.

      destruct x; try destruct t; simpl t2gt in H; inversion H.
      symmetry in H0.
      rewrite H0 in H4.
      apply t2gtId in H4.
      apply t2gtId in H5.
      rewrite H4, H5 in *.

      apply (TflTapp type_leaf TPrimitive stfl_Tcons tequate c t1 (TFunc x0 T) t2 x0 T);
      try assumption;
      simpl; tauto.
  - split; intros; inversion H; try constructor.
    * apply IHt1 in H2.
      apply IHt2 in H3.
      inversion H5.
      inversion H7.
      rewrite H8, H9 in *.
      apply (TflTplus gtype_leaf GPrimitive gtfl_Tcons gequate (t2gtContext c) (term2gterm t1) GInt (term2gterm t2) GInt);
      try assumption;
      simpl; constructor.
    * assert (H5' := H5).
      assert (H3' := H3).
      apply simplifyType in H5'.
      apply simplifyType in H3'.
      inversion H5'.
      inversion H3'.

      specialize (IHt1 x0).
      specialize (IHt2 x).
      symmetry in H8, H9.
      rewrite H8, H9 in *.
      apply IHt1 in H3.
      apply IHt2 in H5.

      assert (GPrimitive Int = t2gt TInt). simpl. tauto.
      rewrite H10 in H2.
      apply t2gtId in H2.
      symmetry in H2. rewrite H2 in *.
      destruct tt1; inversion H6. rewrite H13 in *.
      destruct tt2; inversion H7. rewrite H15 in *.
      unfold GPrimitive, GLeaf in H10.
      rewrite H10 in H8.
      rewrite H10 in H9.
      apply t2gtId in H8.
      apply t2gtId in H9.
      rewrite H8, H9 in *.

      apply (TflTplus type_leaf TPrimitive stfl_Tcons tequate c t1 TInt t2 TInt);
      try assumption;
      simpl; constructor.

      symmetry in H14. rewrite H14 in *. destruct x; try destruct t5; inversion H8. 
      symmetry in H12. rewrite H12 in *. destruct x0; try destruct t4; inversion H9. 
  - split; intros; inversion H; try constructor.
    * apply IHt1 in H3.
      apply IHt2 in H4.
      apply IHt3 in H6.
      clear H0 H1 H2 H5 H7 c0 t0 t4 t5 ttx IHt1 IHt2 IHt3 H.
      unfold tequate in H9.
      unfeq. unfold type_EqDec in H9.
      un_type_dec.
      inversion H9. symmetry in H0. rewrite e, H0 in *. clear H0 H9 e T tt2.
      inversion H8. rewrite H in *. clear H H8 tt1.
      apply (TflTif gtype_leaf GPrimitive gtfl_Tcons gequate (t2gtContext c) (term2gterm t1) GBool (term2gterm t2) (t2gt tt3) (term2gterm t3) (t2gt tt3) (t2gt tt3));
      try assumption;
      simpl; try constructor.
      apply gequateId.
    * assert (H3' := H3).
      assert (H4' := H4).
      assert (H6' := H6).
      apply simplifyType in H3'.
      apply simplifyType in H4'.
      apply simplifyType in H6'.
      inversion H3'.
      inversion H4'.
      inversion H6'.

      specialize (IHt1 x).
      specialize (IHt2 x0).
      specialize (IHt3 x1).
      symmetry in H10, H11, H12.
      rewrite H10, H11, H12 in *.
      apply IHt1 in H3.
      apply IHt2 in H4.
      apply IHt3 in H6.

      clear H3' H4' H6' IHt1 IHt2 IHt3 H.
      symmetry in H10, H11, H12.
      rewrite H10, H11, H12 in *.
      clear H10 H11 H12 H7 tt1 tt2 tt3 ttx H0 H1 H2 t0 t4 t5 H5 c0.

      destruct x; try destruct t; simpl t2gt in H8; inversion H8. clear H8 H t.
      apply gequateT2GT in H9.
      inversion H9.
      apply t2gtId in H0.
      rewrite H, H0, H1 in *.
      apply (TflTif type_leaf TPrimitive stfl_Tcons tequate c t1 TBool t2 x1 t3 x1 x1);
      try assumption;
      simpl; try constructor.
      unfold tequate. unf. un_type_dec.
  - split; intros; inversion H; try constructor.
    * apply IHt in H3.
      rewrite H4 in *.
      clear H0 H1 H2 H4 c0 t1 t0 tt1.

      apply (TflTassert gtype_leaf GPrimitive gtfl_Tcons gequate (t2gtContext c) (term2gterm t) (t2gt T) (t2gt T));
      simpl; try constructor.
      inversion H5.
      rewrite H5 in *.
      assumption.
    * assert (H4' := H4).
      apply simplifyType in H4'.
      inversion H4'.

      specialize (IHt x).
      rewrite H6 in *. clear H6 tt H4'.
      apply IHt in H4.

      clear IHt t1 H0 c0 H2 tt1 H1 H.
      apply t2gtId in H3.
      rewrite H3 in *.
      apply gConsByEquate in H5. inversion H5.
      apply gequateT2GT in H. inversion H.
      rewrite H0, H1 in *.
      apply (TflTassert type_leaf TPrimitive stfl_Tcons tequate c t T T);
      try assumption;
      simpl; try constructor.
Qed.