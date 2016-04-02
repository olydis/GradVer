Require Import Coq.Unicode.Utf8 Arith Bool Ring Setoid String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Sets.Powerset.

(*set*)

(*
Inductive set (t : Type) : Type :=
| SetEmpty : set t
| SetCons : t -> set t -> set t.

Fixpoint set_in (t : Type) (x : t) (s : set t) :=
  match s with
  | SetEmpty _ => False
  | SetCons _ x' s' => x = x' \/ set_in t x s'
  end.*)

(*recusive approach... nope
Inductive type' (nested_type : Set) : Set :=
| Int : type' nested_type
| Bool : type' nested_type
| Func : nested_type -> nested_type -> type' nested_type.
*)

(**Types**)

Inductive primitive_type : Set :=
| Int : primitive_type
| Bool : primitive_type.

Inductive type : Set :=
| TPrimitive : primitive_type -> type
| TFunc : type -> type -> type.

Inductive gtype : Set :=
| GPrimitive : primitive_type -> gtype
| GFunc : gtype -> gtype -> gtype
| GUnknown : gtype.

Inductive tdom : type -> type -> Prop := 
| TDom : forall t a b, t = TFunc a b -> tdom t a.
Inductive tcod : type -> type -> Prop := 
| TCod : forall t a b, t = TFunc a b -> tcod t b.
Inductive tequate : type -> type -> type -> Prop :=
| TEquate : forall t, tequate t t t.

Inductive gdom : gtype -> gtype -> Prop := 
| GDom : forall t a b, t = GFunc a b -> gdom t a
| GDomU : gdom GUnknown GUnknown.
Inductive gcod : gtype -> gtype -> Prop := 
| GCod : forall t a b, t = GFunc a b -> gcod t b
| GCodU : gcod GUnknown GUnknown.
Inductive gequate : gtype -> gtype -> gtype -> Prop :=
| GEquatePrim : forall t, gequate (GPrimitive t) (GPrimitive t) (GPrimitive t)
| GEquateUL : forall t, gequate GUnknown t t
| GEquateUR : forall t, gequate t GUnknown t
| GEquateAbs : forall t11 t12 t21 t22 tx1 tx2, 
  gequate t11 t21 tx1 -> gequate t12 t22 tx2 -> gequate (GFunc t11 t12) (GFunc t21 t22)  (GFunc tx1 tx2).

Inductive class_gtype_cons : gtype -> gtype -> Prop :=
| GTypeConsRefl : forall t, class_gtype_cons t t
| GTypeConsUL : forall t, class_gtype_cons GUnknown t
| GTypeConsUR : forall t, class_gtype_cons t GUnknown
| GTypeConsAbs : forall t11 t12 t21 t22, 
  class_gtype_cons t11 t21 ->
  class_gtype_cons t12 t22 ->
  class_gtype_cons (GFunc t11 t12) (GFunc t21 t22).

(*checks*)
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
    tdom tt1 tt2 ->
    tcod tt1 ttx ->
    stfl_term_type c (TflTermApp stfl_T t1 t2) ttx
| StflTplus : forall c t1 t2,
    stfl_term_type c t1 (TPrimitive Int) ->
    stfl_term_type c t2 (TPrimitive Int) ->
    stfl_term_type c (TflTermPlus stfl_T t1 t2) (TPrimitive Int)
| StflTif : forall c t1 t2 tt2 t3 tt3 ttx,
    stfl_term_type c t1 (TPrimitive Bool) ->
    stfl_term_type c t2 tt2 ->
    stfl_term_type c t3 tt3 ->
    tequate tt2 tt3 ttx ->
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
| GtflTx : forall (c : gtfl_T_context) (x : tfl_Var) (t : gtfl_T), 
    c x t -> gtfl_term_type c (TflTermVar gtfl_T x) t
| GtflTn : forall c n, 
    gtfl_term_type c (TflTermNat gtfl_T n) (GPrimitive Int)
| GtflTb : forall c b, 
    gtfl_term_type c (TflTermBool gtfl_T b) (GPrimitive Bool)
| GtflTapp : forall c t1 tt1 t2 tt2 ttx,
    gtfl_term_type c t1 tt1 ->
    gtfl_term_type c t2 tt2 ->
    gdom tt1 tt2 ->
    gcod tt1 ttx ->
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
    gequate tt2 tt3 ttx ->
    gtfl_term_type c (TflTermIf gtfl_T t1 t2 t3) ttx
| GtflTlambda : forall (c : gtfl_T_context) t tt1 tt2 (x : tfl_Var),
    gtfl_term_type (tfl_T_context_set gtfl_T x tt1 c) t tt2 ->
    gtfl_term_type c (TflTermAbs gtfl_T x tt1 t) (GFunc tt1 tt2)
| GtflTassert : forall c t tt tt1,
    gtfl_term_type c t tt ->
    gtfl_Tcons tt tt1 ->
    gtfl_term_type c (TflTermAssert gtfl_T t tt1) tt1
.

(**naive subtyping relation (<:)**)
Inductive class_gsubt : gtype -> gtype -> Prop :=
| SubtUnknown : forall t, class_gsubt t GUnknown
| SubtRefl : forall t, class_gsubt t t
| SubtLift : forall t11 t12 t21 t22, 
  class_gsubt t11 t21 -> class_gsubt t12 t22 -> class_gsubt (GFunc t11 t12) (GFunc t21 t22)
.

(**powerset lifting (pseudo but sufficient so far!)**)
Inductive ptype : Set :=
| PTypeSingletonPrim : primitive_type -> ptype
| PTypeTotal : ptype
| PTypeMFunc : ptype -> ptype -> ptype.

(*subset*)
Inductive ptSpt : ptype -> ptype -> Prop :=
| PSPrefl : forall a, ptSpt a a
| PSPtot : forall a, ptSpt a PTypeTotal
| PSPlift : forall t11 t12 t21 t22,
  ptSpt t11 t12 -> ptSpt t21 t22 -> ptSpt (PTypeMFunc t11 t21) (PTypeMFunc t12 t22)
.

(*Definition 1 - Concretization (gamma)*)
Fixpoint g2pt (t : gtype) : ptype := match t with
| GPrimitive pt => PTypeSingletonPrim pt
| GFunc a b => PTypeMFunc (g2pt a) (g2pt b)
| GUnknown => PTypeTotal
end.

(*lift type*)
Fixpoint t2gt (t : type) : gtype := match t with
| TPrimitive pt => GPrimitive pt
| TFunc a b => GFunc (t2gt a) (t2gt b)
end.
Definition t2pt (t : type) : ptype := g2pt (t2gt t).
Fixpoint pt2t (t : ptype) : type := match t with (**draws sample**)
| PTypeSingletonPrim pt => TPrimitive pt
| PTypeMFunc a b => TFunc (pt2t a) (pt2t b)
| PTypeTotal => TPrimitive Bool
end.

(*Definition 2 - Type Precision (\sqsubseteq)*)
Definition gtSgt (a : gtype) (b : gtype) : Prop := ptSpt (g2pt a) (g2pt b).

(*Definition 3 - Predicate Lifting*)
Definition plift (pred : type -> type -> Prop) (a b : ptype) : Prop :=
exists a' b', pred a' b' /\ ptSpt (t2pt a') a /\ ptSpt (t2pt b') b.
Definition glift (pred : type -> type -> Prop) (a b : gtype) : Prop :=
plift pred (g2pt a) (g2pt b).

(*Definition 5 - alpha*)
Fixpoint pt2g (t : ptype) : gtype := match t with
| PTypeSingletonPrim t => GPrimitive t
| PTypeTotal => GUnknown
| PTypeMFunc a b => GFunc (pt2g a) (pt2g b)
end.

Ltac helpTac := 
  unfold gtSgt, g2pt;
  split;
  intros;
  try inversion H;
  try apply SubtRefl;
  try apply SubtUnknown;
  try apply PSPrefl;
  try apply PSPtot.

(*Proposition 1 - Type Precision == naive subtyping relation*)
Theorem typePrecision : forall t1 t2, gtSgt t1 t2 <-> class_gsubt t1 t2.
Proof.
  induction t1, t2;
  try destruct p;
  try destruct p0.

  helpTac.
  helpTac.
  helpTac.
  helpTac.
  helpTac.
  helpTac.
  helpTac.
  helpTac.
  helpTac.
  helpTac.
  
  (*hard case begin*)
  specialize (IHt1_1 t2_1).
  specialize (IHt1_2 t2_2).
  split.

  (*dir1*)
  intros.
  inversion H.

  assert (gtSgt t1_1 t2_1). unfold gtSgt. rewrite H2. apply PSPrefl.
  assert (gtSgt t1_2 t2_2). unfold gtSgt. rewrite H3. apply PSPrefl.
  apply SubtLift.
  apply IHt1_1. assumption.
  apply IHt1_2. assumption.

  apply SubtLift.
  apply IHt1_1. assumption.
  apply IHt1_2. assumption.

  (*dir2*)
  intros.
  inversion H.
  unfold gtSgt.
  apply PSPrefl.

  unfold gtSgt.
  simpl.
  apply PSPlift.
  apply IHt1_1. assumption.
  apply IHt1_2. assumption.
  (*hard case end*)

  helpTac.
  helpTac.
  helpTac.
  helpTac.
  helpTac.
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

Lemma funcLift1 : forall a a' b b',
t2pt (TFunc a b) = PTypeMFunc (g2pt a') (g2pt b')
->
(a' = t2gt a).
Proof.
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

(*
  apply GTypeConsAbs.
    apply IHt1_1.
    inversion H0;
    inversion H1;
    destruct x;
    destruct x0;
    try (contradict H4; compute; congruence).

    clear H2 H3 a a0 H0 H1 IHt1_1 IHt1_2.
    destruct t1_1, t2_1; simpl.
      exists (TPrimitive p).
      exists (TPrimitive p0).
      apply funcLift in H4.
      apply funcLift in H6.
      inversion H4.
      inversion H6.
      inversion H.
      clear H H4 H6.
      split.
        congruence.
        split; compute; apply PSPrefl.

      inversion H. apply funcLift in H4. apply funcLift in H6. inversion H4. inversion H6. congruence.

      exists (TPrimitive p).
      exists (TPrimitive p).
      split.
        congruence.
        split; compute; constructor.

      inversion H. apply funcLift in H4. apply funcLift in H6. inversion H4. inversion H6. congruence.

      apply funcLift in H4.
      apply funcLift in H6.
      inversion H4.
      inversion H6.
      inversion H.
      clear H H4 H6.
      exists x1.
      exists x0_1.
      split.
        congruence.
        split; unfold t2pt.
          symmetry in H0. rewrite H0. simpl g2pt. constructor.
          symmetry in H2. rewrite H2. simpl g2pt. constructor.

      apply funcLift in H4.
      apply funcLift in H6.
      inversion H4.
      inversion H6.
      inversion H.
      clear H H4 H6.
      exists x1.
      exists x1.
      split.
        congruence.
        split; unfold t2pt.
          symmetry in H0. rewrite H0. simpl g2pt. constructor.
          constructor.

      exists (TPrimitive p).
      exists (TPrimitive p).
      split.
        congruence.
        split; compute; constructor.

      apply funcLift in H4.
      apply funcLift in H6.
      inversion H4.
      inversion H6.
      inversion H.
      clear H H4 H6.
      exists x0_1.
      exists x0_1.
      split.
        congruence.
        split; unfold t2pt.
          constructor.
          symmetry in H2. rewrite H2. simpl g2pt. constructor.

      exists x1.
      exists x1.
      split.
        congruence.
        split; compute; constructor.

      decide 
      specialize (IHt1_1 t2_1).
      apply IHt1_1.
      .
      exists x1.
      exists x2.
        split.
          congruence.
          split; compute; constructor.

    assert (p = p0).
    congruence.
    split.
    congruence.


  unfold g2pt in H0, H1;
  inversion H0; inversion H1.*)

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

  admit.

  inversion H. 
    rewrite H2 in *. rewrite H3 in *. clear H H2 H3 H0. clear t t1_1 t1_2.
    admit.

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
    split.
      inversion H0.
      inversion H2.
      inversion H6.
      inversion H8.
      clear H0 H2 H6 H8.
      congruence.
      split; constructor.
        
    admit.

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
Theorem soundnessAlpha : forall pt gt, ptSpt pt (g2pt gt) -> .
Proof.
  apply ptype_ind.
  intros.
  apply PSPrefl.
  apply PSPrefl.
  intros.
  simpl.
  apply PSPlift; congruence.
Qed.

