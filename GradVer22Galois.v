Load GradVer21Determ.
Import Semantics.

Require Import Coq.Logic.Classical_Pred_Type.

Definition PLIFTm1 (f : phi -> phi) : (pphi -> pphi) :=
  fun pp1 => fun p2 => exists p1, pp1 p1 /\ f p1 = p2.
Definition PLIFTp1 (f : phi -> phi -> Prop) : (pphi -> pphi) :=
  fun pp1 => fun p2 => exists p1, pp1 p1 /\ f p1 p2.
Definition GLIFTmp1 (f : phi -> phi) (gf : gphi -> gphi -> Prop) : Prop :=
  forall gp1 gp2 pp gp2',
  gGamma gp1 pp ->
  gAlpha (PLIFTm1 f pp) gp2 ->
  gf gp1 gp2' ->
  gphiEquals gp2' gp2.
Definition GLIFTm1 (f : phi -> phi) (gf : gphi -> gphi) : Prop :=
  forall gp1 gp2 pp,
  gGamma gp1 pp ->
  gAlpha (PLIFTm1 f pp) gp2 ->
  gphiEquals (gf gp1) gp2.
Definition GLIFTpp1 (f : phi -> phi -> Prop) (gf : gphi -> gphi -> Prop) : Prop :=
  forall gp1 gp2 pp gp2',
  gGamma gp1 pp ->
  gAlpha (PLIFTp1 f pp) gp2 ->
  gf gp1 gp2' ->
  gphiEquals gp2' gp2.
Definition GLIFTpp1x (f : phi -> phi -> Prop) (gf : gphi -> gphi -> Prop) : Prop :=
  forall gp1 gp2 pp,
  gGamma gp1 pp ->
  gf gp1 gp2 ->
  gAlpha (PLIFTp1 f pp) gp2.

(* (* monotonic function with respect to phiImplies *)
Definition pmFun (f : phi -> phi -> Prop) : Prop :=
  forall x1 y1 x2 y2,
    f x1 y1 ->
    f x2 y2 ->
    phiImplies x1 x2 ->
    phiImplies y1 y2. *)

(* monotonic function with respect to phiImplies *)
Definition pmFun (f : phi -> phi -> Prop) : Prop :=
  forall x1 y1 x2 y2,
    f x1 y1 ->
    f x2 y2 ->
    phiImplies x1 x2 ->
    phiImplies y1 y2.

(* special condition *)
Definition gFun (f : phi -> phi -> Prop) : Prop :=
  forall pa pb pc, f pb pc ->
  forall p1, gGamma' (pa, pc) p1 ->
  exists p2
         p3, gGamma' (pa, pb) p2 /\
             f p2 p3 /\
             phiImplies p1 p3.

(* determinism, goodness transfer, sanity, ... *)
Definition goodFun (f : phi -> phi -> Prop) : Prop :=
  (forall x y,
    f x y ->
    good x ->
    good y)
  /\
  (forall x y1 y2,
    f x y1 ->
    f x y2 ->
    y1 = y2)
  /\
  (forall x y,
    good x ->
    f x y -> 
    exists x' y', good x' /\ phiImplies x' x /\ y <> y' /\ f x' y').

Definition liftable (f : phi -> phi -> Prop) : Prop :=
  goodFun f /\
  pmFun f /\
  gFun f.

Lemma liftableTrans : forall f1 f2,
  liftable f1 ->
  liftable f2 ->
  liftable (fun x1 x3 => exists x2, f1 x1 x2 /\ f2 x2 x3).
Proof.
  unfold liftable.
  intros. unf.
  split.
    unfold goodFun in *. unf.
    split.
      intros. unf.
      eapply H6 in H12; eauto.
    split.
      intros. unf.
      assert (x0 = x1). eapp H2.
      subst. eapp H1.
    intros. unf.
    assert (H10' := H10).
    apply H7 in H10'; auto. unf.
    assert (H12' := H12).
    admit.
  split.
    unfold pmFun in *.
    intros. unf.
    eapply H0; eauto.
  unfold gFun in *.
  intros. unf.
  assert (H8' := H8).
  eapply H3 in H8; eauto. unf.
  assert (H4' := H4).
  eapply H5 in H4; eauto. unf.
  destruct pa.
  - inv H7. inv H9. inv H6. simpl in *.
    unfold gGamma'. simpl.
    exists pb.
    exists pc.
    splau.
    splau.
    admit.
  - inv H7. inv H9. inv H6. simpl in *.
    assert (pc = x1). eapp H1. subst.
    assert (x = x3). eapp H2. subst.
    exists pb.
    exists x1.
    cut.
Admitted.

Definition simpleLift (f : phi -> phi -> Prop) : (gphi -> gphi -> Prop) :=
  fun gp1 gp2 =>
    gGood gp1 /\
    gGood gp2 /\
    fst gp1 = fst gp2 /\
    f (snd gp1) (snd gp2).

(* liftable functions are in fact simply liftable *)
Lemma GLIFT_liftable : forall f,
  goodFun f ->
  pmFun f ->
  gFun f ->
  GLIFTpp1x f (simpleLift f).
Proof.
  unfold GLIFTpp1x, PLIFTp1,
    simpleLift, pmFun, goodFun, gFun.
  intros.
  
  destruct gp1, gp2. simpl in *.
  unf. subst.
  
  rename H4 into go0.
  rename H3 into go1.
  rename H2 into ga.
  rename H0 into mon.
  rename H1 into mag.
  rename H6 into goF.
  rename H into det.
  rename H7 into ff.
  rename H9 into nconst.
  inv ga.
  clear H.
  
  constructor.
  - constructor.
    * assert (exists x, gGamma' (b0, p1) x) as ee.
        unfold gGamma'. simpl.
        destruct b0.
          inv go1. apply hasWellFormedSubtype in H. unf.
          exists x. splau. eca.
        eex.
      invE ee xx.
      eapply (mag b0) in ff; eauto.
      unf.
      exists x0.
      exists x.
      tauto.
    * intros. unf.
      apply goF in H1; auto.
      unfold gGamma' in *.
      destruct b0; simpl in *; cut.
      subst.
      inv go0.
      split. apply H. 
      inv H0; cut.
  - assumption.
  - repeat intro. unf.
    unfold gGamma' in *.
    destruct b0; simpl in *.
    * unf.
      eapply mon in H2; eauto.
    * subst.
      eapp det.
  - unfold pincl in *.
    intros.
    assert (ffx := ff).
    eapply mag in ff; eauto. unf.
    assert (gGamma' gp' x0).
      apply H0.
      eex.
    destruct gp'.
    unfold gGamma' in *. simpl in *.
    destruct b, b0; unf; subst.
    * splau.
      eapp (phiImpliesTrans p2 x0 p3).
    * assert (x0 = p1).
        eapp det. subst.
      splau.
    * apply nconst in H3; auto. unf.
      specialize (H0 x1).
      contradict H0.
      apply ex_not_not_all.
      eexists; cut.
      exists x0.
      splau.
      splau.
      eapp (phiImpliesTrans x0 x p0).
    * eapp det.
Qed.

Definition liftableAppend (p : phi) (p1 p2 : phi) : Prop :=
  p2 = p1 ++ p /\
  (good p1 -> good (p1 ++ p)) /\
  (forall p'',(good p'' /\ phiImplies p'' (p1 ++ p)) ->
   exists p' , good p'  /\ phiImplies p'  (p1) /\ phiImplies p'' (p' ++ p) /\ good (p' ++ p)).

Theorem liftableAppend_ : forall p, liftable (liftableAppend p).
Proof.
  split.
    constructor.
      intros. inv H. apply H2. assumption.
    split; intros.
      inv H. inv H0. congruence.
    exists (phiTrue :: x). exists (phiTrue :: y).
    split. rewriteRev goodConsTrue. assumption.
    split. rewrite cons2app. eapp phiImpliesSuffix.
    split. intro. symmetry in H1. apply infRecList in H1. inv H1.
    inv H0. unf.
    split. simpl. congruence.
    split. intros. rewriteRevIn goodConsTrue H2. apply H0 in H2. rewrite goodConsTrue in H2. assumption.
    intros. unf. simpl in *.
    assert (good p'' /\ phiImplies p'' (x ++ p0)) as IH. splau. eapp phiImpliesTrans. rewrite cons2app. eapp phiImpliesSuffix.
    apply H1 in IH. unf.
    exists x0. splau. splau. eapp phiImpliesTrans. repeat intro. eca. apply inclEmpty. eca. common. assumption.
  split.
    unfold pmFun. intros.
    inv H. inv H0.
    repeat intro.
    apply evalphiSymm.
    apply evalphiSymm in H.
    apply evalphiApp in H. unf.
    apply evalphiAppRev; cut.
  unfold gFun. intros.
  inv H. unf.
  unfold gGamma' in *. simpl in *.
  destruct pa.
  - assert (H00 := H0).
    apply H1 in H0. unf.
    exists x. exists (x ++ p0).
    splau.
    splau.
    split. congruence.
    splau.
    intros. unf.
    exists x.
    cut.
  - subst.
    exists pb. exists (pb ++ p0).
    splau.
    splau.
    split. congruence.
    split. assumption.
    apply H1.
Qed.

Definition minWith {T:Type} (pred : T -> Prop) (lt : T -> T -> Prop) : T -> Prop :=
    fun x => pred x /\ (forall y, pred y -> lt x y).

Definition liftableWOvar (x : x) (p1 p2 : phi) : Prop :=
  (good p1 -> good p2) /\
  (minWith (fun p => phiImplies p1 p /\ ~ In x (FV p)) phiImplies p2).

Theorem liftableWOvar_ : forall x, liftable (liftableWOvar x).
Proof.
  split.
    constructor.
      intros. apply H. assumption.
    split.
      intros. admit. (*the case when implemented*)
    intros.
      admit. (* add x=x for variable x that does not occur in x0 *)
  split.
    unfold pmFun. intros.
    inv H. inv H0.
    unfold minWith in *.
    unf.
    apply H7.
    splau.
    eapp (phiImpliesTrans x1 x2 y2).
  unfold gFun. intros.
  unfold gGamma' in *. simpl in *.
  destruct pa.
  - unf.
    eexists. (* take minimum self-framed pb (if multiple choices, look at p1) *)
    eexists. (* follows from evaluation of WO *)
    admit.
  - subst.
    exists pb.
    exists pc.
    cut.
Admitted.

