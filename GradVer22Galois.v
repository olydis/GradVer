Load GradVer21Determ.
Import Semantics.

Require Import Coq.Logic.Classical_Pred_Type.

Definition PLIFTm1 (f : phi -> phi) : (pphi -> pphi) :=
  fun pp1 => fun p2 => exists p1, pp1 p1 /\ f p1 = p2.
Definition PLIFTp1 (f : phi -> phi -> Prop) : (pphi -> pphi) :=
  fun pp1 => fun p2 => exists p1, pp1 p1 /\ f p1 p2.
Definition PLIFTp3 (f : phi -> phi -> phi -> phi -> Prop) : (pphi -> pphi -> pphi -> pphi) :=
  fun pp1 pp2 pp3 => fun px => exists p1 p2 p3, pp1 p1 /\ pp2 p2 /\ pp3 p3 /\ f p1 p2 p3 px.
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
Definition GLIFTpp3 (f : phi -> phi -> phi -> phi -> Prop) (gf : gphi -> gphi -> gphi -> gphi -> Prop) : Prop :=
  forall gp1 gp2 gp3 gpx pp1 pp2 pp3 gpx',
  gGamma gp1 pp1 ->
  gGamma gp2 pp2 ->
  gGamma gp3 pp3 ->
  gAlpha (PLIFTp3 f pp1 pp2 pp3) gpx ->
  gf gp1 gp2 gp3 gpx' ->
  gphiEquals gpx' gpx.

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
    y1 = y2).

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
      eapply H2 in H10; eauto.
    intros. unf.
    assert (x0 = x1). eapp H6.
    subst. eapp H7.
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
  rename H8 into det.
  rename H7 into ff.
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
    * admit. (*contradictory*)
    * eapp det.
Admitted.

Definition liftableImplies (p : phi) (p1 p2 : phi) : Prop :=
  p1 = p2 /\
  phiImplies p1 p.

Theorem liftableImplies_ : forall p, liftable (liftableImplies p).
Proof.
  split.
    split; intros.
      inv H. assumption.
    inv H. inv H0. congruence.
  split.
    unfold pmFun. intros.
    inv H. inv H0.
    assumption.
  unfold gFun. intros.
  inv H.
  exists p1.
  exists p1.
  splau.
  splau.
  splau.
  eapp (phiImpliesTrans p1 pc p0).
  unfold gGamma' in *. simpl in *.
  destruct pa; unf; cut.
Qed.

Definition liftableAppend (p : phi) (p1 p2 : phi) : Prop :=
  p2 = p1 ++ p /\
  (good p1 -> good (p1 ++ p)) /\
  (forall p'',(good p'' /\ phiImplies p'' (p1 ++ p)) ->
   exists p' , good p'  /\ phiImplies p'  (p1) /\ phiImplies p'' (p' ++ p) /\ good (p' ++ p)).

Theorem liftableAppend_ : forall p, liftable (liftableAppend p).
Proof.
  split.
    split; intros.
      inv H. apply H2. assumption.
    inv H. inv H0. congruence.
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
    split; intros.
      intros. apply H. assumption.
    intros. admit. (*the case when implemented*)
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

Definition liftableWOacc (a : A'_s) (p1 p2 : phi) : Prop :=
  (phiImplies p1 [phiAcc (fst a) (snd a)]) /\
  (good p1 -> good p2) /\
  (minWith (fun p => phiImplies p1 p /\ (forall px, phiImplies p px /\ ~ In a (staticFootprint px) /\ ~ In a (staticFootprintX px))) phiImplies p2).

Theorem liftableWOacc_ : forall x, liftable (liftableWOacc x).
Proof.
Admitted.

Fixpoint liftableWOaccs (a : A_s) (p1 p2 : phi) : Prop :=
  match a with
  | [] => p1 = p2
  | (a' :: a) => exists pp, liftableWOacc a' p1 pp /\
                            liftableWOaccs a pp p2
  end.
  
Theorem liftableWOaccs_ : forall x, liftable (liftableWOaccs x).
Proof.
  induction x.
  - simpl.
    split.
      split; cut.
    split.
      unfold pmFun. intros. subst. auto.
    unfold gFun. intros. subst. eex.
  - simpl.
    apply liftableTrans.
    * apply liftableWOacc_.
    * assumption.
Qed.

Definition liftableWOaccsX (p : phi) (p1 p2 : phi) : Prop :=
  phiImplies p1 p /\
  liftableWOaccs (staticFootprint p) p1 p2.
  
Theorem liftableWOaccsX_ : forall x, liftable (liftableWOaccsX x).
Proof.
  intros.
  assert (li := liftableWOaccs_ (staticFootprint x)).
  unfold liftableWOaccsX.
  inv li. inv H0.
  split.
    inv H.
    split; intros; unf.
      eapply H0; eauto.
    eapply H3; eauto.
  split.
  - unfold pmFun in *. intros. unf.
    eapply H1; eauto.
  - unfold gFun in *. intros. unf.
    eapply H2 in H5; eauto.
    unf.
    exists x0.
    exists x1.
    splau.
    splau.
    splau.
    unfold gGamma' in H0.
    simpl in *.
    destruct pa.
    * unf.
      eapp phiImpliesTrans.
    * subst.
      assumption.
Qed.


Definition liftablePS2 
  (x1 : x) (y1 : x) 
  (x2 : x) (y2 : x) 
  (p1 p2 : phi) : Prop :=
  p2 = phiSubsts2 x1 y1 x2 y2 p1
  .

Theorem liftablePS2_ : forall x1 y1 x2 y2, liftable (liftablePS2 x1 y1 x2 y2).
Proof.
Admitted.


Definition liftablePS3 
  (x1 : x) (y1 : x) 
  (x2 : x) (y2 : x) 
  (x3 : x) (y3 : x) 
  (p1 p2 : phi) : Prop :=
  p2 = phiSubsts3 x1 y1 x2 y2 x3 y3 p1
  .

Theorem liftablePS3_ : forall x1 y1 x2 y2 x3 y3, liftable (liftablePS3 x1 y1 x2 y2 x3 y3).
Proof.
Admitted.

