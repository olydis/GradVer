Load GradVer16LemmaHalloc.
Import Semantics.

(*evalphid*)
Lemma evalphidEmpty : forall H r A,
  ~ evalphid H r A [].
Proof.
  intuition.
  inversionx H1.
  tauto.
Qed.

Lemma evalphidCons : forall H r A p' pd,
  evalphid H r A (p' ::: pd) <->
  incl (footprint' H r p') A /\
  evalphi' H r (footprint' H r p') p' /\
  evalphid H r (Aexcept A (footprint' H r p')) pd.
Proof.
  induction pd; split; intros; simpl in *.
  - inversionx H1.
    tauto.
  - unf.
    inversionx H4.
    tauto.
  - unfold evalphid in *. unf.
    inversionx H1.
    * inversionx H3.
      split; auto.
      split; auto.
      eex.
      eapp in_eq.
    * lapply H2; intros.
      + unf.
        split; auto.
        split; auto.
        eex.
        eapp in_cons.
      + eex.
  - unf.
    unfold evalphid in H4. unf.
    inversionx H4.
    * eex.
      + eapp in_eq.
      + eca.
    * lapply H5; intros.
      + unfold evalphid in H4. unf.
        eex.
        eapp in_cons.
      + split; auto.
        split; auto.
        eex.
Qed.

Ltac ecad := apply evalphidCons; simpl; repeat split.
Ltac epdCommon H := 
  try (apply evalphidEmpty in H; tauto);
  unfold evalphid in H;
  inversion H as [?p temp]; clear H; inversionx temp.

(*In*)
Lemma InConsd : forall (p : phi) (p' : phi') (pd : phid),
  In p (p' ::: pd) <->
  exists pd', p = p' :: pd' /\ In pd' pd.
Proof.
  induction pd; split; intros; simpl in *.
  - tauto.
  - unf.
    tauto.
  - inversionx H0.
    * eex.
    * apply IHpd in H1. unf. subst.
      eex.
  - unf.
    inversionx H2.
    * auto.
    * apply or_intror.
      unfold dcons.
      eapp in_map_iff.
Qed.

(*phidSatisfiable*)
Lemma phidSatisfiableEmpty : ~ phidSatisfiable [].
Proof.
  unfold phidSatisfiable, evalphid.
  intuition. unf.
  tauto.
Qed.

Lemma phidSatisfiableNotEmpty : forall pd,
  phidSatisfiable pd -> exists p, In p pd.
Proof.
  intros.
  destruct pd.
  - exfalso.
    eapp phidSatisfiableEmpty.
  - eex.
    eapp in_eq.
Qed.

(*sfrmphi*)
Lemma sfrmphidEmpty : forall A,
  sfrmphid A [].
Proof.
  unfold sfrmphid.
  intuition.
Qed.

Lemma sfrmphidCons : forall A p' p,
  phidSatisfiable (p' ::: p) ->
  sfrmphid A (p' ::: p) <->
  sfrmphi' A p' /\
  sfrmphid (staticFootprint' p' ++ A) p.
Proof.
  unfold sfrmphid.
  intros; split; intros.
  - split.
    * apply phidSatisfiableNotEmpty in H0. unf.
      apply InConsd in H2. unf. subst.
      specialize (H1 (p' :: x1)).
      lapply H1; intros.
      + inversionx H0.
        assumption.
      + eapp InConsd.
    * intros.
      specialize (H1 (p' :: p1)).
      lapply H1; intros.
      + inversionx H3.
        assumption.
      + eapp InConsd.
  - unf.
    apply InConsd in H2. unf. subst.
    apply H4 in H5.
    eca.
Qed.

(* Ltac epdCommon H := 
  try (apply sfrmphidEmpty in H; tauto);
  unfold evalphid in H;
  inversion H as [?p temp]; clear H; inversionx temp. *)