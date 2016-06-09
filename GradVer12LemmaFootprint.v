Load GradVer10LemmaSfrmSubst.
Import Semantics.

Lemma dynamicASstaticFP : forall H r p,
  footprint H r p = oflatten (map (A'_s2A'_d H r) (staticFootprint p)).
Proof.
  induction p0; try tauto.
  destruct a; try tauto.
  simpl.
  rewrite IHp0.
  unfold A'_s2A'_d. simpl.
  destruct (evale' H0 r e0); try tauto.
  destruct v0; try tauto.
Qed.

Lemma staticVSdynamicFP : forall p H r o f,
  (exists e, evale' H r e = Some (vo o) /\ In (e, f) (staticFootprint p))
  <->
  In (o, f) (footprint H r p).
Proof.
  intros.
  unfold staticFootprint, footprint, staticFootprint', footprint'.
  split; intros; unf; rewrite in_flat_map in *; unf.
  - eexists; split; eauto.
    destruct x1; inversionx H4; inversionx H2; try tauto.
    rewrite H1.
    intuition.
  - destruct x0; try inversionx H3.
    exists e0.
    rewrite in_flat_map.
    destruct (evale' H0 r e0); try inversionx H3.
    destruct v0; try inversionx H3; inversionx H2; try tauto.
    split; intuition.
    eexists; split; eauto.
    simpl.
    auto.
Qed.

Lemma staticVSdynamicFP' : forall p H r o f,
  (exists e, evale' H r e = Some (vo o) /\ In (e, f) (staticFootprint' p))
  <->
  In (o, f) (footprint' H r p).
Proof.
  intros.
  assert (sdFP := staticVSdynamicFP [p0] H0 r o0 f0).
  simpl in sdFP. repeat rewrite app_nil_r in sdFP.
  assumption.
Qed.

Lemma footprintContainsNot : forall p H r A o f,
  evalphi H r (Aexcept A [(o, f)]) p ->
  ~ In (o, f) (footprint H r p).
Proof.
  induction p0; intros; simpl in *; auto.
  inversionx H1.
  rewrite AexceptComm in H12.
  apply IHp0 in H12.
  intuition.
  contradict H12.
  apply in_app_iff in H1.
  intuition.
  apply H6 in H2.
  apply InAexceptNot in H2.
  contradict H2.
  constructor.
  tauto.
Qed.

Lemma footprintDistinct : forall H r p A,
  evalphi H r A p ->
  listDistinct (footprint H r p).
Proof.
  induction p0; intros; simpl in *; try tauto.
  inversionx H1.
  destruct a; simpl in *; try (eapply IHp0; eassumption).
  destruct (evale' H0 r e0); simpl in *; try (eapply IHp0; eassumption).
  destruct v0; simpl in *; try (eapply IHp0; eassumption).
  split.
  - eapply footprintContainsNot.
    eauto.
  - eapply IHp0.
    eauto.
Qed.
