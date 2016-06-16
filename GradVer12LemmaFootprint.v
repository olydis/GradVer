Load GradVer10LemmaSfrmSubst.
Import Semantics.

Lemma dynamicASstaticFP : forall H r p,
  incl (oflatten (map (A'_s2A'_d H r) (staticFootprint p))) (footprint H r p).
Proof.
  induction p0; simpl; try apply inclEmpty.
  destruct a; try tauto.
  unfold incl. intros.
  rewrite map_app, oflattenApp, in_app_iff in H1.
  inversionx H1; try rewrite IHp0 in H2; intuition.
  simpl in *.
  destruct l; try tauto.
  unfold A'_s2A'_d in *. simpl in *.
  destruct (evale' H0 r e0); try tauto.
  destruct v0; try tauto.
  intuition.
Qed.

Lemma staticVSdynamicFP' : forall p H r o f,
  (exists e, evale' H r e = Some (vo o) /\ In (e, f) (staticFootprint' p)) ->
  In (o, f) (footprint' H r p)
  .
Proof.
  intros. unf.
  destruct p0; try tauto. simpl in *.
  destruct l; inversionx H3; try tauto.
  inversionx H2.
  rewrite H1.
  rewrite ecoincidesEmpty.
  apply in_eq.
Qed.

Lemma staticVSdynamicFP : forall p H r o f,
  (exists e, evale' H r e = Some (vo o) /\ In (e, f) (staticFootprint p)) ->
  In (o, f) (footprint H r p).
Proof.
  induction p0; intros; simpl in *; unf; try tauto.
  rewrite in_app_iff in *.
  inversionx H3.
  - apply or_introl.
    eapp staticVSdynamicFP'.
  - apply or_intror.
    eapp IHp0.
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
  destruct (ecoincides H0 r o0 l).
    common. eapp IHp0.
  split.
  - eapply footprintContainsNot.
    eauto.
  - eapply IHp0.
    eauto.
Qed.
