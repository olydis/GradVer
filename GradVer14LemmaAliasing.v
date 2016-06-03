Load GradVer13LemmaXdot.
Import Semantics.

Definition phiNotAliasedInEnv (p : phi) (H : H) (r : rho) :=
  forall e1 e2 f, 
    edotInPhi p e1 f ->
    edotInPhi p e2 f ->
    evale' H r e1 = evale' H r e2 ->
    e1 = e2.

Lemma noAliasing : forall p H r A,
  sfrmphi [] p ->
  evalphi H r A p ->
  phiNotAliasedInEnv p H r.
Proof.
  unfold phiNotAliasedInEnv.
  intuition.
  rename H2 into ep.
  rename H3 into xd1.
  rename H4 into xd2.
  rename H5 into req.
  
  assert (xd1' := xd1).
  assert (xd2' := xd2).

  eapply edotphiEvaluates in xd1'; eauto.
  eapply edotphiEvaluates in xd2'; eauto.
  unf.
  rename H3 into sr1.
  rename H2 into sr2.

  eapply edotphiStaticFootprint in xd1; eauto.
  eapply edotphiStaticFootprint in xd2; eauto.
  
  apply footprintDistinct in ep.
  rewrite dynamicASstaticFP in ep.
  generalize p0 e2 x0 e1 x1 ep req xd1 xd2 sr1 sr2.
  clear.
  
  induction p0; intros; simpl in *; try tauto.
  destruct a; simpl in *; try (eapply IHp0; eauto; fail).
  assert (x0 = x1).
    rewrite sr1, sr2 in req.
    inversionx req.
    tauto.
  subst.
  inversionx xd1;
  inversionx xd2.
  * inversionx H1.
    inversionx H2.
    tauto.
  * inversionx H1.
    rewrite sr1 in ep.
    inversionx ep.
    contradict H1.
    generalize p0 sr2 H2. clear.
    induction p0; simpl; try tauto.
    intros.
    destruct a; simpl in *; try (eapply IHp0; eauto).
    inversionx H2.
    + inversionx H1.
      rewrite sr2.
      intuition.
    + eapply IHp0 in H1; eauto.
      destruct (evale' H0 r e0); auto.
      destruct v0; auto.
      apply in_cons.
      auto.
  * inversionx H2.
    rewrite sr2 in ep.
    inversionx ep.
    contradict H2.
    generalize p0 sr1 H1. clear.
    induction p0; simpl; try tauto.
    intros.
    destruct a; simpl in *; try (eapply IHp0; eauto).
    inversionx H1.
    + inversionx H2.
      rewrite sr1.
      intuition.
    + eapply IHp0 in H2; eauto.
      destruct (evale' H0 r e0); auto.
      destruct v0; auto.
      apply in_cons.
      auto.
  * eapply IHp0; eauto.
    destruct (evale' H0 r e0); auto.
    destruct v0; auto.
    inversionx ep.
    auto.
Qed.
