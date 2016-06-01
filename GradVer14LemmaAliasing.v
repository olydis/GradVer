Load GradVer13LemmaXdot.
Import Semantics.

Definition phiNotAliasedInR (p : phi) (r : rho) :=
  forall x1 x2 f, 
    xdotInPhi p x1 f ->
    xdotInPhi p x2 f ->
    r x1 = r x2 ->
    x1 = x2.

Lemma noAliasing : forall p H r A,
  sfrmphi [] p ->
  evalphi H r A p ->
  phiNotAliasedInR p r.
Proof.
  unfold phiNotAliasedInR.
  intuition.
  rename H2 into ep.
  rename H3 into xd1.
  rename H4 into xd2.
  rename H5 into req.
  
  assert (xd1' := xd1).
  assert (xd2' := xd2).

  eapply xdotphiEvaluates in xd1'; eauto.
  eapply xdotphiEvaluates in xd2'; eauto.
  unf.
  rename H3 into sr1.
  rename H2 into sr2.

  eapply xdotphiStaticFootprint in xd1; eauto.
  eapply xdotphiStaticFootprint in xd2; eauto.
  
  apply footprintDistinct in ep.
  rewrite dynamicASstaticFP in ep.
  generalize p0 x2 x0 x1 x3 ep req xd1 xd2 sr1 sr2.
  clear.
  
  induction p0; intros; simpl in *.
  - inversion xd1.
  - destruct a; simpl in *; try (eapply IHp0; eauto; fail).
    assert (x3 = x0).
      rewrite sr1, sr2 in req.
      inversionx req.
      tauto.
    subst.
    inversionx xd1;
    inversionx xd2.
    * inversionx H0.
      inversionx H1.
      tauto.
    * inversionx H0.
      rewrite sr1 in ep.
      inversionx ep.
      contradict H0.
      generalize p0 sr2 H1. clear.
      induction p0; simpl; try tauto.
      intros.
      destruct a; simpl in *; try (eapply IHp0; eauto).
      inversionx H1.
      + inversionx H0.
        rewrite sr2.
        intuition.
      + eapply IHp0 in H0; eauto.
        destruct (r x1); auto.
        destruct v0; auto.
        apply in_cons.
        auto.
    * inversionx H1.
      rewrite sr2 in ep.
      inversionx ep.
      contradict H1.
      generalize p0 sr1 H0. clear.
      induction p0; simpl; try tauto.
      intros.
      destruct a; simpl in *; try (eapply IHp0; eauto).
      inversionx H0.
      + inversionx H1.
        rewrite sr1.
        intuition.
      + eapply IHp0 in H1; eauto.
        destruct (r x2); auto.
        destruct v0; auto.
        apply in_cons.
        auto.
    * eapply IHp0; eauto.
      destruct (r x4) eqn: rr; auto.
      destruct v0; auto.
      inversionx ep.
      auto.
Qed.
