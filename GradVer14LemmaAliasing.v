Load GradVer13LemmaXdot.
Import Semantics.

Definition phiNotAliasedInEnv (p : phi) (H : H) (r : rho) :=
  forall e1 e2 f,
    In (e1, f) (staticFootprintX p) ->
    In (e2, f) (staticFootprintX p) ->
    evale' H r e1 = evale' H r e2 ->
    e1 = e2.
(* 
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

  eapply jointFootprint in xd1'; eauto.
  eapply jointFootprint in xd2'; eauto.
  unf.
  rename H4 into sr1.
  rename H3 into sr2.

  eapply sfrmphiVSsfpX in xd1; eauto.
  eapply sfrmphiVSsfpX in xd2; eauto.
  simpl in *.
  
  apply footprintDistinct in ep.
  rewrite dynamicASstaticFP in ep.
  
  unfold A'_s2A'_d in *.
  simpl in *.
  
  destruct (evale' H0 r e1) eqn: ee1; try discriminate.
  destruct (evale' H0 r e2) eqn: ee2; try discriminate.
  simpl in *.
  destruct v0; try discriminate.
  destruct v1; try discriminate.
  inversionx sr1.
  inversionx sr2.
  inversionx req.
  
  generalize ee1 ee2 p0 ep xd1 xd2.
  clear.
  
  induction p0; intros; simpl in *; try tauto.
  destruct a; simpl in *; try (eapply IHp0; eauto; fail).
  inversionx xd1;
  inversionx xd2.
  * inversionx H1.
    inversionx H2.
    tauto.
  * inversionx H1.
    rewrite ee1 in ep.
    inversionx ep.
    contradict H1.
    generalize p0 ee2 H2. clear.
    induction p0; simpl; try tauto.
    intros.
    destruct a; simpl in *; try (eapply IHp0; eauto).
    inversionx H2.
    + inversionx H1.
      rewrite ee2.
      intuition.
    + eapply IHp0 in H1; eauto.
      destruct (evale' H0 r e0); auto.
      destruct v0; auto.
      apply in_cons.
      auto.
  * inversionx H2.
    rewrite ee2 in ep.
    inversionx ep.
    contradict H2.
    generalize p0 ee1 H1. clear.
    induction p0; simpl; try tauto.
    intros.
    destruct a; simpl in *; try (eapply IHp0; eauto).
    inversionx H1.
    + inversionx H2.
      rewrite ee1.
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
 *)