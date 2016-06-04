Load GradVer16LemmaHalloc.
Import Semantics.



Lemma odotInPhiStaticFootprint : forall p e f,
  sfrmphi [] p ->
  edotInPhi p e f ->
  In (e, f) (staticFootprint p).
Proof.
  intros.
  eapply edotphiStaticFootprintHelper; eauto.
Qed.

Lemma AexceptNOTodotInPhi : forall H r o f p A,
  sfrmphi [] p ->
  evalphi H r (Aexcept A [(o, f)]) p ->
  ~ odotInPhi H r p o f.
Proof.
  intros.
  intuition.
  apply odotedotPhi in H3.
  unf.
  eappIn edotphiStaticFootprint H5.
  assert (In (o0, f0) (footprint H0 r p0)).
    eapp staticVSdynamicFP.
  apply evalphiImpliesAccess in H2.
  apply H2 in H4.
  apply InAexceptNot in H4.
  contradict H4.
  constructor.
  tauto.
Qed.

Lemma HSubst'NOTodotInE : forall H r o v f e,
  ¬ odotInE H r e o f ->
  evale' H r e =
  evale' (HSubst o f v H) r e.
Proof.
  induction e0; intros; simpl in *; auto.
  apply not_or_and in H1.
  unf.
  apply IHe0 in H3. clear IHe0.
  rewriteRev H3. clear H3.
  apply not_and_or in H2.
  destruct (evale' H0 r e0) eqn: ee; try tauto.
  destruct v1; try tauto.
  unfold HSubst.
  dec (o_dec o1 o0); try tauto.
  inversionx H2; try tauto.
  destruct (H0 o0); try tauto.
  destruct p0. simpl in *.
  dec (string_dec f1 f0); try tauto.
Qed.

Lemma HSubstHasDynamicType : forall H v v' t o f,
  hasDynamicType H v t <->
  hasDynamicType (HSubst o f v' H) v t.
Proof.
  split; intros;
  inversionx H1;
  try (eca; fail);
  unfold HSubst in *.
  - dec (o_dec o1 o0); eca.
    * dec (o_dec o0 o0).
      rewrite H3.
      eauto.
    * rename de2 into dex.
      dec (o_dec o1 o0); try tauto.
      rewrite H3.
      eauto.
  - dec (o_dec o1 o0); try (eca; fail).
    destruct (H0 o0) eqn: Hx.
    * destruct p0.
      inversionx H3.
      eca.
    * inversionx H3.
Qed.

Lemma HSubst'NOTodotInPhi : forall H r o v f p,
  ¬ odotInPhi' H r p o f ->
  evalphi' H r (footprint' H r p) p <->
  evalphi' (HSubst o f v H) r (footprint' (HSubst o f v H) r p) p.
Proof.
  intros.
  rename H1 into H2.
  destruct p0; simpl in H2; try apply not_or_and in H2; unf;
  split; intros;
  try constructor;
  try inversionx H2;
  simpl in *.
  - eca; unfold evale in *.
    erewrite HSubst'NOTodotInE in H7; eauto.
    erewrite HSubst'NOTodotInE in H11; eauto.
  - eca; unfold evale in *.
    erewrite HSubst'NOTodotInE; eauto.
    erewrite HSubst'NOTodotInE; eauto.
  - eca; unfold evale in *.
    erewrite HSubst'NOTodotInE in H7; eauto.
    erewrite HSubst'NOTodotInE in H11; eauto.
  - eca; unfold evale in *.
    erewrite HSubst'NOTodotInE; eauto.
    erewrite HSubst'NOTodotInE; eauto.
  - inversionx H1.
    erewrite HSubst'NOTodotInE in H10; eauto.
    eca. unfold evale.
    destruct (evale' (HSubst o0 f0 v0 H0) r e0); try tauto.
    destruct v1; try tauto.
    inversionx H10; try tauto.
    inversionx H1; try tauto.
  - inversionx H1.
    erewrite HSubst'NOTodotInE; eauto.
    eca.
    unfold evale in *.
    erewrite HSubst'NOTodotInE; eauto.
  - inversionx H1.
    eca.
    rewriteRev HSubstHasDynamicType.
    assumption.
  - inversionx H1.
    eca.
    rewrite HSubstHasDynamicType.
    eauto.
Qed.

Lemma footprint'HSubst : forall H r p o f v,
  ¬ odotInPhi' H r p o f ->
  footprint' (HSubst o f v H) r p = footprint' H r p.
Proof.
  intros.
  destruct p0; simpl in *; try tauto.
  rewriteRev HSubst'NOTodotInE; eauto.
Qed.

Lemma HSubstNOTodotInPhi : forall H r o v f p A,
  ¬ odotInPhi H r p o f ->
  evalphi H r A p <->
  evalphi (HSubst o f v H) r A p.
Proof.
  induction p0; intros; simpl in *.
  - split; intros; constructor.
  - apply not_or_and in H1.
    unf.
    rename H3 into od1.
    rename H2 into od2.
    apply (IHp0 (Aexcept A (footprint' H0 r a))) in od1.
    split; intros.
    * inversionx H1.
      rewrite od1 in H12.
      eca.
      + rewrite footprint'HSubst; auto.
      + rewriteRev HSubst'NOTodotInPhi; auto.
      + rewrite footprint'HSubst; auto.
    * inversionx H1.
      rewrite footprint'HSubst in *; auto.
      rewriteRevIn od1 H12.
      eca.
      rewrite HSubst'NOTodotInPhi; eauto.
      rewrite footprint'HSubst in *; eauto.
Qed.

Lemma evalphiHSubstAexcept : forall p H r A o f x v,
  sfrmphi [] p ->
  r x = Some (vo o) ->
  evalphi H r (Aexcept A [(o, f)]) p ->
  evalphi (HSubst o f v H) r (Aexcept A [(o, f)]) p.
Proof.
  intros.
  assert (~ odotInPhi H0 r p0 o0 f0).
    eapp AexceptNOTodotInPhi.
  apply HSubstNOTodotInPhi; auto.
Qed.

