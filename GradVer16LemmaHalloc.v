Load GradVer15LemmaPhiOrthogonality.
Import Semantics.



Lemma evale'Halloc : forall H r o C e o',
  H o = None ->
  evale' H r e = Some (vo o') <->
  evale' (Halloc o C H) r e = Some (vo o').
Proof.
  induction e0; intros; simpl in *; try tauto.
  destruct (evale' H0 r e0) eqn: ee1;
  destruct (evale' (Halloc o0 C0 H0) r e0) eqn: ee2;
  try destruct v0;
  try destruct v1;
  try tauto;
  specialize (IHe0 o1);
  intuition;
  try discriminate.
  - inversionx H2.
    unfold Halloc.
    destruct (fields C0); auto.
    dec (o_dec o0 o1); auto.
    rewrite H1 in *.
    simpl in *.
    discriminate.
  - inversionx H2.
    unfold Halloc in H4.
    destruct (fields C0); auto.
    dec (o_dec o0 o1); auto.
    simpl in *.
    destruct (find
          (λ fs' : T * string,
           if string_dec f0 (snd fs') then true else false) l); try discriminate.
Qed.

Lemma footprint'Halloc : forall H r o C p,
  H o = None ->
  footprint' H r p = footprint' (Halloc o C H) r p.
Proof.
  intros.
  destruct p0; simpl; try tauto.
  destruct (evale' H0 r e0) eqn: ee1;
  destruct (evale' (Halloc o0 C0 H0) r e0) eqn: ee2;
  try destruct v0;
  try destruct v1;
  try tauto;
  eapply evale'Halloc in H1.
  - apply H1 in ee2.
    rewrite ee2 in *.
    discriminate.
  - apply H1 in ee1.
    rewrite ee2 in *.
    discriminate.
  - apply H1 in ee2.
    rewrite ee2 in *.
    inversionx ee1.
    tauto.
  - apply H1 in ee1.
    rewrite ee2 in *.
    discriminate.
  - apply H1 in ee2.
    rewrite ee2 in *.
    discriminate.
Qed.


Lemma evaleRemoveHalloc : forall H r o C e v,
  H o = None ->
  evale H r e v ->
  evale (Halloc o C H) r e v.
Proof.
  induction e0; intros; unfold evale; simpl in *; try tauto.
  inversionx H2.
  unfold evale in *.
  destruct (evale' H0 r e0); try discriminate.
  destruct v1; try discriminate.
  specialize (IHe0 (vo o1)).
  intuition.
  rewrite H3.
  unfold Halloc.
  destruct (fields C0); try tauto.
  dec (o_dec o0 o1); try tauto.
  rewrite H1 in *.
  discriminate.
Qed.


Lemma evalphiRemoveHalloc : forall H r o C p A,
  H o = None ->
  evalphi H r A p ->
  evalphi (Halloc o C H) r A p.
Proof.
  induction p0; intros; simpl in *; try constructor.
  inversionx H2.
  eca.
  - rewriteRev footprint'Halloc; auto.
  - rewriteRev footprint'Halloc; auto.
    inversionx H12;
    eca;
    try eapp evaleRemoveHalloc.
    unfold Halloc.
    destruct (fields C0); auto.
    inversionx H4; eca.
    dec (o_dec o0 o1); eauto.
    rewrite H1 in *.
    discriminate.
  - rewriteRev footprint'Halloc; auto.
Qed.

Lemma hasDynamicTypeHalloc : forall o C H fs,
  fields C = Some fs ->
  hasDynamicType (Halloc o C H) (vo o) (TClass C).
Proof.
  intros.
  eca.
  unfold Halloc.
  rewrite H1.
  dec (o_dec o0 o0).
  eauto.
Qed.

Lemma accListAppExtract : forall x A l,
  accListApp x l A = accListApp x l [] ++ A.
Proof.
  induction l; simpl; try tauto.
  rewrite IHl. tauto.
Qed.

Lemma ehasDynamicTypeRemoveHalloc : forall H r e T o C,
  H o = None ->
  ehasDynamicType H r e T ->
  ehasDynamicType (Halloc o C H) r e T.
Proof.
  unfold ehasDynamicType.
  intros.
  unf.
  eapply evaleRemoveHalloc in H2; eauto.
  eexists; eax.
  inversionx H4; eca.
  inversionx H1.
  unfold Halloc.
  destruct (fields C0); eauto.
  dec (o_dec o0 o1); eauto.
  rewrite H4 in H5.
  discriminate.
Qed.