Load GradVer16LemmaHalloc.
Import Semantics.


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


Lemma evale'eSubsts2RhoFrom3 : forall H r z v2 x1 x2 T_r vo1 e,
  incl (FVe e) [xUserDef z; xthis] ->
  r x2 = Some v2 ->
  r x1 = Some (vo vo1) ->
  evale' H r (eSubsts [(xthis, x1); (xUserDef z, x2)] e) =
  evale' H (rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) (xUserDef z) v2) e.
Proof.
  induction e0; intros; simpl in *.
  - tauto.
  - apply inclSingle in H1.
    unfold xSubsts, rhoFrom3.
    inversionx H1; simpl.
    * dec (x_dec (xUserDef z) (xUserDef z)).
      assumption.
    * inversionx H4; tauto.
  - rewrite IHe0; auto.
Qed.

Lemma footprint'PhiSubsts2RhoFrom3 : forall H r z v2 x1 x2 T_r vo1 a,
  incl (FV' a) [xUserDef z; xthis] ->
  r x2 = Some v2 ->
  r x1 = Some (vo vo1) ->
  footprint' H r (phi'Substs [(xthis, x1); (xUserDef z, x2)] a) =
  footprint' H (rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) (xUserDef z) v2) a.
Proof.
  intros.
  destruct a; simpl in *; try tauto.
  erewrite evale'eSubsts2RhoFrom3; auto.
Qed.

Lemma evale'PhiSubsts2RhoFrom3 : forall H r z v2 x1 x2 T_r vo1 e,
  incl (FVe e) [xUserDef z; xthis] ->
  r x2 = Some v2 ->
  r x1 = Some (vo vo1) ->
  evale' H
    r
    (eSubsts [(xthis, x1); (xUserDef z, x2)] e) =
  evale' H
    (rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) (xUserDef z) v2)
    e.
Proof.
  induction e0; intros; simpl in *.
  - tauto.
  - unfold xSubsts, rhoFrom3.
    apply inclSingle in H1.
    inversionx H1; simpl.
    * dec (x_dec (xUserDef z) (xUserDef z)).
      assumption.
    * inversionx H4; try tauto.
  - rewrite IHe0; auto.
Qed.

Lemma inclApp : forall {T : Type} (A1 A2 B : list T),
  incl (A1 ++ A2) B ->
  incl A1 B /\ incl A2 B.
Proof.
  unfold incl.
  intros.
  intuition.
Qed.

Lemma evalphi'PhiSubsts2RhoFrom3 : forall H r z v2 x1 x2 T_r vo1 a,
  incl (FV' a) [xUserDef z; xthis] ->
  r x2 = Some v2 ->
  r x1 = Some (vo vo1) ->
  evalphi' H
    r
    (footprint' H
      (rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) (xUserDef z) v2)
      a) 
    (phi'Substs [(xthis, x1); (xUserDef z, x2)] a) ->
  evalphi' H
    (rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) (xUserDef z) v2)
    (footprint' H
      (rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) (xUserDef z) v2)
      a)
    a.
Proof.
  intros.
  destruct a; inversionx H4; common; simpl in *.
  - constructor.
  - apply inclApp in H1. unf.
    eca; unfold evale;
    erewrite evale'eSubsts2RhoFrom3 in *; eauto.
  - apply inclApp in H1. unf.
    eca; unfold evale;
    erewrite evale'eSubsts2RhoFrom3 in *; eauto.
  - eca; unfold evale;
    erewrite evale'eSubsts2RhoFrom3 in *; eauto.
  - apply inclSingle in H1.
    unfold xSubsts, rhoFrom3 in *.
    inversionx H1; simpl in *; eca.
    * dec (x_dec (xUserDef z) xresult). clear de2.
      dec (x_dec (xUserDef z) xthis). clear de2.
      dec (x_dec (xUserDef z) (xUserDef z)).
      rewrite H2 in *. assumption.
    * inversionx H4; try tauto.
      dec (x_dec xthis xresult). clear de2.
      dec (x_dec xthis xthis).
      rewrite H3 in *. assumption.
Admitted.

Lemma evalphiPhiSubsts2RhoFrom3 : forall H r z v2 x1 x2 T_r vo1 p A,
  incl (FV p) [xUserDef z; xthis] ->
  r x2 = Some v2 ->
  r x1 = Some (vo vo1) ->
  evalphi
    H
    r
    A
    (phiSubsts2 xthis x1 (xUserDef z) x2 p) ->
  evalphi
    H
    (rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) (xUserDef z) v2)
    A 
    p.
Proof.
  induction p0; intros; simpl; try constructor.
  inversionx H2.
  simpl in *.
  inversionx H4.
  eca.
  - erewrite footprint'PhiSubsts2RhoFrom3 in H9; eauto.
    unfold incl. intros.
    intuition.
  - apply inclApp in H1. unf.
    erewrite (footprint'PhiSubsts2RhoFrom3 _ _ _ _ _ _ T_r) in H14; eauto.
    eapp evalphi'PhiSubsts2RhoFrom3.
  - apply inclApp in H1. unf.
    erewrite (footprint'PhiSubsts2RhoFrom3 _ _ _ _ _ _ T_r) in H15; eauto.
Qed.

Lemma disjointAexcept : forall A B,
  disjoint A B ->
  Aexcept A B = A.
Proof.
  induction A;
  intros;
  simpl;
  try tauto.
  rewrite cons2app in H0.
  apply disjointSplitA in H0. unf.
  apply IHA in H2. rewrite H2.
  destruct (negb (existsb (A_d'_decb a) B)) eqn: cl; try tauto.
  apply negb_false_iff in cl.
  apply existsb_exists in cl. unf.
  specialize (H1 x0).
  intuition.
  contradict H0.
  constructor.
  undecb.
  destruct a, x0. simpl in *.
  dec (o_dec o0 o1); simpl in *; try discriminate.
  dec (string_dec f0 f1); simpl in *; try discriminate.
  tauto.
Qed.

Lemma evalphiFootprintAccess : ∀ p H r A,
       evalphi H r A p ->
       evalphi H r (footprint H r p) p.
Proof.
  induction p0; intros; simpl in *; eca.
  - intuition.
  - inversionx H1.
    assumption.
  - inversionx H1.
    rewrite AexceptAppFirst.
    rewrite AexceptSame.
    simpl.
    assert (disjoint (footprint H0 r p0) (footprint' H0 r a)).
      apply evalphiImpliesAccess in H12.
      unfold incl, disjoint in *.
      intros.
      specialize (H12 x0).
      destruct (classic (In x0 (footprint H0 r p0)));
      intuition.
      apply InAexceptNot in H2.
      intuition.
    rewrite disjointAexcept; auto.
    eapp IHp0.
Qed.


Lemma inclAexceptDisjoint : forall A B C,
  incl A (Aexcept B C) ->
  disjoint A C.
Proof.
  unfold incl, disjoint.
  intros.
  specialize (H0 x0).
  destruct (classic (In x0 A)); intuition.
  apply InAexceptNot in H2.
  auto.
Qed.

Lemma evalphiRemoveAexcept : forall H r p A1 A2,
  disjoint (footprint H r p) A2 ->
  evalphi H r A1 p ->
  evalphi H r (Aexcept A1 A2) p.
Proof.
  induction p0; intros; simpl in *; try constructor.
  inversionx H2.
  apply disjointSplitA in H1. unf.
  eca.
  - unfold incl, disjoint in *.
    intros.
    eapp InAexceptConstr.
    specialize (H2 a0).
    intuition.
  - rewrite AexceptComm.
    eapp IHp0.
Qed.

Lemma evalphiElemWise : forall H r A1 A2 p,
  (forall p', In p' p ->
  (evalphi' H r A1 p' -> evalphi' H r A2 p')
  ) ->
  (evalphi  H r A1 p  -> evalphi  H r A2 p ).
Proof.
  induction p0;
  intros; try constructor.
  inversionx H2.
  eca.
  - eapply evalphi'incl in H12; eauto.
    eapply H1 in H12.
    * eapp evalphi'ImpliesIncl.
    * constructor.
      tauto.
  - assert (evalphi H0 r A2 p0) as ep.
    * eapp IHp0.
      + intros.
        apply H1 in H3; auto.
        apply in_cons.
        auto.
      + eapp evalphiAexcept.
    * eapply evalphiImpliesAccess in H13.
      apply inclAexceptDisjoint in H13.
      eapp evalphiRemoveAexcept.
Qed.
  

Lemma inclxSubsts : forall x0 x1 x2 z x,
  let xUDz := xUserDef z in
  In x [xUDz; xthis; xresult] ->
  In (xSubsts [(xthis, x1); (xUDz, x2); (xresult, x0)] x) [x2; x1; x0].
Proof.
    intros.
    assert (x_decb xUDz xthis = false) as xd1. dec (x_dec xUDz xthis). tauto.
    assert (x_decb xUDz xresult = false) as xd2. dec (x_dec xUDz xresult). tauto.
    assert (x_decb xUDz xUDz = true) as xd3. dec (x_dec xUDz xUDz). tauto.
    unfold xSubsts.
    inversionx H0; subst; simpl;
    try rewrite xd3;
    try tauto.
    inversionx H1; subst; simpl;
    try rewrite xd3;
    try tauto.
    inversionx H0; subst; simpl;
    try rewrite xd3;
    try tauto.
Qed.

Lemma incleSubsts : forall x0 x1 x2 z e0,
  let xUDz := xUserDef z in
  incl (FVe e0) [xUDz; xthis; xresult] ->
  incl (FVe (eSubsts [(xthis, x1); (xUDz, x2); (xresult, x0)] e0)) [x2; x1; x0].
Proof.
  induction e0; intros; simpl in *.
  - apply inclEmpty.
  - apply inclSingle.
    apply inclSingle in H0.
    eapp inclxSubsts.
  - eapp IHe0.
Qed.

Lemma inclPhiSubsts3 : forall x0 x1 x2 z p p',
  let xUDz := xUserDef z in
  incl (FV p) [xUDz; xthis; xresult] ->
  In p' (phiSubsts3 xthis x1 (xUserDef z) x2 xresult x0 p) ->
  incl (FV' p') [x2; x1; x0].
Proof.
  induction p0; intros; simpl in *; inversionx H1;
  apply inclApp in H0;
  unf.
  - destruct a; simpl in *.
    * apply inclEmpty.
    * apply inclApp in H1. unf.
      apply incl_app;
      eapp incleSubsts.
    * apply inclApp in H1. unf.
      apply incl_app;
      eapp incleSubsts.
    * eapp incleSubsts.
    * apply inclSingle.
      apply inclSingle in H1.
      eapp inclxSubsts.
  - eapp IHp0.
Qed.


Lemma incl2PhiSubst3 : 
  forall fH' iR fR' x0 x1 x2 vo1 v2 vresult z e0,
  let xUDz := xUserDef z in
  let fR := rhoSubst x0 vresult iR in
  incl (FVe e0) [xUDz; xthis; xresult] ->
  iR x1 = Some (vo vo1) ->
  iR x2 = Some v2 ->
  fR' xthis = Some (vo vo1) ->
  fR' xUDz = Some v2 ->
  fR' xresult = Some vresult ->
  x0 <> x2 ->
  x0 <> x1 ->
  evale' fH' fR (eSubsts [(xthis, x1); (xUDz, x2); (xresult, x0)] e0) =
  evale' fH' fR' e0.
Proof.
  induction e0; intros; simpl in *.
  - tauto.
  - assert (x_decb xUDz xthis = false) as xd1. dec (x_dec xUDz xthis). tauto.
    assert (x_decb xUDz xresult = false) as xd2. dec (x_dec xUDz xresult). tauto.
    assert (x_decb xUDz xUDz = true) as xd3. dec (x_dec xUDz xUDz). tauto.
    apply inclSingle in H0.
    subst xUDz fR.
    inversionx H0.
      rewrite H4.
      unfold xSubsts, rhoSubst. simpl.
      rewrite xd3.
      dec (x_dec x2 x0); tauto.
    inversionx H8.
      rewrite H3.
      unfold xSubsts, rhoSubst. simpl.
      dec (x_dec x1 x0); tauto.
    inversionx H0.
      rewrite H5.
      unfold xSubsts, rhoSubst. simpl.
      dec (x_dec x0 x0); tauto.
    tauto.
  - subst fR xUDz.
    erewrite IHe0; eauto.
Qed.

  (*LHS: xthis, xresult, xUDz
       --> x1, x0, x2 
       --> iR x1, vresult, iR x2
       --> vo1, vresult, v2 *)
  (*RHS: xthis, xresult, xUDz
     --> fR' xthis, fR' xresult, fR' xUDz
     --> r' xthis, vresult, r' xUDz
     --> vo1, vresult, v2 *)

Lemma evale'2PhiSubsts3 : 
  forall fH' iR fR' x0 x1 x2 vo1 v2 vresult z e,
  let xUDz := xUserDef z in
  let fR := rhoSubst x0 vresult iR in
  incl (FVe e) [xUDz; xthis; xresult] ->
  iR x1 = Some (vo vo1) ->
  iR x2 = Some v2 ->
  fR' xthis = Some (vo vo1) ->
  fR' xUDz = Some v2 ->
  fR' xresult = Some vresult ->
  x0 <> x2 ->
  x0 <> x1 ->
  x1 <> x2 ->
  evale' fH' fR (eSubsts [(xthis, x1); (xUserDef z, x2); (xresult, x0)] e) =
  evale' fH' fR' e.
Proof.
  induction e0; intros; simpl in *.
  - tauto.
  - subst fR.
    apply inclSingle in H0.
    unfold xSubsts, rhoSubst. simpl.
    inversionx H0; subst.
      dec (x_dec (xUserDef z) xthis). clear de2.
      dec (x_dec (xUserDef z) (xUserDef z)).
      rewrite H4.
      dec (x_dec x2 x0); tauto.
    inversionx H9; simpl.
      rewrite H3.
      dec (x_dec x1 x0); tauto.
    inversionx H0; simpl.
      rewrite H5.
      dec (x_dec x0 x0); tauto.
    tauto.
  - subst fR.
    erewrite IHe0; eauto.
Qed.

Lemma footprint'2PhiSubsts3 : 
  forall fH' iR fR' x0 x1 x2 vo1 v2 vresult z p,
  let xUDz := xUserDef z in
  let fR := rhoSubst x0 vresult iR in
  incl (FV' p) [xUDz; xthis; xresult] ->
  iR x1 = Some (vo vo1) ->
  iR x2 = Some v2 ->
  fR' xthis = Some (vo vo1) ->
  fR' xUDz = Some v2 ->
  fR' xresult = Some vresult ->
  x0 <> x2 ->
  x0 <> x1 ->
  x1 <> x2 ->
  footprint' fH' fR (phi'Substs [(xthis, x1); (xUserDef z, x2); (xresult, x0)] p) =
  footprint' fH' fR' p.
Proof.
  intros.
  destruct p0; simpl in *; try tauto.
  subst fR.
  erewrite evale'2PhiSubsts3; eauto.
Qed.

Lemma footprint2PhiSubsts3 : 
  forall fH' iR fR' x0 x1 x2 vo1 v2 vresult z p,
  let xUDz := xUserDef z in
  let fR := rhoSubst x0 vresult iR in
  incl (FV p) [xUDz; xthis; xresult] ->
  iR x1 = Some (vo vo1) ->
  iR x2 = Some v2 ->
  fR' xthis = Some (vo vo1) ->
  fR' xUDz = Some v2 ->
  fR' xresult = Some vresult ->
  x0 <> x2 ->
  x0 <> x1 ->
  x1 <> x2 ->
  footprint fH' fR (phiSubsts3 xthis x1 xUDz x2 xresult x0 p) =
  footprint fH' fR' p.
Proof.
  induction p0; intros; simpl in *; try tauto.
  apply inclApp in H0. unf.
  subst fR xUDz.
  rewrite IHp0; auto.
  erewrite footprint'2PhiSubsts3; eauto.
Qed.

Lemma AexceptDisjoint : forall A1 A2,
  disjoint A1 A2 ->
  Aexcept A1 A2 = A1.
Proof.
  unfold disjoint, Aexcept, except.
  induction A1; intros; simpl in *; try tauto.
  assert (~ (existsb (A_d'_decb a) A2) = true).
    intuition.
    apply existsb_exists in H1.
    unf.
    specialize (H0 x0).
    intuition.
    undecb.
    destruct a, x0. simpl in *.
    dec (o_dec o0 o1); simpl; try discriminate.
    dec (string_dec f0 f1); simpl; try discriminate.
    tauto.
  apply not_true_is_false in H1.
  rewrite H1. simpl.
  rewrite IHA1; try tauto.
  intros.
  specialize (H0 x0).
  intuition.
Qed.

Lemma evalphi2PhiSubsts3 : 
  forall fH' iR fR' x0 x1 x2 vo1 v2 vresult z ppost fA',
  let xUDz := xUserDef z in
  let fR := rhoSubst x0 vresult iR in
  incl (FV ppost) [xUDz; xthis; xresult] ->
  iR x1 = Some (vo vo1) ->
  iR x2 = Some v2 ->
  fR' xthis = Some (vo vo1) ->
  fR' xUDz = Some v2 ->
  fR' xresult = Some vresult ->
  x0 <> x2 ->
  x0 <> x1 ->
  x1 <> x2 ->
  evalphi
    fH'
    fR'
    fA'
    ppost ->
  evalphi
    fH'
    fR
    (footprint fH' fR (phiSubsts3 xthis x1 xUDz x2 xresult x0 ppost))
    (phiSubsts3 xthis x1 xUDz x2 xresult x0 ppost).
Proof.
  induction ppost; intros; simpl in *; try constructor.
  eca.
  - intuition.
  - rename H9 into ep.
    destruct a;
    inversion ep as [? | ? ? ? ? ? ? ? ? invc ? inva invb];
    subst; clear ep invb;
    simpl in *.
    * constructor.
    * apply inclApp in H0. unf.
      apply inclApp in H9. unf.
      inversionx inva.
      eca; unfold evale in *;
      subst fR xUDz;
      erewrite incl2PhiSubst3; eauto.
    * apply inclApp in H0. unf.
      apply inclApp in H9. unf.
      inversionx inva.
      eca; unfold evale in *;
      subst fR xUDz;
      erewrite incl2PhiSubst3; eauto.
    * apply inclApp in H0. unf.
      inversionx inva.
      eca; unfold evale in *;
      subst fR xUDz;
      erewrite incl2PhiSubst3; eauto.
    * assert (x_decb xUDz xthis = false) as xd1. dec (x_dec xUDz xthis). tauto.
      assert (x_decb xUDz xresult = false) as xd2. dec (x_dec xUDz xresult). tauto.
      assert (x_decb xUDz xUDz = true) as xd3. dec (x_dec xUDz xUDz). tauto.
      rewrite cons2app in H0.
      apply inclApp in H0. unf.
      apply inclSingle in H9.
      inversionx inva.
      subst fR. unfold rhoSubst, xSubsts, rhoFrom3 in *. simpl.
      inversionx H9; subst; simpl.
        rename H16 into ee.
        rewrite H4 in ee. inversionx ee.
        eca. rewrite xd3. dec (x_dec x2 x0); tauto.
      inversionx H0; subst; simpl.
        rename H16 into ee.
        rewrite H3 in ee. simpl in ee. inversionx ee.
        eca. dec (x_dec x1 x0); tauto.
      inversionx H9; subst; simpl.
        rename H16 into ee.
        rewrite H5 in ee. inversionx ee.
        eca. dec (x_dec x0 x0); tauto.
      tauto.
  - rename H9 into ep.
    inversion ep as [? | ? ? ? ? ? ? ? ? invc ? inva invb]. subst. clear ep inva invc.
    assert (disjoint (footprint fH' fR' ppost) (footprint' fH' fR' a)).
      apply evalphiImpliesAccess in invb.
      apply inclAexceptDisjoint in invb.
      apply invb.
    subst fR xUDz.
    apply inclApp in H0. unf.
    erewrite footprint2PhiSubsts3; eauto.
    erewrite footprint'2PhiSubsts3; eauto.
    eapply IHppost in invb; eauto.
    erewrite footprint2PhiSubsts3 in invb; eauto.
    
    rewrite AexceptAppFirst.
    rewrite AexceptSame. simpl.
    rewrite AexceptDisjoint; auto.
Qed.


Lemma A_sSubstsApp : forall m A1 A2,
  A_sSubsts m (A1 ++ A2) =
  A_sSubsts m A1 ++ A_sSubsts m A2.
Proof.
  induction A1; intros; try tauto.
  destruct a.
  unfold A_sSubsts in *. simpl.
  rewrite IHA1.
  tauto.
Qed.

Lemma A_sSubstsFP' : forall m p,
  A_sSubsts m (staticFootprint' p) =
  staticFootprint' (phi'Substs m p).
Proof.
  unfold A_sSubsts;
  destruct p0;
  tauto.
Qed.

Lemma sfrmeSubsts : forall x0 x1 x2 z e A,
  sfrme A e ->
  sfrme (A_sSubsts [(xthis, x1); (xUserDef z, x2); (xresult, x0)] A) (eSubsts [(xthis, x1); (xUserDef z, x2); (xresult, x0)] e).
Proof.
  induction e0; intros; simpl in *; try (constructor; fail).
  inversionx H0.
  eapply IHe0 in H5; eauto.
  eca.
  unfold A_sSubsts.
  apply in_flat_map.
  exists (phiAcc (eSubsts [(xthis, x1); (xUserDef z, x2); (xresult, x0)] e0) f0).
  split.
  - unfold phiSubsts, phi'Substs.
    apply in_map_iff.
    exists (phiAcc e0 f0).
    intuition.
    apply in_map_iff.
    eex. tauto.
  - constructor.
    tauto.
Qed.

Lemma sfrmphiPhiSubsts3 : forall x0 x1 x2 z p A,
  sfrmphi A p ->
  sfrmphi (A_sSubsts [(xthis, x1); (xUserDef z, x2); (xresult, x0)] A) (phiSubsts [(xthis, x1); (xUserDef z, x2); (xresult, x0)] p).
Proof.
  induction p0; intros; try tauto.
  inversionx H0.
  eapply IHp0 in H2; eauto.
  eca.
  - inversionx H1; simpl; eca;
    eapp sfrmeSubsts.
  - rewrite A_sSubstsApp in H2.
    rewrite A_sSubstsFP' in H2.
    assumption.
Qed.
