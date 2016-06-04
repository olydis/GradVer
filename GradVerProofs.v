Load GradVer20Hook.
Import Semantics.

Definition phiEquiv (p1 p2 : phi) := phiImplies p1 p2 /\ phiImplies p2 p1.

(* PROOF SECTION *)
Notation "'φ'" := phi.
Notation "'ρ'" := rho.


(* determinism? *)

Definition invPhiHolds
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    sfrmphi [] phi /\ evalphi Heap rho A phi.
Definition invTypesHold
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    forall e T, hasStaticType phi e T -> ehasDynamicType Heap rho e T.
Definition invHELPER
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    forall o C m f T,
      Heap o = Some (C, m) ->
      fieldType C f = Some T ->
      exists v, m f = Some v /\ hasDynamicType Heap v T.

Definition invNoAlias
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    sfrmphi [] phi /\ evalphi Heap rho A phi.

Definition invAll
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    invPhiHolds
      Heap rho A phi /\
    invTypesHold
      Heap rho A phi /\
    invHELPER
      Heap rho A phi.

Ltac emagicProgress :=
  repeat eexists;
  econstructor; econstructor;
  unfold evale; simpl; eauto.

Definition soundness : Prop :=
  forall pre s post initialHeap initialRho initialAccess S',
  hoare pre s post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s) :: S') (finalHeap, (finalRho, finalAccess, []) :: S') /\
    invAll finalHeap finalRho finalAccess post.

Ltac uninv :=
  unfold invAll in *;
  unfold invPhiHolds in *;
  unfold invTypesHold in *;
  unfold invHELPER in *.

Ltac applyINVtypes INVtypes H :=
  apply INVtypes in H;
  unfold ehasDynamicType in H;
  inversion H as [? xt]; clear H;
  inversion xt as [xt1 ?xd]; clear xt;
  inversionx xt1.

Ltac applyINVphi2 INVphi2 H :=
  assert (evp := INVphi2);
  apply H in evp.

Theorem staSemProgress : forall (s'' : s) (s' : list s) (pre post : phi) initialHeap initialRho initialAccess S',
  hoareSingle pre s'' post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s'' :: s') :: S') (finalHeap, (finalRho, finalAccess, s') :: S')
.
  destruct s'';
  do 7 intro;
  intro HO;
  intro INV;

  uninv;
  inversion HO; clear HO; subst;

  inversion INV as [INVphi INVtypesHELPER]; clear INV;
  inversion INVphi as [INVphi1 INVphi2]; clear INVphi;
  inversion INVtypesHELPER as [INVtypes INVHELPER]; clear INVtypesHELPER.
  - (*sMemberSet*)
    applyINVtypes INVtypes H8.
    applyINVtypes INVtypes H6.
    applyINVphi2 INVphi2 H3.
    
    inversionx evp.
    inversionx H15.
    simpl in *.
    clear H10.
    inversionx H17.
    common.
    inversionx H14.
    rewrite H7 in *.
    inversionx H16.
    
    inversionx xd0; inversionx H2; inversionx H17; inversionx H0.

    apply inclSingle in H8.

    emagicProgress.
  - (*sAssign*)
    applyINVtypes INVtypes H7.
    emagicProgress.
  - (*sAlloc*)
    assert (HnT := HnotTotal initialHeap). inversionE HnT.
    
    unfold fieldsNames in *.
    common.
    
    emagicProgress.
  - (*sCall*)
    applyINVtypes INVtypes H4.
    applyINVtypes INVtypes H6.
    applyINVtypes INVtypes H7.
    applyINVphi2 INVphi2 H8.
    clear H8.
    rename evp into H8.
    inversionx H8.
    simpl in *.
    clear H9.
    inversionx H16.
    common.
    inversionx H13.
    rewrite H7 in *. inversionx H1.
    inversionx xd; try tauto.

    (*well def*)
    remember (Method T_r m0 T_p z (Contract phi_pre phi_post) underscore) as mm.
    assert (exists fs ms, class C0 = Some (Cls C0 fs ms) /\ In mm ms).
      unfold mmethod in *.
      destruct (class C0) eqn: cc; try (inversion H5; fail).
      destruct c.
      unfold class in cc.
      apply find_some in cc.
      inversionx cc.
      unfold C_decb, string_decb, dec2decb in *.
      destruct (string_dec c C0); inversionx H1.
      apply find_some in H5. inversionx H5.
      repeat eexists; eauto.
    unf.
    assert (mWellDefined C0 mm).
      assert (CWellDefined (Cls C0 x3 x6)).
        apply pWellDefined.
        unfold class in H1.
        apply find_some in H1.
        intuition.
      unfold CWellDefined in H0.
      inversionE H0.
      apply H6.
      assumption.
    unfold mWellDefined in H0.
    rewrite Heqmm in H0.
    unf.
    rename H6 into varsPre.
    rename H0 into varsPost.
    
    remember (rhoFrom3 xresult (defaultValue T_r) xthis (vo o0) (xUserDef z) x5) as r'.
    remember (footprint initialHeap r' phi_pre) as fp.
    remember (phiType (xUserDef z) T_p :: phiType xthis (TClass C0) :: phi_pre) as phi_pre'.
    remember (phiType (xUserDef z) T_p :: phiType xthis (TClass C0) :: phiType xresult T_r :: phi_post) as phi_post'.

    (*proof strategy*)
    assert (forall a b c d, dynSem a b -> dynSemStar b c -> dynSem c d -> dynSemStar a d)
           as strat.
      intros.
      econstructor; eauto.
      eapply dynSemStarBack; eauto.

    (*Part 1: make the call*)
    assert (dynSem 
              (initialHeap, (initialRho, initialAccess, sCall x0 x1 m0 x2 :: s') :: S')
              (initialHeap, (r', fp, underscore) :: (initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s') :: S')
           ).
      subst.
      econstructor; unfold evale; simpl; eauto.
      apply evalphiPrefix in H17.
      admit. (*TODO: helper?*)
    rename H0 into step1.

    (*Part 2: method body (assumes soundness, termination, ... for method body)*)
    assert soundness as sdn. admit. (*assume that for method body*)
    unfold soundness in sdn.
    remember ((initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s') :: S') as S''.
    specialize (sdn phi_pre' underscore phi_post' initialHeap r' fp S'').
    apply sdn in H9. Focus 2. admit. (*that follows from preservation proof of Part 1!*)
    clear sdn.
    unf.
    rename H6 into step2.

    (*Part 3: call finish*)
    assert (exists initialRh', dynSem
              (x7, (x8, x9, []) :: (initialRho, Aexcept initialAccess fp , sCall x0 x1 m0 x2 :: s') :: S')
              (x7,                 (initialRh', Aexcept initialAccess fp ++ footprint x7 x8 phi_post, s') :: S')
           ).
      assert (dss := step2).

      (*heap*)
      eapply HeapGetsMoreSpecific in step2; try eassumption.
      inversionE step2.

      (*rho*)
      eapply RhoGetsMoreSpecific in dss.
      Focus 2.
        instantiate (2 := xresult).
        rewrite Heqr'.
        unfold rhoFrom3, x_decb, dec2decb.
        simpl. eauto.
      inversionE dss.

      eexists. econstructor; eauto.
        unfold mpost, mcontract.
        rewrite H5, Heqmm. simpl. tauto.

        uninv. unf.
        subst.
        inversionx H19.
        inversionx H29.
        inversionx H31.
        simpl in H33.
        repeat common.
        assumption.
    unf.
    rename H6 into step3.
    
    (*marriage*)
    subst.
    repeat eexists.
    eapply strat; eauto.
  - (*sReturn*)
    applyINVtypes INVtypes H4.
    emagicProgress.
  - (*sAssert*)
    emagicProgress.
  - (*sRelease*)
    applyINVphi2 INVphi2 H1.
    apply evalphiPrefix in evp.
    emagicProgress.
  - (*sDeclare*)
    emagicProgress.
Admitted.

Ltac emagicProgressx :=
  repeat eexists;
  econstructor; econstructor;
  unfold evale; simpl; eauto.

(*    x : T * y : T   =>  x : T                *)
(*    x : T * y = 3   =>  x : T * y : T        *)
(*    3 = 4           =>  x : T                *)
(*    3 = x           =>  x : T                *)


(*Lemma hasStaticTypePhiSubst : forall x0 e0 e1 p T0 T1,
  hasStaticType (phiSubst x0 e0 p) (ex x0) T0 /\
  hasStaticType (phiSubst x0 e0 p) e0 T0 ->
  (hasStaticType p e1 T1 -> hasStaticType (phiSubst x0 e0 p) e1 T1)
.
Proof.
Admitted.*)

Lemma phiImpliesType : forall T' p x T H,
  In (phiType x T') p ->
  phiSatisfiable p ->
  phiImplies p [phiType x T] ->
  hasDynamicType H (defaultValue T') T.
Proof.
  intros.
  unfold phiImplies, phiSatisfiable in *.
  unf.
  assert (H4' := H4).
  apply H3 in H4'. clear H3.
  eapply evalphiTypeUnlift in H1; eauto.
  inversionx H4'.
  simpl in *.
  inversionx H1.
  inversionx H12.
  rewrite H9 in H10. clear H9. inversionx H10.
  inversionx H11;
  inversionx H14;
  constructor.
Qed.

Lemma phiImpliesSatisfiable : forall p1 p2,
  phiImplies p1 p2 ->
  phiSatisfiable p1 ->
  phiSatisfiable p2.
Proof.
  unfold phiImplies, phiSatisfiable.
  intros.
  unf.
  repeat eexists.
  apply H0.
  eauto.
Qed.

Lemma FVeMaxOne : forall e x1 x2,
  In x1 (FVe e) ->
  In x2 (FVe e) ->
  x1 = x2.
Proof.
  induction e0; simpl; intros; intuition; subst; auto.
Qed.

Lemma ehasDynamicTypeRemoveRhoSubst : forall H r e x v T,
  ¬ In x (FVe e) ->
  ehasDynamicType H r e T ->
  ehasDynamicType H (rhoSubst x v r) e T.
Proof.
  intros.
  unfold ehasDynamicType, evale in *.
  rewrite evaleRemoveRhoSubst; eauto.
Qed.

Lemma evalphiImpliesAccess : forall H r p A,
  evalphi H r A p ->
  incl (footprint H r p) A.
Proof.
  induction p0; intros; simpl in *.
  - apply inclEmpty.
  - inversionx H1.
    apply IHp0 in H12.
    apply inclAexcept in H12.
    apply incl_app; auto.
Qed.

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

(* 
Lemma HSubstNOTodotInE : forall H r v' o f e,
  (forall x, r x = Some (vo o) -> ~ xdotInE e x f) ->
  evale' H r e = evale' (HSubst o f v' H) r e.
Proof.
  induction e0; intros; unfold evale in *; try tauto.
  destruct e0.
  - simpl. 
    tauto.
  - simpl.
    specialize (H1 x0).
    destruct (r x0); try tauto.
    destruct v0; try tauto.
    unfold HSubst.
    dec (o_dec o1 o0); try tauto.
    intuition.
    destruct (H0 o0); try tauto.
    destruct p0.
    simpl.
    dec (string_dec f1 f0); try tauto.
    contradict H2.
    simpl.
    tauto.
  - apply IHe0 in H1.
    simpl in *.
    tauto.
  
  
  split;
  intros;
  inversionx H1;
  try constructor;
  simpl in *.
  inversionx H2.
  
  auto.
Admitted. *)

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

Lemma FVapp : forall p1 p2,
  FV (p1 ++ p2) = FV p1 ++ FV p2.
Proof.
  induction p1; intros; simpl; try tauto.
  rewrite IHp1.
  intuition.
Qed.

Lemma FVaccListApp : forall x p l,
  FV (accListApp x l p) = map (fun asd => x) l ++ FV p.
Proof.
  induction l; simpl; try tauto.
  rewrite IHl.
  tauto.
Qed.

Lemma hasStaticTypeTransfer : forall p1 p2 e T,
  (forall x T', phiImplies p1 [phiType x T'] -> phiImplies p2 [phiType x T']) ->
  (forall e, phiImplies p1 [phiNeq e (ev vnull)] -> phiImplies p2 [phiNeq e (ev vnull)]) ->
  hasStaticType p1 e T ->
  hasStaticType p2 e T.
Proof.
  induction e0;
  intros;
  inversionx H2; eca.
Qed.


Theorem staSemSoundness : forall (s'' : s) (s' : list s) (pre post : phi) initialHeap initialRho initialAccess S',
  hoareSingle pre s'' post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s'' :: s') :: S') (finalHeap, (finalRho, finalAccess, s') :: S') /\
    invAll finalHeap finalRho finalAccess post
.
  destruct s'';
  do 7 intro;
  intro HO;
  intro INV;

  uninv;
  inversion HO; clear HO; subst;

  inversion INV as [INVphi INVtypesHELPER]; clear INV;
  inversion INVphi as [INVphi1 INVphi2]; clear INVphi;
  inversion INVtypesHELPER as [INVtypes INVHELPER]; clear INVtypesHELPER.
  - (*sMemberSet*)
    rename H6 into hstX0.
    rename H8 into hstX1.
    rename H3 into im.
    rename H9 into fht.
    rename H4 into sf.
    assert (temp := hstX0). 
      applyINVtypes INVtypes temp.
      rename x2 into v0.
      rename xd into hdtV0.
      rename H1 into irX0.
    assert (temp := hstX1).
      applyINVtypes INVtypes temp.
      rename x2 into v1.
      rename xd into hdtV1.
      rename H1 into irX1.
    applyINVphi2 INVphi2 im.
    
    inversionx evp.
    inversionx H10.
    simpl in *.
    clear H5.
    inversionx H12.
    common.
    rewrite H3 in *.
    inversionx H8.
    inversionx irX0.
    inversionx H9.
    rewrite H8 in *.
    inversionx H3.
    clear H10 H11.
    inversionx hdtV0.

    apply inclSingle in H4.

    do 4 eexists; try emagicProgress. (*progress*)
    assert (evalphi
              (HSubst o0 f0 v1 initialHeap)
              initialRho
              initialAccess
              (phiType x0 (TClass C0) :: phiAcc (ex x0) f0 :: 
                phiNeq (ex x0) (ev vnull) :: phiEq (edot (ex x0) f0) (ex x1) :: 
                phi'0)) as eph.
      eca; simpl.
        apply inclEmpty.
        eca. econstructor.
          unfold HSubst.
          unfold o_decb, f_decb, string_decb, dec2decb.
          des (o_dec o0 o0).
          rewrite H5.
          eauto.
      common.
      eca; simpl; rewrite H8.
        apply inclSingle. assumption.
        eca. constructor. tauto.
      eca; simpl.
        apply inclEmpty.
        eca. unfold evale. simpl. eauto. discriminate.
      common.
      eca; simpl.
        apply inclEmpty.
        eca. unfold evale; simpl. rewrite H8.
          unfold HSubst.
          dec (o_dec o0 o0).
          rewrite H5.
          simpl.
          dec (string_dec f0 f0).
          tauto.
      common.
      eapp evalphiHSubstAexcept.
    assert (∀ (o1 : o) (C1 : C) (m1 : f → option v) (f1 : f) (T1 : T),
        HSubst o0 f0 v1 initialHeap o1 = Some (C1, m1)
        → fieldType C1 f1 = Some T1
          → ∃ v0 : v,
            m1 f1 = Some v0 ∧ hasDynamicType (HSubst o0 f0 v1 initialHeap) v0 T1
        ) as hlp.
      intros.
      unfold HSubst in H0.
      dec (o_dec o1 o0).
        rewrite H5 in *.
        inversionx H0.
        dec (string_dec f1 f0).
          unfold fieldHasType in *.
          rewrite fht in H1. inversionx H1.
          eex.
          apply hasDynamicTypeHSubst.
          assumption.
          
          eapply INVHELPER in H1; eauto.
          unf.
          eex.
          apply hasDynamicTypeHSubst.
          assumption.
        eapply INVHELPER in H1; eauto.
        unf.
        eex.
        apply hasDynamicTypeHSubst.
        assumption.
    repeat split; repeat constructor.
    * eapply sfrmIncl; eauto. apply inclEmpty.
    * apply eph.
    * induction e0; intros; inversionx H0; simpl in *.
      + eex. eca.
      + eex. eca.
      + apply H3 in eph.
        inversionx eph. inversionx H14.
        eex.
      + apply H7 in eph.
        inversionx eph. inversionx H16. common. inversionx H15.
        unfold ehasDynamicType, evale. simpl.
        apply IHe0 in H3.
        inversionx H3. unf. common.
        rewrite H1 in *. inversionx H6.
        inversionx H2; try tauto.
        rewrite H12.
        simpl.
        eapp hlp.
    * apply hlp.
  - (*sAssign*)
    assert (HH3 := H3).
    applyINVtypes INVtypes H7.
    applyINVphi2 INVphi2 H2.
    do 4 eexists; try emagicProgress. (*progress*)
    repeat split; repeat constructor.
    * apply sfrmphiApp; try assumption.
      repeat constructor.
      assumption.
    * admit.
    * assert (evalphi initialHeap (rhoSubst x0 x1 initialRho) initialAccess
              (phi'0 ++ [phiEq (ex x0) e0])) as ep. admit.
      induction e1; intros; unfold ehasDynamicType, evale.
      + inversionx H0; simpl; eexists; split; eauto; constructor.
      + unfold rhoSubst. simpl.
        inversionx H0.
        eapply evalphiImpliesType in H8; eauto.
        inversionx H8.
        inversionx H0.
        inversionx H6.
        eexists; split; eauto.
      + inversionx H0.
        apply IHe1 in H8.
        admit.
  - (*sAlloc*)
    assert (HnT := HnotTotal initialHeap). unf.
    
    unfold fieldsNames in *.
    common.
    
    do 4 eexists; try emagicProgress. (*progress*)
    repeat split; repeat constructor.
    * generalize l H3. clear.
      induction l; intros; simpl in *.
      + repeat constructor.
        assumption.
      + repeat constructor.
        eapply sfrmIncl; eauto.
        apply inclEmpty.
    * assert (evalphi 
            (Halloc x1 c initialHeap) 
            (rhoSubst x0 (vo x1) initialRho)
            initialAccess
            phi'0) as ep.
        apply H2 in INVphi2.
        apply evalphiRemoveRhoSubst; auto.
        apply evalphiRemoveHalloc; auto.
      assert (exists l, fields c = Some l) as Heq0. eauto.
      assert (forall l,
          (evalphi
            (Halloc x1 c initialHeap)
            (rhoSubst x0 (vo x1) initialRho)
            (initialAccess)
            (phiType x0 (TClass c) :: phiNeq (ex x0) (ev vnull) :: phi'0))
          ->
          (evalphi
            (Halloc x1 c initialHeap)
            (rhoSubst x0 (vo x1) initialRho)
            (initialAccess ++ map (λ cf' : T * f, (x1, snd cf')) l)
            (accListApp x0 (map snd l)
               (phiType x0 (TClass c) :: phiNeq (ex x0) (ev vnull) :: phi'0)))
         ) as remAccList.
        clear.
        induction l; intros; simpl in *.
          rewrite app_nil_r. assumption.
        apply IHl in H0.
        eca; simpl; rewrite rhoSubstId.
          apply inclSingle. intuition.
          eca; unfold evale; simpl; try rewrite rhoSubstId; eauto.
        admit.
      apply remAccList.
      eca; simpl; try apply inclEmpty. eca; try rewrite rhoSubstId; eauto. eapply hasDynamicTypeHalloc; eauto.
      common.
      eca; simpl; try apply inclEmpty. eca; unfold evale; simpl; try rewrite rhoSubstId; eauto. discriminate.
      common.
      assumption.
    * intros.
      rewrite accListAppExtract in H1.
      assert (CL := classic (In x0 (FVe e0))).
      inversionx CL.
      + admit.
      + rewrite cons2app2 in H1.
        rewrite app_assoc in H1.
        apply hasStaticTypeNarrowing in H1; simpl.
      ++  eapply phiImpliesStaticType in H1; eauto.
          apply INVtypes in H1.
          apply ehasDynamicTypeRemoveRhoSubst; auto.
          apply ehasDynamicTypeRemoveHalloc; auto.
      ++  unfold disjoint. intros.
          dec (x_dec x0 x2); auto.
          apply or_intror.
          rewrite FVapp.
          rewrite in_app_iff.
          rewrite FVaccListApp.
          simpl.
          intuition.
          rewrite app_nil_r in H8.
          apply in_map_iff in H8.
          unf.
          tauto.
      ++  unfold disjoint. intros.
          dec (x_dec x0 x2); auto.
          apply or_intror.
          rewrite FVapp.
          rewrite in_app_iff.
          rewrite FVaccListApp.
          simpl.
          intuition.
          rewrite app_nil_r in H8.
          apply in_map_iff in H8.
          unf.
          tauto.
      ++  admit.
      ++  eex.
  - (*sCall*)
    admit.



(*
(*
Lemma evalphiSingleton : forall H r A p,
  evalphi H r A [p] <-> evalphi' H r A p.
Proof.
  split; intros.
  - inversionx H1.
    apply eval
*)
Lemma hasStaticTypeFromEq : forall e p T x,
  NotIn x (FV p) ->
  hasStaticType (p ++ [phiEq (ex x) e]) (ex x) T ->
  hasStaticType p e T.
Proof.
  intros.
  inversionx H1.
  unfold phiImplies in H4.
  
Check evalphiImpliesType.
  Print evalphi'.
  

  
  induction e0;
  intros;
  inversionx H1;
  unfold phiImplies in H4.
  - destruct v0; try constructor.
      
        apply evalphiSuffix in ep.
          destruct e0; simpl in *.
            inversionx H1.
            inversionx xd.
          inversionx H6.
          clear H18.
          inversionx H17.
          common.
          unfold rhoSubst in H10. dec (x_dec x0 x0).
            inversionx H10.
          
     intros.
      eapply phiImpliesStaticType in H2; eauto.
      + apply INVtypes in H2.
        apply INVtypes in H5.
        cons2app2
Lemma ehasDynamicTypeRhoSubst : forall e T T' x v H r,
  hasDynamicType H v T' ->
  ehasDynamicType H r (ex x) T' ->
  ehasDynamicType H r e T ->
  ehasDynamicType H (rhoSubst x v r) e T.
Proof.
  induction e0; intros; 
  unfold ehasDynamicType, evale in *;
  simpl in *; try assumption.
  - unfold rhoSubst.
    dec (x_dec x0 x1).
    * inversionE H2.
      inversionE H3.
      intuition.
      rewrite H3 in *.
      inversionx H4.
      eexists; split; eauto.
        
      eapply hasStaticTypePhiSubst in H0.
      + apply INVtypes in H0. apply INVtypes in HH3. apply INVtypes in H2. admit.
      + split; eauto.*)
      
  - (*sReturn*)
    applyINVtypes INVtypes H4.
    
    do 4 eexists; try emagicProgress. (*progress*)
    assert (evalphi 
        initialHeap 
        (rhoSubst xresult x1 initialRho) 
        initialAccess
        (phiType xresult T0 :: phiEq (ex xresult) (ex x0) :: phi'0))
          as eph.
      eca; simpl.
        apply inclEmpty.
        eca. rewrite rhoSubstId. tauto.
      eca; simpl.
        apply inclEmpty.
        eca; unfold evale; simpl.
          rewrite rhoSubstId. eauto.
          unfold rhoSubst. dec (x_dec x0 xresult); tauto.
      common.
      apply H1 in INVphi2.
      eapp evalphiRemoveRhoSubst.
    repeat split; repeat constructor.
    * simpl. assumption.
    * apply eph.
    * (* intros.
      (*destruct (classic (In xresult (FVe e0))).
      + admit.
      + *)
      
      assert (hasStaticType pre e0 T1) as hst.
        eapply hasStaticTypeTransfer in H0; eauto; intros.
          admit.
          

      
       *)
      induction e0; intros.
      + inversionx H0; eex; eca.
      + inversionx H0.
        apply H8 in eph.
        inversionx eph.
        inversionx H15.
        eca.
      + inversionx H0.
        apply H10 in eph. clear H10.
        apply IHe0 in H8. clear IHe0.
        inversionx H8.
        unf.
        inversionx eph. simpl in *. clear H11 H18.
        inversionx H17.
        common.
        inversionx H15.
        rewrite H10 in H5. inversionx H5.
        inversionx H7; try tauto. clear H16.
        eex.
      ++  unfold evale.
          simpl.
          rewrite H10.
          rewrite H11.
          simpl.
          admit.
      ++  eca.
 *)
Lemma phiImliesType2 : forall x T1 T2 p,
  phiSatisfiable p ->
  In (phiType x T1) p ->
  phiImplies p [phiType x T2] ->
  T1 = T2.
Proof.
  intros.
  unfold phiSatisfiable in *. unf.
  assert (H3' := H3).
  eapply evalphiTypeUnlift in H3'; eauto.
  apply H2 in H3.
  eapply evalphiTypeUnlift in H3; eauto; try (constructor; eauto; fail).
  inversionx H3.
  inversionx H3'.
  rewrite H9 in H8. clear H9. inversionx H8.
  inversionx H10;
  inversionx H11.
  - tauto.
  - admit.
  - 
  
          eapply phiImpliesType in H8; eauto.
      +++ eex.
      
      
      destruct (classic (In xresult (FVe e0))).
      + inversionx H0; simpl in *; try tauto.
      ++  inversionx H5; try tauto.
          eapply phiImpliesType in H7; eauto.
          eex.
        admit.
      assert (CL := classic (In xresult (FVe e0))).
      
  - (*sAssert*)
    do 4 eexists; try emagicProgress. (*progress*)
    repeat split; repeat constructor.
    * assumption.
    * assumption.
    * assumption.
  - (*sRelease*)
    applyINVphi2 INVphi2 H1.
    do 4 eexists; try emagicProgress; 
    try (apply evalphiPrefix in evp; assumption). (*progress*)
    repeat split; repeat constructor.
    * assumption.
    * apply evalphiApp in evp. intuition.
    * intros.
      apply phiImpliesSuffix in H1.
      eapply phiImpliesStaticType in H1; eauto.
  - (*sDeclare*)
    do 4 eexists; try emagicProgress. (*progress*)
    repeat split; repeat constructor.
    * assumption.
    * apply H2 in INVphi2.
      econstructor; simpl; eauto.
      + apply inclEmpty.
      + econstructor; eauto.
      ++  rewrite rhoSubstId.
          eauto.
      ++  apply hasDynamicTypeDefault.
      + common.
        econstructor; eauto.
      ++  apply inclEmpty.
      ++  eca; unfold evale; simpl; eauto.
          rewrite rhoSubstId. tauto.
      ++  simpl.
          common.
          erewrite evalphiRemoveRhoSubst; intuition.
    * intros.
      assert (evalphi initialHeap initialRho initialAccess phi'0) as sat0.
        apply H2.
        assumption.
      (*end assertion*)
      assert (phiSatisfiable [phiType x0 t; phiEq (ex x0) (ev (defaultValue' t))]) as sat1.
        unfold phiSatisfiable.
          exists newHeap.
          exists (fun x => Some (defaultValue t)).
          exists [].
          eca; simpl.
            apply inclEmpty.
            eca. apply hasDynamicTypeId.
            eca; simpl.
              apply inclEmpty.
              eca; unfold evale; simpl; eauto.
              constructor.
      (*end assertion*)
      assert (phiSatisfiable ([phiType x0 t; phiEq (ex x0) (ev (defaultValue' t))] ++ phi'0)) as sat2.
        apply phiSatisfiableApp; auto.
          unfold phiOrthogonal, disjoint.
          simpl.
          intros.
          destruct (x_dec x0 x1);
          subst;
          intuition.
          
          eex.
      (*end assertion*)
      
      rewrite cons2app2 in H0.
      assert (CL := classic (In x0 (FVe e0))).
      inversionx CL.
      + apply hasStaticTypePhiComm in H0.
        apply hasStaticTypeNarrowing in H0.
      ++  assert (forall xx t ee T,
              phiSatisfiable [phiType xx t; phiEq (ex xx) (ev (defaultValue' t))] ->
              hasStaticType [phiType xx t; phiEq (ex xx) (ev (defaultValue' t))] ee T ->
              In xx (FVe ee) ->
              ee = ex xx).
            induction ee;
            intros; simpl in *; intuition; subst; intuition.
            inversionx H5.
            eapply IHee in H7; eauto.
            subst.
            inversionx H10.
            unfold phiSatisfiable in H3.
            unf.
            assert (x2 xx <> Some (ve vnull)) as xxNotNull.
              apply H12 in H5.
              inversionx H5.
              simpl in *.
              inversionx H18.
              common.
              inversionx H16.
              rewrite H9.
              intuition.
              inversionx H3.
              contradict H17.
              tauto.
            assert (x2 xx = Some (defaultValue t0)) as xxDefault.
              inversionx H5.
              inversionx H19.
              simpl in *.
              inversionx H20.
              common.
              rewrite H9.
              auto.
            assert (x2 xx = Some (ve vnull)) as xxNull.
              apply H8 in H5.
              inversionx H5.
              simpl in *.
              inversionx H18.
              rewrite H15 in *.
              inversionx H16; auto.
              destruct t0; inversion xxDefault.
            tauto.
          eapply H3 in H1; eauto.
          subst.
          inversionx H0.
          eapply (phiImpliesType t) in H7; eauto.
      +++ eca.
          unfold evale.
          simpl.
          split; eauto.
          apply rhoSubstId.
      +++ constructor.
          tauto.
      ++  simpl.
          unfold disjoint.
          intros.
          des (x_dec x0 x1); intuition.
          constructor.
          intuition.
          inversionx H3; try tauto.
          inversionx H5; try tauto.
      ++  unfold disjoint.
          intros.
          des (x_dec x0 x1); intuition.
          constructor.
          intros.
          eapply FVeMaxOne in H1; eauto.
      ++  eex.
      ++  assumption.
      + apply hasStaticTypeNarrowing in H0.
      ++  eapply phiImpliesStaticType in H0; eauto.
          apply INVtypes in H0.
          apply ehasDynamicTypeRemoveRhoSubst; auto.
      ++  simpl.
          unfold disjoint.
          intros.
          des (x_dec x0 x1); intuition.
          apply or_intror.
          intuition.
          inversionx H3; try tauto.
          inversionx H5; try tauto.
      ++  simpl.
          unfold disjoint.
          intros.
          des (x_dec x0 x1); intuition.
          apply or_intror.
          intuition.
          inversionx H3; try tauto.
          inversionx H5; try tauto.
      ++  assumption.
      ++  eex.
Admitted.

(*
Lemma phiTrueSubst : forall a b p, phiTrue = phiSubst a b p -> p = phiTrue.
Proof.
  intros.
  destruct p; auto;
  unfold phiSubst in H0; inversion H0.
Qed.
Lemma phiTrueSubsts : forall a p, phiTrue = phiSubsts a p -> p = phiTrue.
Proof.
  induction a; intros.
  - simpl in H0.
    auto.
  - simpl in H0.
    apply IHa in H0.
    symmetry in H0.
    apply phiTrueSubst in H0.
    assumption.
Qed.
Lemma phiEqSubsts : forall a p e1 e2, phiEq e1 e2 = phiSubsts a p -> exists e1' e2', p = phiEq e1' e2' /\ e1 = eSubsts a e1' /\ e2 = eSubsts a e2'.
Proof.
  induction a; intros.
  - repeat eexists.
    simpl in H0.
    subst.
    auto.
  - simpl in H0.
    apply IHa in H0.
    inversion H0; clear H0.
    inversion H1; clear H1.
    intuition.
    subst.
    destruct p; simpl in H1; inversion H1.
    repeat eexists.
    * admit.
    * admit.
Admitted.

Lemma eSubstsVal : forall x v, eSubsts x (ev v) = (ev v).
Proof.
  induction x0; intros.
  - simpl; tauto.
  - specialize (IHx0 v0).
    assert (eSubsts (a :: x0) (ev v0) = eSubsts x0 (ev v0)).
    * admit.
    * rewrite IHx0 in H0.
      assumption.
Admitted.

*)

Ltac tmp := repeat eexists; econstructor; econstructor; eauto.
Ltac unfWT := 
  unfold wellTyped in *;
  unfold wellTypedPhi in *;
  unfold wellTypedE in *;
  simpl getType in *.

Definition consistent (H' : H) (r : rho) := forall x' o' res, r x' = Some (vo o') -> H' o' = Some res.

Lemma rhoVSeSubst : forall e'' e''' h r e' x' v', 
 evale h r e' = Some v' ->
 eSubst x' e' e'' = e''' ->
  evale h (rhoSubst x' v' r) e'' =
  evale h r e'''.
Proof.
  induction e''; intros; subst.
  - simpl. auto.
  - simpl eSubst. simpl. unfold rhoSubst.
    case_eq (x_decb x0 x'); intros; simpl; try tauto.
    rewrite H0.
    tauto.
Qed.

Lemma rhoVSphiSubst1 : forall e'' e''' h r e' x' v' a, 
 evale h r e' = Some v' ->
 phi'Subst x' e' e'' = e''' ->
  (evalphi' h (rhoSubst x' v' r) a e'' ->
  evalphi' h r a e''').
Proof.
  induction e''; intros; subst; intros; try constructor; simpl in *.
  - inversion H2; clear H2; subst.
    econstructor.
    * erewrite rhoVSeSubst in H4; eauto.
    * erewrite rhoVSeSubst in H8; eauto.
    * tauto.
  - inversion H2; clear H2; subst.
    econstructor.
    * erewrite rhoVSeSubst in H4; eauto.
    * erewrite rhoVSeSubst in H8; eauto.
    * tauto.
  - inversion H2; clear H2; subst.
    econstructor.
    * erewrite rhoVSeSubst in H7; eauto.
    * tauto.
Qed.
Lemma rhoVSphiSubst2 : forall e'' e''' h r e' x' v' a, 
 evale h r e' = Some v' ->
 phi'Subst x' e' e'' = e''' ->
  (evalphi' h r a e''' ->
  evalphi' h (rhoSubst x' v' r) a e'').
Proof.
  induction e''; intros; subst; intros; try constructor; simpl in *.
  - inversion H2; clear H2; subst.
    specialize (rhoVSeSubst e0 (eSubst x' e' e0) h r e' x' v').
    intros.
    specialize (rhoVSeSubst e1 (eSubst x' e' e1) h r e' x' v').
    intros.
    intuition.
    rewrite H8, H4 in *.
    econstructor; eauto.
  - inversion H2; clear H2; subst.
    specialize (rhoVSeSubst e0 (eSubst x' e' e0) h r e' x' v').
    intros.
    specialize (rhoVSeSubst e1 (eSubst x' e' e1) h r e' x' v').
    intros.
    intuition.
    rewrite H8, H4 in *.
    econstructor; eauto.
  - inversion H2; clear H2; subst.
    specialize (rhoVSeSubst e0 (eSubst x' e' e0) h r e' x' v').
    intros.
    intuition.
    rewrite H7 in *.
    econstructor; eauto.
Qed.



(*
Lemma hasDynamicTypeRhoSubst : forall e x0 x1 T0 T1 H r,
  ehasDynamicType H r (ex x0) T0 ->
  hasDynamicType H x1 T0 ->
  ehasDynamicType H r e T1 ->
  (exists v, evale' H r e = Some v /\ v <> vnull) ->
  ehasDynamicType H (rhoSubst x0 x1 r) e T1.
Proof.
  induction e0; intros.
  - inversionx H1.
    inversionx H5.
    inversionx H3.
    inversionx H5.
    inversionx H1.
    inversionx H3.
    econstructor.
    split; eauto.
    constructor.
  - inversionx H1.
    inversionx H5.
    inversionx H3.
    inversionx H5.
    inversionx H1.
    inversionx H3.
    des (x_dec x0 x1).
    * unfold ehasDynamicType.
      unfold evale, rhoSubst, x_decb, dec2decb. simpl. des (x_dec x1 x1).
      exists x2. intuition.
      rewrite H5 in H8.
      inversionx H8.
      unfold evale in H4. simpl in H4.
      inversionx H4.
      inversionx H1.
      rewrite H3 in H5.
      inversionx H5.
      
      inversionx H2; try constructor;
      inversionx H6; try (contradict H4; tauto);
      inversionx H7;
      econstructor.
      
      rewrite H8 in H10.
      inversionx H10.
      eauto.
    * unfold ehasDynamicType.
      rename de2 into de22.
      unfold evale, rhoSubst, x_decb, dec2decb. simpl. des (x_dec x0 x1); try (contradict de22; tauto).
      eexists; eauto.
  - inversionx H3.
    inversionx H5.
    inversionx H3.
    destruct (evale' H0 r e0) eqn: e0e; try inversionx H7.
    destruct v0; try inversionx H5.
    destruct (H0 o0) eqn: H0e; simpl in H7; try inversionx H7.
    destruct p0. simpl in *.
    specialize (IHe0 x0 x1 T0 (TClass c) H0 (rhoSubst x0 x1 r)).
    intuition.
    assert (ehasDynamicType H0 (rhoSubst x0 x1 r) e0 (TClass c)).
      econstructor; split; eauto. econstructor. eauto.
    intuition. clear H3.
    assert (∃ v0 : v, evale' H0 r e0 = Some v0 ∧ (v0 = vnull → False)).
      rewrite e0e. eexists; split; eauto. intuition. inversion H3.
    intuition. clear H3.
    inversionx H7.
    inversionx H3.
    inversionx H7.
    
    rewrite e0e in *. rewrite H0e in *. simpl in *.
    inversionx H4. inversionx H3.
    rewrite H4 in H5. inversionx H5.
    unfold ehasDynamicType.
    unfold evale. simpl.
    rewrite H9.
    destruct x3; inversionx H8.

 des (x_dec x0 x1); try (contradict de22; tauto).
      
    split.*)

(*Lemma rhoPhiHelper'' : forall e r x1 x2 v0 o0 H0 z rt v,
  r x1 = Some (vo o0) ->
  r x2 = Some v0 ->
  (∀ x0 : x, In x0 (FVe e) → xUserDef z = x0 ∨ xthis = x0) ->
  evale H0 r (eSubsts [(xthis, ex x1); (xUserDef z, ex x2)] e) v ->
  evale H0
    (rhoFrom3 xresult (defaultValue rt) xthis (vo o0) (xUserDef z) v0)
    e v.
Proof.
  unfold evale;
  induction e0; intros; simpl in *.
  - assumption.
  - unfold rhoFrom3.
    unfold x_decb, dec2decb in *.
    destruct (x_dec x0 xthis).
    * subst.
      destruct (x_dec xthis xresult); try inversion e0.
      simpl in H4.
      rewrite H1 in H4.
      assumption.
    * destruct (x_dec x0 (xUserDef z)).
      + subst.
        destruct (x_dec (xUserDef z) xresult); try inversion e0.
        simpl in H4.
        rewrite H2 in H4.
        assumption.
      + specialize (H3 x0).
        intuition.
  - destruct (evale' H0 r (eSubsts [(xthis, ex x1); (xUserDef z, ex x2)] e0)) eqn: eva;
    try (inversion H4; fail).
    destruct v2; try (inversion H4; fail).
    eapply IHe0 in eva; eauto.
    erewrite eva.
    apply H4.
Qed.

Lemma rhoPhiHelper' : forall r x1 x2 p' z H0 a0 v0 o0 rt,
  r x1 = Some (vo o0) ->
  r x2 = Some v0 ->
  (∀ x0 : x, In x0 (FV' p') → xUserDef z = x0 ∨ xthis = x0) ->
  evalphi' H0 r a0 (phi'Substs [(xthis, ex x1); (xUserDef z, ex x2)] p') ->
  evalphi' H0 (rhoFrom3 xresult (defaultValue rt) xthis (vo o0) (xUserDef z) v0) a0 p'.
Proof.
  intros.
  inversionx H4;
  unfold phi'Substs in *.
  - destruct p'; simpl in H10; inversionx H10; try constructor.
    * destruct (x_decb x0 xthis); inversionx H5.
      destruct (x_decb x0 (xUserDef z)); inversionx H6.
    * destruct (x_decb x0 xthis); inversionx H5.
      destruct (x_decb x0 (xUserDef z)); inversionx H6.
  - destruct p'; simpl in H6; inversionx H6; try constructor.
    * econstructor.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold FV'. apply in_or_app. auto.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold FV'. apply in_or_app. auto.
      + tauto.
    * destruct (x_decb x0 xthis); inversionx H5.
      destruct (x_decb x0 (xUserDef z)); inversionx H6.
    * destruct (x_decb x0 xthis); inversionx H5.
      destruct (x_decb x0 (xUserDef z)); inversionx H6.
  - destruct p'; simpl in H6; inversionx H6; try constructor.
    * econstructor.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold FV'. apply in_or_app. auto.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold FV'. apply in_or_app. auto.
      + tauto.
    * destruct (x_decb x0 xthis); inversionx H5.
      destruct (x_decb x0 (xUserDef z)); inversionx H6.
    * destruct (x_decb x0 xthis); inversionx H5.
      destruct (x_decb x0 (xUserDef z)); inversionx H6.
  - destruct p'; simpl in H6; inversionx H6; try constructor.
    unfold x_decb, dec2decb in *.
    destruct (x_dec x3 xthis); inversionx H5.
    * econstructor; eauto.
      unfold rhoFrom3.
      unfold x_decb, dec2decb in *.
      destruct (x_dec xthis xresult); try inversion e0.
      destruct (x_dec xthis xthis); try (contradict n; tauto).
      rewrite H1 in H7.
      assumption.
    * destruct (x_dec x3 (xUserDef z)); inversionx H6.
      + econstructor; eauto.
        unfold rhoFrom3.
        unfold x_decb, dec2decb in *.
        destruct (x_dec (xUserDef z) xresult); try inversion e0.
        destruct (x_dec (xUserDef z) xthis); try inversion e0.
        destruct (x_dec (xUserDef z) (xUserDef z)); try (contradict n2; tauto).
        rewrite H2 in H7.
        assumption.
      + specialize (H3 x3).
        simpl in H3.
        intuition.
    * destruct (x_decb x3 xthis); inversionx H5.
      destruct (x_decb x3 (xUserDef z)); inversionx H6.
  - destruct p'; simpl in H6; inversionx H6.
    * destruct (x_decb x3 xthis); inversionx H5.
      destruct (x_decb x3 (xUserDef z)); inversionx H6.
    * specialize (H3 x3).
      simpl in H3.
      unfold rhoFrom3, x_decb, dec2decb in *.
      destruct (x_dec x3 xthis).
      + econstructor. eauto.
      + econstructor. eauto.
Qed.

Lemma rhoPhiHelper : forall phi x1 x2 v0 o0 a z rt r H,
  (∀ x : x, In x (FV phi) → (xUserDef z) = x ∨ xthis = x) ->
  r x1 = Some (vo o0) ->
  r x2 = Some v0 ->
  evalphi H r a (phiSubsts2 xthis (ex x1) (xUserDef z) (ex x2) phi) ->
  evalphi H (rhoFrom3 xresult (defaultValue rt) xthis (vo o0) (xUserDef z) v0) a phi.
Proof.
  induction phi0; intros; inversionx H4; try constructor.
  econstructor; eauto.
  - unfold incl in *.
    intros.
    apply H9.
    destruct a; simpl in *; try inversion H4.
    unfold rhoFrom3 in *.
    unfold x_decb, dec2decb in *.
    specialize (H1 x0).
    intuition; subst.
    * destruct (x_dec (xUserDef z) xresult); try inversion e0.
      destruct (x_dec (xUserDef z) xthis); try inversion e0.
      destruct (x_dec (xUserDef z) (xUserDef z)); try (contradict n; tauto).
      unfold footprint'.
      rewrite H3.
      assumption.
    * destruct (x_dec xthis xresult); try inversion e0.
      destruct (x_dec xthis xthis); try (contradict n; tauto).
      unfold footprint'.
      rewrite H2.
      assumption.
  - eapply rhoPhiHelper'; eauto.
    * intros.
      apply H1.
      unfold FV.
      apply in_flat_map.
      eexists; intuition.
    * inversionx H14;
      try econstructor; eauto.
      unfold rhoFrom3.
      clear H11.
      destruct a; simpl in *; try inversionx H5.
      + specialize (H1 x3).
        unfold x_decb, dec2decb in *.
        intuition; subst; clear H5.
          destruct (x_dec (xUserDef z) xthis); try inversion e0.
          destruct (x_dec (xUserDef z) (xUserDef z)); try (contradict n; tauto).
          destruct (x_dec (xUserDef z) xresult); try inversion e1.
          inversionx H7.
          rewrite H3 in H6.
          inversionx H6. constructor. tauto.
        destruct (x_dec xthis xthis); try (contradict n; tauto).
        destruct (x_dec xthis xresult); try inversion e1.
        inversionx H7.
        rewrite H2 in H6.
        inversionx H6. constructor. tauto.
      + destruct (x_decb x3 xthis); try inversion H7.
        destruct (x_decb x3 (xUserDef z)); try inversion H7.
  - 
Admitted.*)
