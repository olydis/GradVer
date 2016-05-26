Load GradVerLemmas.
Import Semantics.

Definition phiEquiv (p1 p2 : phi) := phiImplies p1 p2 /\ phiImplies p2 p1.

(* PROOF SECTION *)
Notation "'φ'" := phi.
Notation "'ρ'" := rho.

(* determinism? *)

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

Definition invPhiHolds
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    sfrmphi [] phi /\ evalphi Heap rho A phi.
Definition invTypesHold
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    forall e T, hasStaticType phi e T -> ehasDynamicType Heap rho e T.

Definition invAll
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    invPhiHolds
      Heap rho A phi /\
    invTypesHold
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
  unfold invTypesHold in *.

Ltac applyINVtypes INVtypes H :=
  apply INVtypes in H;
  unfold ehasDynamicType in H;
  inversion H as [? xt]; clear H;
  inversion xt as [xt1 ?xd]; clear xt;
  inversionx xt1.

Ltac applyINVphi2 INVphi2 H :=
  apply H in INVphi2.

Ltac common :=
  repeat rewrite AexceptEmpty in *;
  unfold neq in *;
  repeat match goal with
    | [ H : option_map _ ?T = _ |- _ ] =>
                        destruct T eqn: ?;
                        inversionx H
    | [ H : evale _ _ _ _ |- _ ] => unfold evale in H; simpl in H
  end.

Theorem staSemProgress : forall (s'' : s) (s' : list s) (pre post : phi) initialHeap initialRho initialAccess S',
  hoareSingle pre s'' post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s'' :: s') :: S') (finalHeap, (finalRho, finalAccess, s') :: S')
.
  destruct s'';
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro HO;
  intro INV;

  uninv;
  inversion HO; clear HO; subst;

  inversion INV as [INVphi INVtypes]; clear INV;
  inversion INVphi as [INVphi1 INVphi2]; clear INVphi;
  try rewrite getTypeImpliesStaticType in *.
  - applyINVtypes INVtypes H9.
    applyINVtypes INVtypes H7.
    applyINVphi2 INVphi2 H3.
    
    inversionx INVphi2.
    inversionx H16.
    simpl in *.
    clear H11.
    inversionx H18.
    common.
    inversionx H15.
    rewrite H8 in *.
    inversionx H17.
    
    inversionx xd0; try (inversionx H2).

    unfold incl in H9.
    specialize (H9 (o1,f0)).

    emagicProgress.
  - applyINVtypes INVtypes H3.
    emagicProgress.
  - assert (HnT := HnotTotal initialHeap). inversionE HnT.
    
    unfold fieldsNames in *.
    common.
    
    emagicProgress.
  - applyINVtypes INVtypes H4.
    applyINVtypes INVtypes H6.
    applyINVtypes INVtypes H7.
    applyINVphi2 INVphi2 H8.
    clear H8.
    rename INVphi2 into H8.
    inversionx H8.
    simpl in *.
    clear H11.
    inversionx H18.
    common.
    inversionx H15.
    rewrite H7 in *. inversionx H1.
    inversionx xd; try (contradict H16; tauto).

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
    inversionE H0.
    inversionE H1.
    inversionE H0.
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
    intuition.
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
      apply evalPhiPrefix in H19.
      admit. (*TODO: helper?*)
    rename H0 into step1.

    (*Part 2: method body (assumes soundness, termination, ... for method body)*)
    assert soundness as sdn. admit. (*assume that for method body*)
    unfold soundness in sdn.
    remember ((initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s') :: S') as S''.
    specialize (sdn phi_pre' underscore phi_post' initialHeap r' fp S'').
    apply sdn in H11. Focus 2. admit. (*that follows from preservation proof of Part 1!*)
    clear sdn.
    inversion H11; clear H11.
    inversion H0; clear H0.
    inversion H6; clear H6.
    inversion H0; clear H0.
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

        uninv. inversionE H11. inversionE H17.
        subst.
        inversionx H21.
        inversionx H31.
        inversionx H33.
        simpl in H35.
        repeat common.
        assumption.
    inversionE H0.
    rename H6 into step3.
    
    (*marriage*)
    subst.
    repeat eexists.
    eapply strat; eauto.
  - applyINVtypes INVtypes H4.
    emagicProgress.
  - emagicProgress.
  - applyINVphi2 INVphi2 H1.
    apply evalPhiPrefix in INVphi2.
    emagicProgress.
  - emagicProgress.
Proof.

Lemma inclEmpty : forall {T : Type} (x : list T), incl [] x.
Proof.
  unfold incl.
  intros.
  inversion H0.
Qed.


Lemma sfrmeIncl : forall p a b, incl a b -> sfrme a p -> sfrme b p.
Proof.
  intros.
  inversionx H1; try constructor.
  apply H0.
  assumption.
Qed.

Lemma sfrm'Incl : forall p a b, incl a b -> sfrmphi' a p -> sfrmphi' b p.
Proof.
  intros.
  inversionx H1; try constructor;
  eapply sfrmeIncl; eauto.
Qed.

Lemma sfrmIncl : forall p a b, incl a b -> sfrmphi a p -> sfrmphi b p.
Proof.
  induction p0; intros.
  - constructor.
  - inversionx H1.
    eapply sfrm'Incl in H2; eauto.
    econstructor; eauto.
    eapply IHp0; eauto.
    Search incl.
    apply incl_app.
    * apply incl_appl.
      apply incl_refl.
    * apply incl_appr.
      assumption.
Qed.

Ltac emagicProgressx :=
  repeat eexists;
  econstructor; econstructor;
  unfold evale; simpl; eauto.

Lemma evalphiTypeUnlift : forall x T H r A p,
  In (phiType x T) p -> evalphi H r A p -> evalphi' H r A (phiType x T).
Proof.
  induction p0; intros; inversionx H1.
  - inversionx H2.
    inversionx H11.
    econstructor; eauto.
  - apply IHp0; auto.
    inversionx H2.
    apply evalphiAexcept in H13.
    assumption.
Qed.

Lemma hasDynamicTypeHSubst : forall H v T o f x,
  hasDynamicType H v T -> hasDynamicType (HSubst o f x H) v T.
Proof.
  intros.
  inversionx H1; try constructor.
  destruct (o_dec o1 o0) eqn: oo.
  - subst.
    econstructor.
    unfold HSubst.
    unfold o_decb, dec2decb.
    rewrite oo.
    rewrite H3.
    eauto.
  - econstructor.
    unfold HSubst.
    unfold o_decb, dec2decb.
    rewrite oo.
    rewrite H3.
    eauto.
Qed.

Theorem staSemSoundness : forall (s'' : s) (s' : list s) (pre post : phi) initialHeap initialRho initialAccess S',
  hoareSingle pre s'' post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s'' :: s') :: S') (finalHeap, (finalRho, finalAccess, s') :: S') /\
    invAll finalHeap finalRho finalAccess post
.
  destruct s'';
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro HO;
  intro INV;

  uninv;
  inversion HO; clear HO; subst;

  inversion INV as [INVphi INVtypes]; clear INV;
  inversion INVphi as [INVphi1 INVphi2]; clear INVphi;
  try rewrite getTypeImpliesStaticType in *.
  - applyINVtypes INVtypes H9.
    applyINVtypes INVtypes H7.
    applyINVphi2 INVphi2 H3.
    
    inversionx INVphi2.
    inversionx H16.
    simpl in *.
    clear H11.
    inversionx H18.
    common.
    inversionx H15.
    rewrite H8 in *.
    inversionx H17.
    
    inversionx xd0; try (inversionx H2).

    unfold incl in H9.
    specialize (H9 (o1,f0)).

    assert (In (o1, f0) initialAccess). apply H9. constructor. tauto.
      clear H9.

    do 4 eexists; try emagicProgress. (*progress*)
    repeat split.
    * constructor.
    * constructor.
    * repeat constructor.
    * repeat constructor.
    * eapply sfrmIncl; eauto. apply inclEmpty.
    * econstructor; eauto; simpl.
        apply inclEmpty.
        econstructor; eauto. econstructor.
          unfold HSubst.
          unfold o_decb, f_decb, string_decb, dec2decb.
          destruct (o_dec o1 o1); try (contradict n; tauto).
          rewrite H12.
          eauto.
      common.
      econstructor; eauto; simpl; rewrite H8.
        unfold incl. intros. inversionx H2; try inversion H6. assumption.
        econstructor; eauto.
      econstructor; eauto; simpl.
        apply inclEmpty.
        econstructor; eauto.
      common.
      econstructor; eauto; simpl.
        apply inclEmpty.
        econstructor; eauto. unfold evale; simpl. rewrite H8.
          unfold HSubst.
          unfold o_decb, f_decb, string_decb, dec2decb.
          destruct (o_dec o1 o1); try (contradict n; tauto).
          rewrite H12.
          simpl.
          destruct (string_dec f0 f0); try (contradict n; tauto).
          tauto.
      common.
      admit.
    * unfold ehasDynamicType.
      induction e0; intros.
      + exists v0.
        unfold evale.
        simpl.
        intuition.
        inversionx H2; constructor.
      + destruct (x_dec x3 x0); subst.
      ++  exists (vo o1).
          unfold evale.
          simpl.
          intuition.
          inversionx H2.
          inversionx H9. inversionx H2. econstructor. unfold HSubst, o_decb, dec2decb. rewrite H12. destruct (o_dec o1 o1); eauto. contradict n. tauto.
          inversionx H2. inversion H6.
          inversionx H6. inversion H2.
          inversionx H2. inversion H6.
          unfold NotIn in *.
          contradict H5.
          generalize phi'0 H6.
          clear.
          induction phi'0; intros; inversionx H6. constructor. tauto.
          intuition.
          unfold FV in *.
          apply in_flat_map.
          apply in_flat_map in H1.
          inversionE H1.
          exists x1.
          intuition.
      ++  inversionx H2.
          inversionx H9. inversionx H2. contradict n. tauto.
          inversionx H2. inversion H6.
          inversionx H6. inversion H2.
          inversionx H2. inversion H6.
          eapply evalphiTypeUnlift in H6; eauto.
          inversionx H6.
          exists v0.
          unfold evale.
          simpl.
          intuition.
          apply hasDynamicTypeHSubst.
          assumption.
      + inversionx H2.
        apply IHe0 in H11.
        inversionE H11.
        inversionx H2.
        inversionx H7.

          SearchAbout not.
   inversionx CL.
      + 
 admit. assert (hasStaticType pre e0 T1).
      + inversionx H2; try constructor; try assumption.
          inversionx H7.
            inversionx H2.

      unfold evale.
      

    try (unfold evale; simpl; eauto; fail);
    try (apply inclEmpty; fail);
    common;
    try rewrite H7.
    * apply H9. constructor. tauto.
    * unfold incl. intros. inversionx H0; try inversion H2.
      apply H9. constructor. tauto.
    * constructor. tauto.
    * unfold HSubst.
      unfold o_decb, f_decb, string_decb, dec2decb.
      destruct (o_dec o0 o0); try (contradict n; tauto).
      rewrite H8.
      simpl.
      destruct (string_dec f0 f0); try (contradict n; tauto).
      tauto.
    * admit.
    * Print hasStaticType. inversionx H0; simpl.
      
      

SearchAbout incl.

    emagicProgress.
  - applyINVtypes INVtypes H3.
    emagicProgress.
  - assert (HnT := HnotTotal initialHeap). inversionE HnT.
    
    unfold fieldsNames in *.
    common.
    
    emagicProgress.
  - applyINVtypes INVtypes H4.
    applyINVtypes INVtypes H6.
    applyINVtypes INVtypes H7.
    applyINVphi2 INVphi2 H8.
    inversionx H8.
    simpl in *.
    clear H11.
    inversionx H18.
    common.
    inversionx H15.
    rewrite H7 in *. inversionx H1.
    inversionx xd; try (contradict H16; tauto).

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
    inversionE H0.
    inversionE H1.
    inversionE H0.
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
    intuition.
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
      apply evalPhiPrefix in H19.
      admit. (*TODO: helper?*)
    rename H0 into step1.

    (*Part 2: method body (assumes soundness, termination, ... for method body)*)
    assert soundness as sdn. admit. (*assume that for method body*)
    unfold soundness in sdn.
    remember ((initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s') :: S') as S''.
    specialize (sdn phi_pre' underscore phi_post' initialHeap r' fp S'').
    apply sdn in H11. Focus 2. admit. (*that follows from preservation proof of Part 1!*)
    clear sdn.
    inversion H11; clear H11.
    inversion H0; clear H0.
    inversion H6; clear H6.
    inversion H0; clear H0.
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

        uninv. inversionE H11. inversionE H17.
        subst.
        inversionx H21.
        inversionx H31.
        inversionx H33.
        simpl in H35.
        repeat common.
        assumption.
    inversionE H0.
    rename H6 into step3.
    
    (*marriage*)
    subst.
    repeat eexists.
    eapply strat; eauto.
  - applyINVtypes INVtypes H4.
    emagicProgress.
  - emagicProgress.
  - applyINVphi2 INVphi2 H1.
    apply evalPhiPrefix in H1.
    emagicProgress.
  - emagicProgress.
Proof.


Lemma phiImpliesRefl : forall x, phiImplies x x.
Proof.
  unfold phiImplies.
  auto.
Qed.
Hint Resolve phiImpliesRefl.

Lemma AexceptReverse : forall a1 a2, Aexcept (a1 ++ a2) a2 = a1.
Admitted.

Lemma evalPhiImplies : forall H' r A' q1 q2,
  phiImplies q1 q2 -> evalphi H' r A' q1 -> evalphi H' r A' q2.
Proof.
  intros.
  unfold phiImplies in H0.
  specialize (H0 H' r A').
  intuition.
Qed.

Lemma InAexcept : forall x a a', In x (Aexcept a a') -> In x a.
Proof.
  unfold Aexcept.
  unfold except.
  induction a; intros.
  - compute in H0.
    inversion H0.
  - simpl.
    simpl filter in H0.
    destruct (existsb (A_d'_decb a) a'); simpl in H0.
    * apply IHa in H0.
      auto.
    * inversion H0; auto.
      apply IHa in H1.
      auto.
Qed.

Lemma mapSplitFst : forall {A B : Type} (x : list (A * B)), map fst x = fst (split x).
Admitted.
Lemma mapSplitSnd : forall {A B : Type} (x : list (A * B)), map snd x = snd (split x).
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

Lemma phiImpliesConj : forall a b c, phiImplies a (phiConj b c) -> phiImplies a b.
Admitted.*)

Ltac tmp := repeat eexists; econstructor; econstructor; eauto.
Ltac unfWT := 
  unfold wellTyped in *;
  unfold wellTypedPhi in *;
  unfold wellTypedE in *;
  simpl getType in *.

Lemma evaleTClass : forall G e' C' h r, getType G e' = Some (TClass C') -> (let res := evale h r e' in res = Some vnull \/ exists o', res = Some (vo o')).
Admitted. (* TODO: entangle *)

Definition consistent (H' : H) (r : rho) := forall x' o' res, r x' = Some (vo o') -> H' o' = Some res.

Lemma exists_forall : forall {A : Type} (b : A -> Prop) (c : Prop), ((exists a, b a) -> c) -> (forall a, b a -> c).
Proof.
  intros.
  apply H0.
  eauto.
Qed.
  

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


(* playground *)
Open Scope string_scope.

Notation "AA '⊢sfrme' ee" := (sfrme AA ee) (at level 90).

Print sfrme.
Print dynSem.