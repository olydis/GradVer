Load GradVerLemmas.
Import Semantics.

Definition phiEquiv (p1 p2 : phi) := phiImplies p1 p2 /\ phiImplies p2 p1.

(* PROOF SECTION *)
Notation "'φ'" := phi.
Notation "'ρ'" := rho.

Ltac des P :=
    destruct P as [de1 | de2];
    try (inversion de1; fail);
    try (contradict de2; tauto; fail);
    try (rewrite de1 in *);
    try (clear de1).

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
  assert (evp := INVphi2);
  apply H in evp.

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
  do 7 intro;
  intro HO;
  intro INV;

  uninv;
  inversion HO; clear HO; subst;

  inversion INV as [INVphi INVtypes]; clear INV;
  inversion INVphi as [INVphi1 INVphi2]; clear INVphi.
  - applyINVtypes INVtypes H9.
    applyINVtypes INVtypes H7.
    applyINVphi2 INVphi2 H3.
    
    inversionx evp.
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
    rename evp into H8.
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
    apply evalPhiPrefix in evp.
    emagicProgress.
  - emagicProgress.
Admitted.

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

Lemma infRecList : forall {T : Type} (x : T) (xs : list T), ~ x :: xs = xs.
Proof.
  intuition.
  apply lengthId in H0.
  simpl in H0.
  contradict H0.
  auto with arith.
Qed.

Lemma phiImpliesStaticType : forall p1 p2 e T, phiImplies p1 p2 -> hasStaticType p2 e T -> hasStaticType p1 e T.
Proof.
  induction e0; intros; inversionx H1; try constructor.
  - unfold phiImplies in *.
    intros.
    apply H4.
    apply H0.
    assumption.
  - econstructor; eauto.
Qed.

(*    x : T * y : T   =>  x : T                *)
(*    x : T * y = 3   =>  x : T * y : T        *)
(*    3 = 4           =>  x : T                *)
(*    3 = x           =>  x : T                *)

Lemma evalphiImpliesType : forall H r A p x T,
  evalphi H r A p -> phiImplies p [phiType x T] -> ehasDynamicType H r (ex x) T.
Proof.
  intros.
  apply H2 in H1.
  inversionx H1.
  inversionx H12.
  unfold ehasDynamicType.
  eexists; eauto.
Qed.

Lemma edotSubst : forall m e f, exists e' f', (eSubsts m (edot e f)) = edot e' f'.
Proof.
  intros; simpl; repeat eexists; eauto.
Qed.

Lemma hasStaticTypePhiSubst : forall x0 e0 e1 p T0 T1,
  hasStaticType (phiSubst x0 e0 p) (ex x0) T0 /\
  hasStaticType (phiSubst x0 e0 p) e0 T0 ->
  (hasStaticType p e1 T1 -> hasStaticType (phiSubst x0 e0 p) e1 T1)
.
Proof.
Admitted.

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

Definition A_sSubsts m (A : A_s) : A_s := 
  flat_map (fun p =>
    match p with
    | phiAcc x f => [(x, f)]
    | _ => []
    end
  )
  (phiSubsts m (map (fun a => phiAcc (fst a) (snd a)) A)).

Definition FVA_s (A : A_s) : list x := map fst A.

Definition FVmTarg (m : list (x * e)) : list x := flat_map FVe (map snd m).

Check in_flat_map.

Fixpoint FVeo (e : e) : option x := 
  match e with
  | ev _ => None
  | ex x => Some x
  | edot e _ => FVeo e
  end.

Definition mMapsTo (m : list (x * e)) (x' : x) : Prop :=
  exists m', In m' m /\ FVeo (snd m') = Some x'.

Definition mMapsToUnique (m : list (x * e)) (x' : x) : Prop :=
  forall f1 f2 e1 e2, 
      In (f1, e1) m -> 
      In (f2, e2) m -> 
      FVeo e1 = Some x' -> 
      FVeo e2 = Some x' -> 
      f1 = f2
.

(* sfrme (A_sSubsts (a => b) (a.f)) (eSubsts (a => b) (b.f)) -> sfrme (a.f) (b.f) *)
Lemma sfrmeSubst : forall m e a,
      (forall x, mMapsToUnique m x /\ (mMapsTo m x -> (~ In x (FVe e) /\ ~ In x (FVA_s a)))) ->
      sfrme (A_sSubsts m a) (eSubsts m e) ->
      sfrme a e.
Proof.
  intros.
  destruct e0; try constructor.
  simpl in *;
  try apply inclEmpty;
  try constructor.
  inversionx H1.
  destruct e0; simpl in H0; inversionx H2.
  constructor.
  destruct (find (λ r : x * e, x_decb x1 (fst r)) m0) eqn: ff.
  - destruct p0.
    subst.
    apply find_some in ff.
    inversionx ff.
    unfold x_decb, dec2decb in H2.
    des (x_dec x1 (fst (x2, ex x0))); try inversionx H2.
    simpl in *.
    unfold A_sSubsts in H4.
    apply in_flat_map in H4.
    inversionx H4.
    inversionx H2.
    destruct x3; inversionx H4; inversionx H2.
    unfold phiSubsts, phi'Substs in H3.
    simpl in *.
    apply in_map_iff in H3.
    inversionx H3.
    inversionx H2.
    apply in_map_iff in H4.
    inversionE H4.
    inversionx H2.
    destruct x4.
    simpl in *.
    destruct (find (λ r : x * e, x_decb x3 (fst r)) m0) eqn: fff1; inversionx H3.
    * destruct p0. destruct e0; inversionx H4.
      apply find_some in fff1.
      inversionx fff1.
      unfold x_decb, dec2decb in *. simpl in *.
      des (x_dec x3 x4); inversionx H3.
      specialize (H0 x0).
      inversionx H0.
      unfold mMapsToUnique in H3.
      eapply H3 in H1; eauto.
      subst.
      assumption.
    * specialize (H0 x0).
      inversionx H0.
      assert (mMapsTo m0 x0).
        eexists; eauto.
      intuition.
      unfold FVA_s in H6.
      rewrite in_map_iff in H6.
      contradict H6.
      eexists; split; eauto.
      auto.
  - inversionx H3.
    unfold A_sSubsts in H4.
    apply in_flat_map in H4.
    inversionx H4.
    inversionx H1.
    destruct x0; inversionx H3; try inversionx H1.
    unfold phiSubsts in H2.
    apply in_map_iff in H2.
    inversionx H2.
    inversionx H1.
    unfold phiSubsts, phi'Substs in H2.
    destruct x0; inversionx H2.
    * destruct (find (λ r : x * e, x_decb x0 (fst r)) m0) eqn: ff1.
      + destruct p0.
        destruct e0; inversionx H4.
        apply find_some in ff1.
        inversionx ff1.
        unfold x_decb, dec2decb in H2.
        simpl in H2.
        des (x_dec x0 x2); inversionx H2.
        apply in_map_iff in H3.
        inversionx H3.
        inversionx H2.
        inversionx H3.
        destruct x3.
        simpl in *.
        specialize (H0 x1).
        inversionx H0.
        assert (mMapsTo m0 x1).
          eexists; eauto.
        intuition.
      + inversionx H4.
        apply in_map_iff in H3.
        inversionx H3.
        inversionx H1. 
        inversionx H2.
        destruct x0.
        simpl.
        assumption.
    * apply in_map_iff in H3.
      inversionx H3.
      inversionx H1.
      inversionx H2.
Qed.

Lemma sfrmeSubstEmpty : forall m e,
      sfrme [] (eSubsts m e) -> sfrme [] e.
Proof.
  intros.
  destruct e0; try constructor.
  simpl in *.
  inversionx H0.
  inversion H3.
Qed.

Lemma eSubstsEmpty : forall p, eSubsts [] p = p.
Proof.
  induction p0; simpl; try tauto.
  rewrite IHp0. tauto.
Qed.

Lemma phiSubstsEmpty : forall p, phiSubsts [] p = p.
Proof.
  induction p0; simpl; try tauto.
  rewrite IHp0.
  unfold phi'Substs.
  destruct a; repeat rewrite eSubstsEmpty; tauto.
Qed.

Lemma sfrmphi'Subst : forall m e a,
     (forall x, mMapsToUnique m x /\ (mMapsTo m x -> (~ In x (FV' e) /\ ~ In x (FVA_s a)))) ->
      sfrmphi' (A_sSubsts m a) (phi'Substs m e)
      ->
      sfrmphi' a e.
Proof.
  intros.
  destruct e0; constructor;
  inversionx H1;
  apply (sfrmeSubst m0); intuition;
  try apply H0;
  apply H0 in H1;
  inversionx H1;
  intuition;
  contradict H3;
  simpl;
  intuition.
Qed.

(* counter-examples:
sfrmphi [] (phiSubsts (a => c, b => c) (acc(b.f) * a.f = 3)) ->
sfrmphi [] (acc(b.f) * a.f = 3)

sfrmphi [] (phiSubsts (a => b) (acc(b.f) * a.f = 3)) ->
sfrmphi [] (acc(b.f) * a.f = 3)

sfrmphi [] (phiSubsts (b => a) (acc(b.f) * a.f = 3)) ->
sfrmphi [] (acc(b.f) * a.f = 3)
*)

Lemma sfrmphiSubst : forall e m a,
     (forall x, mMapsToUnique m x /\ (mMapsTo m x -> (~ In x (FV e) /\ ~ In x (FVA_s a)))) ->
      sfrmphi (A_sSubsts m a) (phiSubsts m e)
      ->
      sfrmphi a e.
Proof.
  induction e0; intros; constructor.
  - inversionx H1.
    eapply sfrmphi'Subst; eauto.
    intros.
    split; try apply H0.
    intros.
    apply H0 in H1.
    inversionx H1.
    intuition.
    contradict H4.
    simpl.
    intuition.
  - destruct a; simpl in *; intuition;
    try (apply IHp0 in H2); try assumption.
    * destruct (find (λ r : x * e, x_decb x0 (fst r)) m0) eqn: ff.
      + destruct p1.
        destruct e0; simpl in *;
        try (apply IHp0 in H2; eapply sfrmIncl; eauto; apply inclEmpty).
        assert (fff := ff).
        apply find_some in ff.
        inversionx ff.
        simpl in H3.
        unfold x_decb, dec2decb in *.
        des (x_dec x0 x1); try inversion H3.
        clear H3 H1.
        admit.
      + simpl in *.

      admit.
  ++  unfold x_decb, dec2decb in *.
      des (x_dec x1 x0).
        destruct e0; simpl in *. 
          apply IHpost in H1. eapply sfrmIncl; eauto; apply inclEmpty.
          admit.
          apply IHpost in H1. eapply sfrmIncl; eauto; apply inclEmpty.
        simpl in *. admit.
  ++  unfold x_decb, dec2decb in *.
      des (x_dec x1 x0).
        destruct e0; simpl in *; apply IHpost in H1; assumption.
        simpl in *. apply IHpost in H1; assumption.

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

  inversion INV as [INVphi INVtypes]; clear INV;
  inversion INVphi as [INVphi1 INVphi2]; clear INVphi.
  - assert (HH9 := H9).
    assert (HH7 := H7).
    assert (HH3 := H3).
    applyINVtypes INVtypes H9.
    applyINVtypes INVtypes H7.
    applyINVphi2 INVphi2 H3.
    
    inversionx evp.
    inversionx H16.
    simpl in *.
    clear H11.
    inversionx H18.
    common.
    rewrite H8 in *.
    inversionx H2.
    inversionx H14.
    inversionx H15.
    rewrite H8 in *.
    inversionx H13.
    clear H14 H16.
    inversionx xd0.

    unfold incl in H9.
    specialize (H9 (o0,f0)). assert (In (o0, f0) [(o0, f0)]). constructor. tauto. intuition.

    do 4 eexists; try emagicProgress. (*progress*)
    repeat split; repeat constructor.
    * eapply sfrmIncl; eauto. apply inclEmpty.
    * econstructor; eauto; simpl.
        apply inclEmpty.
        econstructor; eauto. econstructor.
          unfold HSubst.
          unfold o_decb, f_decb, string_decb, dec2decb.
          des (o_dec o0 o0).
          rewrite H11.
          eauto.
      common.
      econstructor; eauto; simpl; rewrite H8.
        unfold incl. intros. inversionx H6; try inversion H7. assumption.
        econstructor; eauto.
      econstructor; eauto; simpl.
        apply inclEmpty.
        econstructor; eauto. unfold evale. simpl. eauto. common. intuition. inversion H6.
      common.
      econstructor; eauto; simpl.
        apply inclEmpty.
        econstructor; eauto. unfold evale; simpl. rewrite H8.
          unfold HSubst.
          unfold o_decb, f_decb, string_decb, dec2decb.
          des (o_dec o0 o0).
          rewrite H11.
          simpl.
          des (string_dec f0 f0).
          tauto.
      common.
      admit.
    * intros.
      assert (hasStaticType pre e0 T1). admit.
      apply INVtypes in H7. admit.
  - assert (HH3 := H3).
    applyINVtypes INVtypes H3.
    do 4 eexists; try emagicProgress. (*progress*)
    repeat split; repeat constructor.
    * generalize post H6.
      clear.
      induction post; intros; constructor.
      + inversionx H6.
        destruct a; try constructor;
        inversionx H0;
        try apply sfrmeSubst in H5;
        try apply sfrmeSubst in H6;
        assumption.
      + destruct a; simpl in *; intuition.
      ++  unfold x_decb, dec2decb in *.
          des (x_dec x1 x0).
            destruct e0; simpl in *. 
              apply IHpost in H1. eapply sfrmIncl; eauto; apply inclEmpty.
              admit.
              apply IHpost in H1. eapply sfrmIncl; eauto; apply inclEmpty.
            simpl in *. admit.
      ++  unfold x_decb, dec2decb in *.
          des (x_dec x1 x0).
            destruct e0; simpl in *; apply IHpost in H1; assumption.
            simpl in *. apply IHpost in H1; assumption.
    * admit.
    * intros.
      eapply hasStaticTypePhiSubst in H0.
      + apply INVtypes in H0. apply INVtypes in HH3. apply INVtypes in H2. admit.
      + split; eauto.
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