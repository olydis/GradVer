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
Definition invNoAlias
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    sfrmphi [] phi /\ evalphi Heap rho A phi.

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
  - applyINVtypes INVtypes H7.
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
      apply evalphiPrefix in H19.
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
    apply evalphiPrefix in evp.
    emagicProgress.
  - emagicProgress.
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
    * eapply sfrmIncl; eauto. intuition.
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

(*
Lemma evalphi'HSubstAexcept : forall p H r A o f x,
  evalphi' H r (Aexcept A [(o, f)]) p ->
  evalphi' (HSubst o f x H) r (Aexcept A [(o, f)]) p.
Proof.
  intros.
  inversionx H1; try constructor; unfold evale in *.
  * destruct e_1; inversionx H3;
    destruct e_2; inversionx H4;
    econstructor; eauto;
    unfold evale; simpl; eauto.
    - destruct (evale' H0 r e_2) eqn: ee; inversionx H2.
      destruct v0; inversionx H3.
      destruct (H0 o1) eqn: ff; inversionx H2.
      destruct p0.
      simpl in *.
      destruct e_2; simpl in *; inversionx ee; simpl in *.
      + unfold HSubst.
        dec (o_dec o1 o0); rewrite ff; simpl; try tauto.
        dec (string_dec f1 f0); try tauto.

Lemma evalphiHSubstAexcept : forall p H r A o f x,
  evalphi H r (Aexcept A [(o, f)]) p ->
  evalphi (HSubst o f x H) r (Aexcept A [(o, f)]) p.
Proof.
  induction p0; intros; try constructor.
  inversionx H1.
  rewrite AexceptComm in H12.
  eapply IHp0 in H12.
  econstructor; eauto.
  - admit.
  - inversionx H11; simpl in *; try constructor.
    * 
*)

      admit.
    * intros.
      assert (hasStaticType pre e0 T1). admit.
      apply INVtypes in H7. admit.
  - assert (HH3 := H3).
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
  - assert (HnT := HnotTotal initialHeap). inversionE HnT.
    
    unfold fieldsNames in *.
    common.
    do 4 eexists; try emagicProgress. (*progress*)
    repeat split; repeat constructor.
    * admit.
    * admit.
    * admit.
  - admit.
  - applyINVtypes INVtypes H4.
    
    do 4 eexists; try emagicProgress. (*progress*)
    repeat split; repeat constructor.
    * simpl. assumption.
    * admit.
    * admit.
  - do 4 eexists; try emagicProgress. (*progress*)
    repeat split; repeat constructor.
    * assumption.
    * assumption.
    * assumption.
  - applyINVphi2 INVphi2 H1.
    do 4 eexists; try emagicProgress; 
    try (apply evalphiPrefix in evp; assumption). (*progress*)
    repeat split; repeat constructor.
    * assumption.
    * apply evalphiApp in evp. intuition.
    * intros.
      apply phiImpliesSuffix in H1.
      eapply phiImpliesStaticType in H1; eauto.
  - do 4 eexists; try emagicProgress. (*progress*)
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
      unfold ehasDynamicType, evale.
      inversionx H0; simpl in *.
      + eexists.
        split; eca.
      + eexists.
        split; eca.
      + unfold rhoSubst.
        dec (x_dec x1 x0).
      ++  rewrite cons2app2 in H1.

          apply phiImpliesAppCommA in H1.
          apply phiImpliesNarrowing in H1.
      ++  rewrite cons2app2 in H1.
          apply phiImpliesNarrowing in H1.
      +++ assert (hasStaticType pre (ex x1) T0).
            eapply phiImpliesStaticType; eauto.
            constructor.
            assumption.
          apply INVtypes in H0.
          auto.
      +++ unfold phiOrthogonal, disjoint.
          simpl.
          intros.
          destruct (x_dec x0 x2);
          subst;
          intuition.
      +++ apply phiSatisfiableApp.
            unfold phiOrthogonal, disjoint.
            simpl.
            intros.
            destruct (x_dec x0 x2);
            subst;
            intuition.
            
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
            
            apply H2 in INVphi2.
            unfold phiSatisfiable.
            repeat eexists. eauto.
      + 
            
      
      cons2app2
      
          eexists.
          split; try eca.
          apply H2 in INVphi2.
          unfold phiImplies in H1.
          assert (t = T0). admit.
          subst.
          apply hasDynamicTypeDefault.
        eexists.
        split; eca.
      try (eca; split; try eca; fail).
    
      unfold hasStaticType in *.

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
