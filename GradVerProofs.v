Load GradVer20Hook.
Import Semantics.

(* PROOF SECTION *)
Notation "'φ'" := phi.
Notation "'ρ'" := rho.

(* determinism? *)

Definition invPhiHolds
  (G : Gamma) (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    sfrmphi [] phi /\ evalphi Heap rho A phi.
Definition invTypesHold
  (G : Gamma) (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    forall e T,
         match e with
         | edot e _ => phiImplies phi [phiNeq e (ev vnull)]
         | _ => True
         end
      -> hasStaticType G e T
      -> ehasDynamicType Heap rho e T.
Definition invHeapConsistent
  (G : Gamma) (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    forall o C m f T,
      Heap o = Some (C, m) ->
      fieldType C f = Some T ->
      exists v, m f = Some v /\ hasDynamicType Heap v T.
Definition invHeapNotTotal
  (G : Gamma) (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    ∃ omin : o,
    forall o' : o,
      (omin <= o') -> Heap o' = None /\ (forall f, ~ In (o', f) A).
Definition invAevals
  (G : Gamma) (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    forall A', In A' A -> exists v, Heap (fst A') = Some v.

Definition invAll
  (G : Gamma) (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    invPhiHolds
      G Heap rho A phi /\
    invTypesHold
      G Heap rho A phi /\
    invHeapConsistent
      G Heap rho A phi /\
    invHeapNotTotal
      G Heap rho A phi /\
    invAevals
      G Heap rho A phi.

Ltac emagicProgress :=
  repeat eexists;
  econstructor; econstructor;
  unfold evale; simpl; eauto.

Definition soundness G pre s post initialHeap initialRho initialAccess S : Prop :=
  hoare G pre s post ->
  invAll G initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s) :: S) (finalHeap, (finalRho, finalAccess, []) :: S) /\
    invAll G finalHeap finalRho finalAccess post.

Ltac uninv :=
  unfold invAll in *;
  unfold invPhiHolds in *;
  unfold invTypesHold in *;
  unfold invHeapConsistent in *;
  unfold invHeapNotTotal in *;
  unfold invAevals in *.

Ltac applyINVtypes INVtypes H :=
  apply INVtypes in H; auto;
  unfold ehasDynamicType in H;
  inversion H as [? xt]; clear H;
  inversion xt as [xt1 ?xd]; clear xt;
  inversionx xt1.

Ltac applyINVphi2 INVphi2 H :=
  assert (evp := INVphi2);
  apply H in evp.

(*    x : T * y : T   =>  x : T                *)
(*    x : T * y = 3   =>  x : T * y : T        *)
(*    3 = 4           =>  x : T                *)
(*    3 = x           =>  x : T                *)

Ltac unfoldINV INV :=
  uninv;
  inversion INV as [INVphi INVcarry1]; clear INV;
  inversion INVphi as [INVphi1 INVphi2]; clear INVphi;
  inversion INVcarry1 as [INVtypes INVcarry2]; clear INVcarry1;
  inversion INVcarry2 as [INVHELPER INVcarry3]; clear INVcarry2;
  inversion INVcarry3 as [INVheapNT' INVAevals]; clear INVcarry3;
  inversion INVheapNT' as [omin INVheapNT]; clear INVheapNT'.

Lemma phiImpliesEdotNeq : forall e f,
  phiImplies [phiNeq (edot e f) (ev vnull)] [phiNeq e (ev vnull)].
Proof.
  repeat intro.
  inversionx H0. inversionx H10. common.
  destruct (evale' h r e0) eqn: ee; try discriminate.
  destruct v0; try discriminate.
  inversionx H8.
  eca; econstructor;
  unfold evale.
    eauto.
    simpl. eauto.
  discriminate.
Qed.

Theorem staSemSoundness : forall G (s' s'' : list s) (pre post : phi) initialHeap initialRho initialAccess,
  hoare G pre s'' post ->
  invAll G initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, [(initialRho, initialAccess, s'' ++ s')]) (finalHeap, [(finalRho, finalAccess, s')]) /\
    invAll G finalHeap finalRho finalAccess post
.
Proof.
  do 8 intro.
  intro HO.
  generalize s' initialHeap initialRho initialAccess.
  clear s' initialHeap initialRho initialAccess.
  induction HO;
  do 4 intro;
  intro INV.
  - unfoldINV INV.
    (*sAlloc*)
    pose proof (INVheapNT omin) as newHeap.
    assert (omin ≤ omin). auto.
    apply newHeap in H5. unf.
    set (x1 := omin) in *.
    
    unfold fieldsNames in *.
    common.
    
    do 4 eexists; try emagicProgress. (*progress*)
    assert (evalphi (Halloc x1 C0 initialHeap) (rhoSubst x0 (vo x1) initialRho)
      (initialAccess ++ map (λ cf' : T * f, (x1, snd cf')) l)
      (accListApp x0 (map snd l)
         (phiNeq (ex x0) (ev vnull) :: phi'0)))
          as eph.
      assert (listDistinct (map snd l)) as fd.
        eapp fieldsDistinct.
      assert (forall l,
          listDistinct (map snd l) ->
          (evalphi
            (Halloc x1 C0 initialHeap)
            (rhoSubst x0 (vo x1) initialRho)
            (initialAccess)
            (phiNeq (ex x0) (ev vnull) :: phi'0))
          ->
          (evalphi
            (Halloc x1 C0 initialHeap)
            (rhoSubst x0 (vo x1) initialRho)
            (initialAccess ++ map (λ cf' : T * f, (x1, snd cf')) l)
            (accListApp x0 (map snd l)
               (phiNeq (ex x0) (ev vnull) :: phi'0)))
         ) as remAccList.
        induction l0; intros; simpl in *.
          rewrite app_nil_r. assumption.
        unf.
        apply IHl0 in H9; auto.
        eca; simpl; rewrite rhoSubstId.
          apply inclSingle. intuition.
          eca; unfold evale; simpl; try rewrite rhoSubstId; eauto.
        rewrite AexceptAppFirst.
        rewrite AexceptReduceSecond; auto.
        common.
        remember (Aexcept
              ((x1, snd a) :: map (fun cf' => (x1, snd cf')) l0)
              ([@pair o f x1 (snd a)]))
               as AE.
        assert (AE = map (λ cf' : T * f, (x1, snd cf')) l0).
          subst. simpl.
          undecb.
          simpl.
          dec (o_dec x1 x1). simpl.
          dec (string_dec (snd a) (snd a)). simpl.
          rewrite AexceptReduceSecond. apply AexceptEmpty.
          intuition.
          contradict H8.
          apply in_map_iff.
          apply in_map_iff in H4.
          unf.
          inversionx H4.
          eex.
        rewrite H4.
        assumption.
      apply remAccList; auto.
      eca; simpl; try apply inclEmpty.
        eca; unfold evale; simpl; try rewrite rhoSubstId; eauto. 
        discriminate.
      common.
      eapp evalphiRemoveHalloc.
      eapp evalphiRemoveRhoSubst.
    assert (∀ (o0 : o) (C1 : C) (m0 : f → option v) (f0 : f) 
      (T0 : T),
      Halloc x1 C0 initialHeap o0 = Some (C1, m0)
      → fieldType C1 f0 = Some T0
        → ∃ v0 : v,
          m0 f0 = Some v0 ∧ hasDynamicType (Halloc x1 C0 initialHeap) v0 T0) as hlp.
      intros.
      unfold Halloc in H4.
      rewrite Heqo0 in *.
      dec (o_dec x1 o0).
        inversionx H4.
        assert ((find
           (λ fs' : T * string, if string_dec f0 (snd fs') then true else false)
           l) = Some (T0, f0)) as fi.
          unfold fieldType, fields in *.
          destruct (class C1); try discriminate.
          destruct c.
          common.
          inversionx Heqo0.
          generalize l0 Heqo1.
            induction l2; intros; simpl in *; try discriminate.
            destruct a. simpl in *.
            dec (string_dec f2 f0); simpl in *.
              inversionx Heqo0. dec (string_dec f0 f0). tauto.
              apply IHl2 in Heqo0. rewrite Heqo0. destruct (string_dec f0 f2); subst; tauto.
        rewrite fi.
        simpl.
        eex.
        apply hasDynamicTypeDefault.
        
        eapply INVHELPER in H4; eauto. unf.
        eex.
        unfold Halloc. rewrite Heqo0.
        inversionx H9; try constructor.
        rename de2 into ung.
        eca.
        dec (o_dec x1 o1); eauto.
        rewrite H6 in *.
        discriminate.
    repeat split; repeat constructor.
    * generalize l H1. clear.
      induction l; intros; simpl in *.
      + repeat constructor.
        assumption.
      + repeat constructor.
        eapply sfrmIncl; eauto.
        apply inclEmpty.
    * apply eph.
    * induction e0; intros.
      + apply INVtypes in H5; auto; inversionx H5; unf; common.
        inversionx H5. eex. inversionx H9; eca.
      + unfold ehasDynamicType, evale, rhoSubst. simpl.
        dec (x_dec x2 x0).
          assert (T0 = TClass C0) as TT. inversionx H5. inversionx H3. rewrite H9 in *. inversionx H10. tauto.
          subst.
          apply INVtypes in H5; auto. inversionx H5. unf. common.
          eex.
          eca. unfold Halloc. rewrite Heqo0. dec (o_dec x1 x1). eauto.
        
        apply INVtypes in H5; auto.
        inversionx H5. unf. common.
        eex.
        
        inversionx H9; eca.
        unfold Halloc. rewrite Heqo0.
        rename de2 into de.
        dec (o_dec x1 o0). rewrite H6 in H10. discriminate.
        eauto.
      + apply H4 in eph. rename H4 into tra.
        inversionx eph. inversionx H17. common. inversionx H16.
        inversionx H5.
        apply IHe0 in H12. clear IHe0.
          inversionx H12. unf. common. rewrite H10 in *. inversionx H5. inversionx H15.
          unfold ehasDynamicType, evale. simpl.
          rewrite H10.
          inversionx H8; try tauto.
          rewrite H13. simpl.
          eapp hlp.
        
        destruct e0; auto.
        eapp phiImpliesTrans.
        apply phiImpliesEdotNeq.
    * apply hlp.
    * exists (Datatypes.S x1).
      intros.
      assert (omin <= o').
        apply le_S_n.
        eapp le_trans.
      apply INVheapNT in H5. unf.
      split.
      + unfold Halloc.
        rewrite Heqo0.
        dec (o_dec x1 o'). contradict H4. auto with arith.
        assumption.
      + intros.
        specialize (H9 f0).
        intuition.
        apply in_app_iff in H5.
        inversionx H5; try tauto.
        apply in_map_iff in H10.
        unf.
        inversionx H10.
        subst.
        contradict H4. auto with arith.
    * intros. destruct A'.
      apply in_app_iff in H4. inversionx H4.
      + apply INVAevals in H5.
        unf.
        eex.
        simpl in *.
        unfold Halloc.
        rewrite Heqo0.
        dec (o_dec x1 o0). rewrite H6 in H4. discriminate.
        eauto.
      + apply in_map_iff in H5.
        unf.
        inversionx H5. subst.
        unfold Halloc.
        rewrite Heqo0. simpl.
        dec (o_dec o0 o0). eex.
  - unfoldINV INV.
    (*sMemberSet*)
    rename H2 into hstX0.
    rename H3 into hstX1.
    rename H0 into im.
    rename H4 into fht.
    rename H1 into sf.
    assert (temp := hstX0).
      applyINVtypes INVtypes temp.
      rename x1 into v0.
      rename xd into hdtV0.
      rename H1 into irX0.
    assert (temp := hstX1).
      applyINVtypes INVtypes temp.
      rename x1 into v1.
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
              (phiAcc (ex x0) f0 :: 
                phiNeq (ex x0) (ev vnull) :: phiEq (edot (ex x0) f0) (ex y) :: 
                phi'0)) as eph.
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
    * induction e0; intros; inversionx H1; simpl in *.
      + eex. eca.
      + eex. eca.
      + specialize (INVtypes (ex x1) T1). simpl in *.
        apply INVtypes in H0.
          inversionx H0. unf.
          eca. eca. inversionx H2; try (eca; fail).
          unfold HSubst.
          dec (o_dec o1 o0); eca; rewrite H3.
            dec (o_dec o0 o0). eauto.
            rename de2 into de. dec (o_dec o1 o0).
              contradict de. eauto.
              eauto.
        eca.
      + apply H0 in eph.
        inversionx eph. inversionx H16. common. inversionx H15.
        unfold ehasDynamicType, evale. simpl.
        apply IHe0 in H7.
          inversionx H7. unf. common.
          rewrite H2 in *. inversionx H6.
          inversionx H3; try tauto.
          rewrite H12.
          simpl.
          eapp hlp.
        destruct e0; auto.
        eapp phiImpliesTrans.
        apply phiImpliesEdotNeq.
    * apply hlp.
    * eexists. intros. apply INVheapNT in H0. unf.
      unfold HSubst.
      rewrite H1.
      dec (o_dec o' o0); tauto.
    * intros. apply INVAevals in H0. unf. destruct A'.
      unfold evalA'_d, HSubst in *. simpl in *.
      dec (o_dec o1 o0); try (eex; fail).
      rewrite H1. destruct x1. eex.
  - unfoldINV INV.
    (*sAssign*)
    rename H4 into hstX0.
    rename H5 into hstE0.
    rename H6 into sfe.
    rename H2 into niFVphi.
    rename H3 into niFVe0.
    
    applyINVphi2 INVphi2 H0.
    apply INVtypes in hstE0.
    Focus 2.
      destruct e0; auto.
      simpl in *.
      apply inclSingle in sfe.
      eapp phiImpliesTrans.
      unfold phiImplies. intros.
      eappIn evalphiIn H2.
      inversionx H2. common.
      eca.
        apply inclEmpty.
        eca; unfold evale; simpl.
          eauto.
          discriminate.
      eca.
    inversionx hstE0. unf.
    
    do 4 eexists; try emagicProgress. (*progress*)
    assert (evalphi
              initialHeap 
              (rhoSubst x0 x1 initialRho) 
              initialAccess
              (phi'0 ++ [phiEq (ex x0) e0])) as eph.
      apply evalphiSymm. simpl.
      eca; simpl.
        apply inclEmpty.
        eca; unfold evale; simpl.
          apply rhoSubstId.
          rewrite evale'RemoveRhoSubst; auto.
      common.
      apply evalphiRemoveRhoSubst; auto.
    repeat split; repeat constructor.
    * apply sfrmphiApp. split; try assumption.
      repeat constructor.
      generalize e0 H1 sfe. clear.
      induction e0; intros; try eca; 
      simpl in *;
      apply inclSingle in sfe.
      + apply in_flat_map.
        eex. apply in_eq.
      + apply IHe0; auto.
        destruct e0; try apply inclEmpty.
        simpl.
        apply inclSingle.
        eapply sfrmphiChain in H1.
          simpl in *.
          unfold staticFootprint in *.
          apply in_flat_map in H1. unf.
          destruct x0; try tauto.
          inversionx H2; try tauto.
          inversionx H0.
          eauto.
        apply in_flat_map.
        eex.
        apply in_eq.
    * apply eph.
    * induction e1; intros; unfold ehasDynamicType, evale; 
      inversionx H5; simpl in *.
      + eex. eca.
      + eex. eca.
      + unfold rhoSubst.
        dec (x_dec x2 x0).
          eex. inversionx hstX0. rewrite H7 in *. inversionx H8. assumption.
        assert (ehasDynamicType initialHeap initialRho (ex x2) T1) as hdt.
          apply INVtypes; auto.
          eca.
        inversionx hdt. unf. common.
        eex.
      + apply H2 in eph.
        inversionx eph. inversionx H16. common. inversionx H15.
        unfold ehasDynamicType, evale. simpl.
        apply IHe1 in H9.
          inversionx H9. unf. common.
          rewrite H8 in *. inversionx H6.
          inversionx H7; try tauto.
          rewrite H13.
          simpl.
          eapp INVHELPER.
        destruct e1; auto.
        eapp phiImpliesTrans.
        apply phiImpliesEdotNeq.
    * apply INVHELPER.
    * eax.
    * apply INVAevals.
  - unfoldINV INV.
    (*sReturn*)
    applyINVtypes INVtypes H3.
    
    do 4 eexists; try emagicProgress. (*progress*)
    assert (evalphi 
        initialHeap 
        (rhoSubst xresult x1 initialRho) 
        initialAccess
        (phiEq (ex xresult) (ex x0) :: phi'0))
          as eph.
      eca; simpl.
        apply inclEmpty.
        eca; unfold evale; simpl.
          rewrite rhoSubstId. eauto.
          unfold rhoSubst. dec (x_dec x0 xresult); tauto.
      common.
      apply H0 in INVphi2.
      eapp evalphiRemoveRhoSubst.
    repeat split; repeat constructor.
    * simpl. assumption.
    * apply eph.
    * induction e0; intros.
      + inversionx H6; eex; eca.
      + unfold ehasDynamicType, evale, rhoSubst.
        simpl.
        dec (x_dec x2 xresult).
          eex.
          inversionx H6. inversionx H4.
          rewrite H8 in H9. inversionx H9.
          assumption.
        apply INVtypes in H6; auto.
      + inversionx H6.
        apply H3 in eph. rename H3 into pi.
        apply IHe0 in H10. clear IHe0.
          inversionx H10.
          unf.
          inversionx eph. simpl in *. clear H11 H18.
          inversionx H17.
          common.
          inversionx H15.
          rewrite H10 in H6. inversionx H6.
          inversionx H7; try tauto. clear H16.
          eapply INVHELPER in H12; eauto. unf.
          eex.
          unfold evale.
          simpl.
          rewrite H10.
          rewrite H11.
          simpl.
          assumption.
        destruct e0; auto.
        eapp phiImpliesTrans.
        apply phiImpliesEdotNeq.
    * apply INVHELPER.
    * eax.
    * apply INVAevals.
  - (*sCall*)
    rename y into x1.
    rename z' into x2.
    rename INV into INV0.
    rename H2 into hstX0.
    rename H0 into hstX1.
    rename H3 into hstX2.
    rename H7 into xDist.
    rename H5 into phi_r_sf.
    rename H6 into phi_r_x0.
    rename H4 into impl.
    rename H1 into mme.
    set (mm := Method T_r m0 T_p z (Contract phi_pre phi_post) underscore) in *.
    set (preI := (phiNeq (ex x1) (ev vnull) :: phiSubsts2 xthis x1 (xUserDef z) x2 phi_pre ++ phi_r)) in *.
    
    assert (evalphi initialHeap initialRho initialAccess preI)
    as ep_preI.
      unfoldINV INV0. subst. eapp impl.
    
    assert (evalphi initialHeap initialRho 
      (Aexcept initialAccess
                 (footprint initialHeap initialRho (phiSubsts2 xthis x1 (xUserDef z) x2 phi_pre))) phi_r)
    as ep_phi_r.
      subst preI.
      rewrite app_comm_cons in ep_preI.
      apply evalphiApp in ep_preI.
      simpl in ep_preI.
      apply ep_preI.
    
    assert (evalphi initialHeap initialRho initialAccess (phiSubsts2 xthis x1 (xUserDef z) x2 phi_pre))
    as ep_phi_pre.
      subst preI.
      rewrite cons2app in ep_preI.
      apply evalphiSuffix in ep_preI.
      apply evalphiPrefix in ep_preI.
      assumption.
    
    assert (mWellDefined C0 mm)
    as mmwd.
      eapp IsMethodWellDef.
    
    (*dyn. behavior of involved vars*)
    assert (ehasDynamicType initialHeap initialRho (ex x0) T_r)
    as hdtX0.
      unfoldINV INV0. eapp INVtypes.
    invE hdtX0 v0.
    
    assert (ehasDynamicType initialHeap initialRho (ex x1) (TClass C0))
    as hdtX1.
      unfoldINV INV0. eapp INVtypes.
    invE hdtX1 v1.
    
    assert (ehasDynamicType initialHeap initialRho (ex x2) T_p)
    as hdtX2.
      unfoldINV INV0. eapp INVtypes.
    invE hdtX2 v2.
    
    assert (exists vo1, v1 = vo vo1) as tmp.
      inversionx ep_preI.
      inversionx H11.
      inversionx hdtX1.
      common.
      rewrite H0 in *. inversionx H3. inversionx H8.
      inversionx H1; try tauto.
      eex.
    invE tmp vo1. subst.
    
    assert (exists m1, initialHeap vo1 = Some (C0, m1))
    as Hvo1.
      inversionx hdtX1.
      inversionx H1.
      eex.
    invE Hvo1 m1.
    
    unfold evale in *. simpl in *.
    
    (*aliases*)
    set (r' := rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) (xUserDef z) v2).
    set (fp := footprint initialHeap r' phi_pre).
    set (S'' := [(initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s')]).
    set (phi_end := phiSubsts3 xthis x1 (xUserDef z) x2 xresult x0 phi_post ++ phi_r).
    set (GG := (GammaSet (xUserDef z) T_p
                (GammaSet xthis (TClass C0)
                   (GammaSet xresult T_r GammaEmpty)))) in *.
    
    assert (r' xresult = Some (defaultValue T_r))
    as r'xresult.
      subst r'. unfold rhoFrom3. tauto.
    
    assert (r' xthis = Some (vo vo1))
    as r'xthis.
      subst r'. unfold rhoFrom3. tauto.
    
    assert (r' (xUserDef z) = Some v2)
    as r'xUDz.
      subst r'. unfold rhoFrom3.
      dec (x_dec (xUserDef z) xresult). clear de2.
      dec (x_dec (xUserDef z) xthis). clear de2.
      dec (x_dec (xUserDef z) (xUserDef z)).
      tauto.
    
    (*Part 1: make the call*)
    assert (evalphi initialHeap r' initialAccess phi_pre)
    as ep_phi_pre_rho.
      unf. eapp evalphiPhiSubsts2RhoFrom3.
    
    assert (evalphi initialHeap r' fp phi_pre)
    as ep_phi_pre'.
      eapp evalphiFootprintAccess.
    
    assert (incl fp initialAccess)
    as fp_incl_ia.
      eapp evalphiImpliesAccess.
    
    assert (dynSem 
              (initialHeap, [(initialRho, initialAccess, sCall x0 x1 m0 x2 :: s')])
              (initialHeap, (r', fp, underscore) :: S'')
           )
    as part1.
      eca; unfold evale; simpl. (*3*)
        inversionx hdtX1. eauto.
        inversionx hdtX2. eauto.
        tauto.
    
    assert (invAll GG initialHeap r' fp phi_pre)
    as INV1.
      uninv. repeat split; simpl; try constructor. (*6*)
        unf. assumption.
        apply ep_phi_pre'.
        induction e0; intros; inversionx H1; simpl in *. (*4*)
          eex. eca.
          eex. eca.
          subst GG.
            unfold GammaSet, GammaEmpty in *.
            unfold equiv_decb in *.
            unfold equiv_dec in *.
            unfold x_EqDec in *.
            dec (x_dec (xUserDef z) x3).
              inversionx H4. inversionx hdtX2.
              eex.
            clear de2.
            dec (x_dec xthis x3).
              inversionx H4. inversionx hdtX1.
              eex.
            clear de2.
            dec (x_dec xresult x3).
              inversionx H4. inversionx hdtX0.
              eex.
              apply hasDynamicTypeDefault.
            discriminate.
          apply IHe0 in H5.
            inversionE H5. inversionx H1.
            apply H0 in ep_phi_pre'. inversionx ep_phi_pre'. inversionx H13.
            common. inversionx H12. rewrite H2 in *. inversionx H6. inversionx H3; try tauto.
            eapply INV0 in H7; eauto. inversionE H7. inversionx H1.
            eex. unfold evale. simpl. rewrite H2. rewrite H9. simpl. assumption.
          destruct e0; auto.
          eapp phiImpliesTrans.
          apply phiImpliesEdotNeq.
        unf. assumption.
        unf. exists x3. intros. apply H17 in H22. split; try apply H22. unfold not. intro f0. intro ifp. apply fp_incl_ia in ifp. apply H22 in ifp. tauto.
        intros. eapp INV0.
    
    (*Part 2: method body*)
    assert (∃ finalHeap finalRho finalAccess,
          dynSemStar 
            (initialHeap, [(r', fp, underscore)])
            (finalHeap, [(finalRho, finalAccess, [])]) ∧
          invAll GG finalHeap finalRho finalAccess phi_post)
    as call_finished.
      assert (soundness GG phi_pre underscore phi_post initialHeap r' fp []) as sdn.
        admit. (*assume that for method body*)
      intuition.
    
    invE call_finished finalHeap'.
    invE call_finished finalRho'.
    invE call_finished finalAccess'.
    inversion call_finished as [part2' INV2]. clear call_finished.
    assert (dynSemStar 
      (initialHeap, (r', fp, underscore) :: S'')
      (finalHeap', (finalRho', finalAccess', []) :: S''))
    as part2.
      eapp (dynSemStarLift 
             (initialHeap, [(r', fp, underscore)])
             (finalHeap', [(finalRho', finalAccess', [])])).
    
    assert (finalRho' xthis = Some (vo vo1))
    as fr'xthis.
      eappIn dynSemStarNotModifies part2'. rewrite part2' in r'xthis. auto. apply mmwd.
      
    assert (finalRho' (xUserDef z) = Some v2)
    as fr'xUDz.
      eappIn dynSemStarNotModifies part2'. rewrite part2' in r'xUDz. auto. apply mmwd.

    assert (∀ (A : A'_d) (v0 : v),
      ¬ In A fp -> evalA'_d initialHeap A = Some v0 → 
                   evalA'_d finalHeap'  A = Some v0)
    as Hinv.
      intros.
      eapp dynSemStarNotModifiesH.
   
    assert (∀ (e : e) (v0 : v),
      disjoint (footprintXe initialHeap initialRho e) fp 
                -> evale' initialHeap initialRho e = Some v0 → 
                   evale' finalHeap'  initialRho e = Some v0)
    as Hinve.
      unfold footprintXe, A'_s2A'_d.
      induction e0; intros; simpl in *; try tauto.
      apply disjointSplitA in H0. inversionx H0.
      destruct (evale' initialHeap initialRho e0); try discriminate.
      destruct v3; try discriminate.
      simpl in *.
      unfold disjoint in H2. specialize (H2 (o0, f0)). inversionx H2. contradict H0. intuition.
      eappIn IHe0 H3. rewrite H3.
      apply (Hinv _ v1) in H0.
        unfold evalA'_d in H0.
        simpl in H0.
        assumption.
      unfold evalA'_d. simpl.
      assumption.
    
    assert (disjoint (footprint initialHeap initialRho phi_r) fp)
    as disj_fp.
      eappIn evalphiImpliesAccess ep_phi_r.
      eappIn inclAexceptDisjoint ep_phi_r.
      unfold phiSubsts2 in ep_phi_r.
      erewrite footprintPhiSubsts2RhoFrom3 in ep_phi_r; eauto.
        apply mmwd.
        apply hdtX2.
        apply hdtX1.

    assert (∀ (A : A'_s),
      In A (staticFootprintX phi_r) 
                  -> evalA'_s initialHeap initialRho A =
                     evalA'_s finalHeap' initialRho A)
    as phi_r_inv.
      intros.
      assert (incl (footprint initialHeap initialRho phi_r) initialAccess)
      as fp_incl_iA.
        eappIn evalphiImpliesAccess ep_phi_r.
        eappIn inclAexcept ep_phi_r.
      eappIn evalphiVSfpX ep_phi_r.
      eappIn evalsInIn ep_phi_r. inversionE ep_phi_r. inversionx H1.
      assert (evalA'_d initialHeap x3 = evalA'_d finalHeap' x3).
        eappIn sfrmphiVSdfpX phi_r_sf.
        apply phi_r_sf in H3. clear phi_r_sf.
        eapp dynSemStarNotModifiesHx.
          unfold not. intro.
          specialize (disj_fp x3). tauto.
        apply fp_incl_iA in H3.
        apply INV0 in H3.
        inversionE H3. rewrite H1. discriminate.
      unfold evalA'_s.
      assert (A'_s2A'_d finalHeap' initialRho A = Some x3).
        unfold A'_s2A'_d in *. destruct A. simpl in *.
        destruct (evale' initialHeap initialRho e0) eqn: ee; try discriminate.
        apply Hinve in ee.
          rewrite ee. assumption.
        simpl in *.
        destruct v1; try discriminate.
        inversionx H2.
        assert (incl (footprintXe initialHeap initialRho e0) (footprint initialHeap initialRho phi_r)).
          eappIn sfrmphiVSdfpX phi_r_sf.
          eapp incl_tran.
          eapp inclFPX.
        unfold disjoint. intro AA.
        specialize (H2 AA).
        specialize (disj_fp AA).
        inversionx disj_fp; try auto.
      rewrite H2, H4.
      assumption.
    
    (* 
    assert (∀
      footprint initialHeap r p = footprint finalHeap' r p)
    as Hfp. *)
    (* 
    assert (forall A,
      disjoint A fp ->
      forall r p,
      evalphi initialHeap r A p ->
      evalphi finalHeap' r A p)
    as warpH.
      do 2 intro. induction p0; intros; simpl in *; try constructor.
      inversionx H1. *)
    
    (*Part 3: call finished*)
    assert (exists vresult, finalRho' xresult = Some vresult)
    as vres.
      eapp RhoGetsMoreSpecific.
    invE vres vresult.
    
    set (finalRho := rhoSubst x0 vresult initialRho).
    
    assert (finalRho x0 = Some vresult)
    as frx0.
      subst finalRho. rewrite rhoSubstId. tauto.
    
    assert (finalRho x1 = Some (vo vo1))
    as frx1.
      subst finalRho. unfold rhoSubst. dec (x_dec x1 x0); try tauto.
     
    assert (finalRho x2 = Some v2)
    as frx2.
      subst finalRho. unfold rhoSubst. dec (x_dec x2 x0); try tauto.

    assert (evalphi finalHeap' finalRho' finalAccess' phi_post)
    as eph_phi_post'.
      apply INV2.
    
    assert (eph_phi_post := eph_phi_post').
    
    assert (dynSem
              (finalHeap', (finalRho', finalAccess', []) 
                          :: [(initialRho, Aexcept initialAccess fp , sCall x0 x1 m0 x2 :: s')])
              (finalHeap',   [(finalRho  , Aexcept initialAccess fp ++ footprint finalHeap' finalRho' phi_post, s')])
           )
    as part3.
      eapply HeapGetsMoreSpecific in part2; eauto. inversionE part2.
      eca; unfold evale; simpl. (*2*)
        apply hdtX1.
        unfold mpost, mcontract. rewrite mme. tauto.

(*
    assert (incl
      (footprint finalHeap' finalRho (phiSubsts3 xthis x1 (xUserDef z) x2 xresult x0 phi_post))
      (Aexcept initialAccess fp ++ footprint finalHeap' finalRho' phi_post))
    as incl_FP_phi_post.
      unfold incl. intros.
      subst finalRho.
      admit.
    
    assert (incl
      (footprint finalHeap' finalRho (phiSubsts3 xthis x1 (xUserDef z) x2 xresult x0 phi_r))
      (Aexcept
        (Aexcept initialAccess fp ++ footprint finalHeap' finalRho' phi_post)
        (footprint finalHeap' finalRho (phiSubsts3 xthis x1 (xUserDef z) x2 xresult x0 phi_post))))
    as incl_FP_phi_r.
      subst preI.
      rewrite app_comm_cons in ep_preI.
      apply evalphiApp in ep_preI.
      inversionx ep_preI.
      apply evalphiImpliesAccess in H1.
      apply inclAexceptDisjoint in H1.
      admit.
*)
    assert (incl
      (footprint finalHeap' (rhoSubst x0 vresult initialRho) (phiSubsts3 xthis x1 (xUserDef z) x2 xresult x0 phi_post))
      (footprint finalHeap' finalRho' phi_post))
    as incl_phi_post_fp.
      assert (incl (FV phi_post) [xUserDef z; xthis; xresult]). apply mmwd.
      generalize phi_post H0.
      induction phi_post0; intros; simpl in *; try apply inclEmpty.
      apply inclApp in H1. inversionx H1.
      apply incl_app; try (intuition; fail).
      apply incl_appl.
      destruct a; simpl; try apply inclEmpty.
      unfold incl. generalize e0 H2. induction e1; intros; simpl in *;
      try tauto.
        unfold xSubsts in H4. simpl in H4.
        apply inclSingle in H1.
        inversionx H1. simpl in H4.
          dec (x_dec (xUserDef z) (xUserDef z)).
          unfold rhoSubst in H4.
          dec (x_dec x2 x0). tauto.
          rewrite fr'xUDz.
          assert (initialRho x2 = Some v2). apply hdtX2.
          rewrite H1 in H4.
          assumption.
        inversionx H5. simpl in H4.
          unfold rhoSubst in H4.
          dec (x_dec x1 x0). tauto.
          rewrite fr'xthis.
          assert (initialRho x1 = Some (vo vo1)). apply hdtX1.
          rewrite H1 in H4.
          assumption.
        inversionx H1. simpl in H4.
          unfold rhoSubst in H4.
          dec (x_dec x0 x0).
          rewrite vres.
          assumption.
        tauto.
      destruct (evale' finalHeap' (rhoSubst x0 vresult initialRho)
             (eSubsts [(xthis, x1); (xUserDef z, x2); (xresult, x0)]
                e1)); try tauto.
      destruct v1; try tauto.
      eapply IHe1 in H1; try eca.
      destruct (evale' finalHeap' finalRho' e1); try tauto.
      destruct v1; try tauto.
      inversionx H1; try tauto. inversionx H5.
      assumption.

    assert (∀ x, In x (FV phi_r) → finalRho x = initialRho x)
    as FV_phi_r.
      intros.
      unfold finalRho, rhoSubst.
      dec (x_dec x3 x0); try tauto.
      apply phi_r_x0 in H0. tauto.
      
    assert (footprint finalHeap'  finalRho   phi_r
          = footprint initialHeap initialRho phi_r)
    as fp_eq_2.
      erewrite (footprintChangeRho finalRho initialRho); eauto.
      erewrite (footprintChangeHeap initialHeap finalHeap'); eauto.
      
    assert (incl (footprint finalHeap'  r' phi_post)
                 (footprint initialHeap r' phi_pre))
    as fp_incl_1.
      unfold incl. intro AA. intro inFP.
      assert (In AA (footprint finalHeap' finalRho' phi_post))
      as inFP2.
        unfold footprint in *.
        apply in_flat_map in inFP.
        apply in_flat_map.
        invE inFP p'. inversionx inFP.
        eex.
        destruct p'; try tauto.
        simpl in *.
        assert (forall e o, evale' finalHeap' r' e = Some (vo o)
                         -> evale' finalHeap' finalRho' e = Some (vo o))
        as ev'tmp.
          induction e1; intros; simpl in *.
            tauto.
            subst r'. unfold rhoFrom3 in H2.
              dec (x_dec x3 xresult). destruct T_r; discriminate. clear de2.
              dec (x_dec x3 xthis). inversionx H2. apply fr'xthis. clear de2.
              dec (x_dec x3 (xUserDef z)). inversionx H2. apply fr'xUDz.
              discriminate.
            destruct (evale' finalHeap' r' e1); try discriminate.
              destruct v1; try discriminate.
              erewrite IHe1; eauto.
        specialize (ev'tmp e0).
        destruct (evale' finalHeap' r' e0); try tauto.
        destruct v1; try tauto.
        erewrite ev'tmp; eauto.
      apply evalphiImpliesAccess in eph_phi_post.
      apply eph_phi_post in inFP2.
      assert (finalHeap' (fst AA) <> None) as nn.
        eappIn INV2 inFP2. inversionE inFP2. rewrite H0. discriminate.
      eappIn dynSemStarNoAccessInventing inFP2.
      subst fp.
      inversionx inFP2; try tauto.
      (*contradiction*)
      exfalso.
      admit.
        

    assert (incl (footprint finalHeap'  finalRho   phi_r)
                 (footprint initialHeap initialRho phi_r))
    as fp_incl_2.
      rewrite fp_eq_2. apply incl_refl.
    
    assert (evalphi initialHeap initialRho (Aexcept initialAccess fp) phi_r ->
            evalphi finalHeap'  finalRho   (Aexcept initialAccess fp) phi_r)
    as phi_r_changeEnv.
      intro ep_start.
      eapp (evalphiChangeRho initialRho finalRho).
        intros.
        subst finalRho.
        unfold rhoSubst.
        dec (x_dec x3 x0); try tauto.
        apply phi_r_x0 in H0. tauto.
      eapp (evalphiChangeHeap initialHeap finalHeap').
      
    assert (evalphi
        finalHeap'
        finalRho
        (Aexcept initialAccess fp ++ footprint finalHeap' finalRho' phi_post)
        phi_end)
    as eph_phi_end.
      subst phi_end.
      apply evalphiSymm.
      apply evalphiComposeDisjointFPx.
    (**)subst fp.
        apply evalphiImpliesAccess in ep_phi_r.
        apply inclAexceptDisjoint in ep_phi_r.
        unfold phiSubsts2 in ep_phi_r.
        erewrite footprintPhiSubsts2RhoFrom3 in ep_phi_r; eauto;
        try apply mmwd;
        try apply hdtX1;
        try apply hdtX2.
        unfold phiSubsts3.
        erewrite footprintPhiSubsts3RhoFrom3; eauto;
        try apply mmwd;
        try apply frx0;
        try apply frx1;
        try apply frx2.
        assert (disjoint
              (footprint finalHeap' finalRho phi_r)
              (footprint finalHeap' r' phi_post)
             -> disjoint
              (footprint finalHeap' finalRho phi_r)
              (footprint finalHeap' (rhoFrom3 xresult vresult xthis (vo vo1) (xUserDef z) v2) phi_post)
        ) as narr.
          admit.
        eapp narr.
        unfold disjoint in *.
        intro AA. specialize (ep_phi_r AA).
        unfold not in *.
        inversionx ep_phi_r.
          apply or_introl. intro. contradict H0. eapp fp_incl_2.
          apply or_intror. intro. contradict H0. eapp fp_incl_1.
    (**)eapp (evalphiIncl finalHeap' finalRho phi_r (Aexcept initialAccess fp)). intuition.
        subst fp preI.
        rewrite app_comm_cons in ep_preI.
        apply evalphiApp in ep_preI. inversionx ep_preI.
        simpl in H1.
        unfold phiSubsts2 in H1.
        rewrite (footprintPhiSubsts2RhoFrom3 _ _ _ _ _ (defaultValue T_r) (vo vo1) v2)
        in H1; auto. (*3*)
          apply mmwd.
          apply hdtX2.
          apply hdtX1.
    (**)eapp (evalphiIncl finalHeap' finalRho (phiSubsts3 xthis x1 (xUserDef z) x2 xresult x0 phi_post) (footprint finalHeap' finalRho' phi_post)). intuition.
        eapp evalphiIncl;
        try eapp (evalphi2PhiSubsts3
                finalHeap'
                initialRho
                finalRho'
                x0 x1 x2 vo1 v2 vresult z
                phi_post
                finalAccess'). (*6*)
          apply mmwd.
          apply hdtX1.
          apply hdtX2.
          simpl in xDist. intuition.
          simpl in xDist. intuition.
          simpl in xDist. intuition.

    (*CONT...*)
    assert (invAll
        G
        finalHeap'
        finalRho
        (Aexcept initialAccess fp ++ footprint finalHeap' finalRho' phi_post)
        phi_end)
    as INV3.
      assert (sfrmphi [] phi_post) as tmp_sfrm. apply INV2.
      uninv. repeat split. (*6*)
   (**) subst phi_end.
        apply sfrmphiApp. split.
        unfold phiSubsts3.
          assert (sfrmphi [] phi_post) as sfp. apply INV2. eapply sfrmphiPhiSubsts3 in sfp. apply sfp.
          eapp sfrmIncl. apply inclEmpty.
      (*inversionx tmp_sfrm. inversionx H1. inversionx H3. apply H4. *)
   (**) apply eph_phi_end.
   (**) assert (∀ (e0 : e) (T : T),
          match e0 with
          | ev _ => True
          | ex _ => True
          | edot e1 _ => phiImplies phi_i [phiNeq e1 (ev vnull)]
          end
          → hasStaticType G e0 T
            → ehasDynamicType initialHeap initialRho e0 T) as invty.
          apply INV0.
        induction e0; intros; inversionx H1; simpl in *. (*4*)
          eex. eca.
          eex. eca.
          subst finalRho.
            unfold rhoSubst, ehasDynamicType, evale. simpl.
            dec (x_dec x3 x0).
              eex.
              assert (T0 = T_r) as Teq.
                inversionx hstX0. rewrite H3 in H4. inversionx H4. tauto.
              subst.
              assert (ehasDynamicType finalHeap' finalRho' (ex xresult) T_r) as tt.
                apply INV2; auto. eca.
              inversionx tt. inversionx H1. common.
              rewrite vres in H2. inversionx H2.
              assumption.
            specialize (invty (ex x3) T0).
            apply invty in H0.
              inversionx H0. inversionx H1. eex.
              inversionx H2; try (eca; fail).
              eappIn HeapGetsMoreSpecific H3.
              invE H3 mmx. eca.
            eca.
          apply H0 in eph_phi_end.
            inversionx eph_phi_end.
            inversionx H12.
            apply IHe0 in H5.
              inversionE H5. inversionx H1.
              common.
              rewrite H2 in *. inversionx H4. inversionx H11.
              inversionx H3; try tauto.
              eapply INV2 in H7; eauto. inversionx H7. inversionx H1.
              eex.
              unfold evale. simpl. rewrite H2, H9. simpl. assumption.
            destruct e0; auto.
            eapp phiImpliesTrans.
            apply phiImpliesEdotNeq.
   (**) apply INV2.
   (**) decompose [and] INV0. invE H4 omin0.
        decompose [and] INV1. invE H10 omin1.
        decompose [and] INV2. invE H16 omin2.
        exists (max omin0 omin2). intro o'. intro o'max.
        assert (omin0 <= o') as om0. eapply le_trans. eapp Nat.le_max_l. eauto.
        assert (omin2 <= o') as om2. eapply le_trans. eapp Nat.le_max_r. eauto.
        apply H4  in om0.
        apply H16 in om2.
        split. apply om2.
        intros. unfold not in *. intro inn. apply in_app_iff in inn.
        inversionx inn.
          apply InAexcept in H17. apply om0 in H17. tauto.
          apply evalphiImpliesAccess in eph_phi_post. apply eph_phi_post in H17. apply om2 in H17. tauto.
   (**) intros.
        destruct A'. simpl.
        apply in_app_iff in H0. inversionx H0.
          apply InAexcept in H1.
          apply INV0 in H1.
          inversionE H1. inversionx H0.
          destruct x3.
          eappIn HeapGetsMoreSpecific H2. inversionE H2.
          eex.
        apply evalphiImpliesAccess in eph_phi_post.
        apply eph_phi_post in H1.
        apply INV2 in H1.
        eauto.
    (*MERGE*)
    assert (forall a b c d, dynSem a b -> dynSemStar b c -> dynSem c d -> dynSemStar a d)
    as strat.
      intros. eca. eapp dynSemStarBack.
    
    eex.
    
  - unfoldINV INV.
    (*sAssert*)
    do 4 eexists; try emagicProgress. (*progress*)
    repeat split; repeat constructor.
    * assumption.
    * assumption.
    * assumption.
    * assumption.
    * eax.
    * apply INVAevals.
  - unfoldINV INV.
    (*sRelease*)
    applyINVphi2 INVphi2 H0.
    do 4 eexists; try emagicProgress; 
    try (apply evalphiPrefix in evp; assumption). (*progress*)
    repeat split; repeat constructor.
    * assumption.
    * apply evalphiApp in evp. intuition.
    * intros.
      eapp INVtypes.
      destruct e0; auto.
      eapp phiImpliesTrans.
      eappIn phiImpliesTrans H2.
      eapp phiImpliesSuffix.
    * apply INVHELPER.
    * eexists omin.
      intros.
      apply INVheapNT in H2. unf.
      split; auto.
      intros.
      unfold not in *.
      specialize (H4 f0).
      intros.
      contradict H4.
      apply InAexcept in H2.
      assumption.
    * intros.
      apply InAexcept in H2.
      eapp INVAevals.
  - unfoldINV INV.
    (*sDeclare*)
    assert (evalphi initialHeap (rhoSubst x0 (defaultValue T0) initialRho)
      initialAccess (phiEq (ex x0) (ev (defaultValue' T0)) :: phi0)) 
    as eph.
      eca. apply inclEmpty. eca; unfold evale; simpl; eauto. eapp rhoSubstId.
      common. admit.
    assert (invAll (GammaSet x0 T0 G) initialHeap (rhoSubst x0 (defaultValue T0) initialRho) initialAccess
         (phiEq (ex x0) (ev (defaultValue' T0)) :: phi0)) as IH.
      uninv.
      repeat split; repeat constructor.
        eapp sfrmIncl. apply inclEmpty.
        assumption.
        induction e0; intros.
          inversionx H2; repeat eca.
          inversionx H2.
            unfold ehasDynamicType, rhoSubst, evale, GammaSet in *. simpl.
            dec (x_dec x1 x0).
              dec (x_dec x0 x0). inversionx H5. eex. apply hasDynamicTypeDefault.
            rename de2 into de. dec (x_dec x0 x1). contradict de. tauto.
            assert (hasStaticType G (ex x1) T1) as tt. eca.
            eappIn INVtypes tt.
          inversionx H2. apply H1 in eph.
            inversionx eph.
            inversionx H13.
            apply IHe0 in H6.
              inversionE H6. inversionx H2.
              common.
              rewrite H3 in *. inversionx H5. inversionx H12.
              inversionx H4; try tauto.
              eapply INVHELPER in H8; eauto. inversionx H8. inversionx H2.
              eex.
              unfold evale. simpl. rewrite H3, H10. simpl. assumption.
            destruct e0; auto.
            eapp phiImpliesTrans.
            apply phiImpliesEdotNeq.
        apply INVHELPER.
        exists omin. apply INVheapNT.
        apply INVAevals.
    eapply IHHO in IH. clear IHHO.
    invE IH fH.
    invE IH fR.
    invE IH fA.
    
    rewriteRev app_comm_cons.
    
    do 4 eexists. (*progress*)
      eca. eca.
      apply IH.
    repeat split; repeat constructor; try apply IH.
    intros.
    apply IH; auto.
    generalize e0 T1 H0 H2. clear.
    induction e0; intros; inversionx H2; eca.
    unfold GammaSet.
    dec (x_dec x0 x1); auto.
    rewrite H0 in *.
    discriminate.
  - (*HSEC*)
    eapply IHHO1 in INV. unf.
    eapply IHHO2 in H2. unf.
    do 4 eexists; eauto.
    rewrite app_assoc_reverse.
    eapp dynSemStarTrans.
Admitted.


Theorem initialINV : 
  invAll GammaEmpty newHeap newRho newAccess [].
Proof.
  uninv; intuition.
  - eca.
  - eca.
  - unfold GammaEmpty, ehasDynamicType, evale in *.
    inversionx H1; simpl; try (eex; eca).
    * discriminate.
    * apply (phiImpliesTauto newHeap newRho newAccess) in H0.
      inversionx H0.
      inversionx H12.
      common.
      inversionx H10.
      inversionx H2; simpl in *.
      + inversionx H5. tauto.
      + discriminate.
      + destruct (evale' newHeap newRho e0); try discriminate.
        destruct v0; try discriminate.
  - discriminate.
  - exists 0.
    eca.
Qed.