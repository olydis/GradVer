Load GradVer20Hook.
Import Semantics.

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
Definition invHeapConsistent
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    forall o C m f T,
      Heap o = Some (C, m) ->
      fieldType C f = Some T ->
      exists v, m f = Some v /\ hasDynamicType Heap v T.
Definition invHeapNotTotal
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    ∃ omin : o,
    forall o' : o,
      (omin <= o') -> Heap o' = None /\ (forall f, ~ In (o', f) A).

Definition invAll
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    invPhiHolds
      Heap rho A phi /\
    invTypesHold
      Heap rho A phi /\
    invHeapConsistent
      Heap rho A phi /\
    invHeapNotTotal
      Heap rho A phi.

Ltac emagicProgress :=
  repeat eexists;
  econstructor; econstructor;
  unfold evale; simpl; eauto.

Definition soundness pre s post initialHeap initialRho initialAccess S : Prop :=
  hoare pre s post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s) :: S) (finalHeap, (finalRho, finalAccess, []) :: S) /\
    invAll finalHeap finalRho finalAccess post.

Ltac uninv :=
  unfold invAll in *;
  unfold invPhiHolds in *;
  unfold invTypesHold in *;
  unfold invHeapConsistent in *;
  unfold invHeapNotTotal in *.

Ltac applyINVtypes INVtypes H :=
  apply INVtypes in H;
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
  inversion INVcarry2 as [INVHELPER INVheapNT']; clear INVcarry2;
  inversion INVheapNT' as [omin INVheapNT]; clear INVheapNT'.


Lemma evale'ChangeRho : forall r1 r2 H e,
  (forall x, In x (FVe e) -> r1 x = r2 x) ->
  evale' H r1 e = evale' H r2 e.
Proof.
  induction e0; intros; simpl in *.
  - tauto.
  - apply H1.
    tauto.
  - rewrite IHe0;
    tauto.
Qed.

Lemma footprint'ChangeRho : forall r1 r2 H p,
  (forall x, In x (FV' p) -> r1 x = r2 x) ->
  footprint' H r1 p = footprint' H r2 p.
Proof.
  intros.
  destruct p0; try tauto.
  simpl in *.
  erewrite evale'ChangeRho; tauto.
Qed.
  
Lemma evalphi'ChangeRho : forall r1 r2 H p A,
  (forall x, In x (FV' p) -> r1 x = r2 x) ->
  evalphi' H r1 A p ->
  evalphi' H r2 A p.
Proof.
  intros; simpl in *.
  inversionx H2.
  - constructor.
  - simpl in *.
    eca; unfold evale in *;
    erewrite evale'ChangeRho in H4, H5; eauto;
    intros; intuition.
  - simpl in *.
    eca; unfold evale in *;
    erewrite evale'ChangeRho in H4, H5; eauto;
    intros; intuition.
  - simpl in *.
    eca; unfold evale in *;
    erewrite evale'ChangeRho in H4; eauto;
    intros; intuition.
  - simpl in *.
    eca.
    rewrite H1 in H4; auto.
Qed.

Lemma evalphiChangeRho : forall r1 r2 H p A,
  (forall x, In x (FV p) -> r1 x = r2 x) ->
  evalphi H r1 A p ->
  evalphi H r2 A p.
Proof.
  induction p0; intros; simpl in *; try constructor.
  inversionx H2.
  eca.
  - rewrite (footprint'ChangeRho r1 r2) in H7; auto.
    intros.
    intuition.
  - rewrite (footprint'ChangeRho r1 r2) in H12; auto.
    * eapp (evalphi'ChangeRho r1 r2).
      intros. intuition.
    * intros. intuition.
  - rewrite (footprint'ChangeRho r1 r2) in H13; auto.
    * eapp IHp0.
      intros. intuition.
    * intros. intuition.
Qed.


Theorem staSemSoundness : forall (s'' : s) (s' : list s) (pre post : phi) initialHeap initialRho initialAccess,
  hoareSingle pre s'' post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, [(initialRho, initialAccess, s'' :: s')]) (finalHeap, [(finalRho, finalAccess, s')]) /\
    invAll finalHeap finalRho finalAccess post
.
Proof.
  destruct s'';
  do 6 intro;
  intro HO;
  intro INV;
  inversionx HO.
  - unfoldINV INV.
    (*sMemberSet*)
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
    * eexists. intros. apply INVheapNT in H0. unf.
      unfold HSubst.
      rewrite H1.
      dec (o_dec o' o0); tauto.
  - unfoldINV INV.
    (*sAssign*)
    assert (HH3 := H3).
    applyINVtypes INVtypes H8.
    applyINVphi2 INVphi2 H2.
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
    * apply sfrmphiApp; try assumption.
      repeat constructor.
      assumption.
    * apply eph.
    * induction e1; intros; unfold ehasDynamicType, evale; 
      inversionx H0; simpl in *.
      + eex. eca.
      + eex. eca.
      + apply H9 in eph.
        inversionx eph.
        inversionx H17.
        eex.
      + apply H12 in eph.
        inversionx eph.
        inversionx H19.
        
        apply IHe1 in H9.
        inversionx H9. unf.
        
        common.
        inversionx H18.
        rewrite H11 in *.
        inversionx H7.
        inversionx H8; try tauto.
        rewrite H16.
        simpl.
        eapp INVHELPER.
    * apply INVHELPER.
    * eax.
  - unfoldINV INV.
    (*sAlloc*)
    pose proof (INVheapNT omin) as newHeap.
    assert (omin ≤ omin). auto.
    apply newHeap in H0. unf.
    set (x1 := omin) in *.
    
    unfold fieldsNames in *.
    common.
    
    do 4 eexists; try emagicProgress. (*progress*)
    assert (evalphi (Halloc x1 c initialHeap) (rhoSubst x0 (vo x1) initialRho)
      (initialAccess ++ map (λ cf' : T * f, (x1, snd cf')) l)
      (accListApp x0 (map snd l)
         (phiType x0 (TClass c) :: phiNeq (ex x0) (ev vnull) :: phi'0)))
          as eph.
      assert (listDistinct (map snd l)) as fd.
        eapp fieldsDistinct.
      assert (forall l,
          listDistinct (map snd l) ->
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
        induction l0; intros; simpl in *.
          rewrite app_nil_r. assumption.
        unf.
        apply IHl0 in H7; auto.
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
          apply in_map_iff in H0.
          unf.
          inversionx H0.
          eex.
        rewrite H0.
        assumption.
      apply remAccList; auto.
      eca; simpl; try apply inclEmpty. eca; try rewrite rhoSubstId; eauto. eapply hasDynamicTypeHalloc; eauto.
      common.
      eca; simpl; try apply inclEmpty. eca; unfold evale; simpl; try rewrite rhoSubstId; eauto. discriminate.
      common.
      eapp evalphiRemoveHalloc.
      eapp evalphiRemoveRhoSubst.
    assert (∀ (o0 : o) (C0 : C) (m0 : f → option v) (f0 : f) 
      (T0 : T),
      Halloc x1 c initialHeap o0 = Some (C0, m0)
      → fieldType C0 f0 = Some T0
        → ∃ v0 : v,
          m0 f0 = Some v0 ∧ hasDynamicType (Halloc x1 c initialHeap) v0 T0) as hlp.
      intros.
      unfold Halloc in H0.
      rewrite Heqo0 in *.
      dec (o_dec x1 o0).
        inversionx H0.
        assert ((find
           (λ fs' : T * string, if string_dec f0 (snd fs') then true else false)
           l) = Some (T0, f0)) as fi.
          unfold fieldType, fields in *.
          destruct (class C0); try discriminate.
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
        
        eapply INVHELPER in H0; eauto. unf.
        eex.
        unfold Halloc. rewrite Heqo0.
        inversionx H9; try constructor.
        rename de2 into ung.
        eca.
        dec (o_dec x1 o1); eauto.
        rewrite H1 in *.
        discriminate.
    repeat split; repeat constructor.
    * generalize l H3. clear.
      induction l; intros; simpl in *.
      + repeat constructor.
        assumption.
      + repeat constructor.
        eapply sfrmIncl; eauto.
        apply inclEmpty.
    * apply eph.
    * induction e0; intros; inversionx H0; simpl in *.
      + eex. eca.
      + eex. eca.
      + apply H9 in eph.
        inversionx eph. inversionx H16.
        eex.
      + apply H11 in eph.
        inversionx eph. inversionx H18.
      
        apply IHe0 in H9.
        inversionx H9. unf.
        common.
        inversionx H17.
        rewrite H10 in *.
        inversionx H7.
        inversionx H8; try tauto.
        
        eapply hlp in H13; eauto. unf.
        eex.
        unfold evale.
        simpl.
        rewrite H10.
        rewrite H15.
        simpl.
        assumption.
    * apply hlp.
    * exists (Datatypes.S x1).
      intros.
      assert (omin <= o').
        apply le_S_n.
        eapp le_trans.
      apply INVheapNT in H7. unf.
      split.
      + unfold Halloc.
        rewrite Heqo0.
        dec (o_dec x1 o'). contradict H0. auto with arith.
        assumption.
      + intros.
        specialize (H9 f0).
        intuition.
        apply in_app_iff in H7.
        inversionx H7; try tauto.
        apply in_map_iff in H10.
        unf.
        inversionx H10.
        subst.
        contradict H0. auto with arith.
  - (*sCall*)
    rename INV into INV0.
    rename H6 into hstX0.
    rename H4 into hstX1.
    rename H7 into hstX2.
    rename H13 into xDist.
    rename H9 into phi_r_sf.
    rename H11 into phi_r_x0.
    rename H8 into impl.
    rename H5 into mme.
    set (mm := Method T_r m0 T_p z (Contract phi_pre phi_post) underscore) in *.
    set (preI := (phiNeq (ex x1) (ev vnull) :: phiSubsts2 xthis x1 (xUserDef z) x2 phi_pre ++ phi_r)) in *.
    
    assert (evalphi initialHeap initialRho initialAccess preI)
    as ep_preI.
      unfoldINV INV0. eapp impl.
    
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
      inversionx H9.
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
    set (phi_pre' := phiType (xUserDef z) T_p :: phiType xthis (TClass C0) :: phi_pre) in *.
    set (phi_post' := phiType (xUserDef z) T_p :: phiType xthis (TClass C0) :: phiType xresult T_r :: phi_post) in *.
    set (S'' := [(initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s')]).
    set (phi_end := phiSubsts3 xthis x1 (xUserDef z) x2 xresult x0 phi_post ++ phi_r).
    
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
    
    assert (evalphi initialHeap r' fp phi_pre')
    as ep_phi_pre'.
      eca; simpl.
        apply inclEmpty.
        eca; try apply hdtX2.
      common.
      eca; simpl.
        apply inclEmpty.
        eca; try apply hdtX1.
      common.
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
    
    assert (invAll initialHeap r' fp phi_pre')
    as INV1.
      uninv. repeat split; simpl; try constructor. (*5*)
        unf. assumption.
        apply ep_phi_pre'.
        induction e0; intros; inversionx H0; simpl in *. (*4*)
          eex. eca.
          eex. eca.
          apply H3 in ep_phi_pre'.
            inversionx ep_phi_pre'.
            inversionx H10.
            eex.
          apply IHe0 in H3.
            inversionE H3. inversionx H0.
            apply H5 in ep_phi_pre'. inversionx ep_phi_pre'. inversionx H13.
            common. inversionx H12. rewrite H1 in *. inversionx H6. inversionx H2; try tauto.
            eapply INV0 in H7; eauto. inversionE H7. inversionx H0.
            eex. unfold evale. simpl. rewrite H1. rewrite H9. simpl. assumption.
        unf. assumption.
        unf. exists x3. intros. apply H20 in H16. intuition. apply fp_incl_ia in H25. apply H24 in H25. tauto.
    
    (*Part 2: method body*)
    assert (∃ finalHeap finalRho finalAccess,
          dynSemStar 
            (initialHeap, [(r', fp, underscore)])
            (finalHeap, [(finalRho, finalAccess, [])]) ∧
          invAll finalHeap finalRho finalAccess phi_post')
    as call_finished.
      assert (soundness phi_pre' underscore phi_post' initialHeap r' fp []) as sdn. admit. (*assume that for method body*)
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
    
    assert (∀ (A : A'_d) (v0 : v),
      ¬ In A fp -> evalA'_d initialHeap A = Some v0 → 
                   evalA'_d finalHeap'  A = Some v0)
    as Hinv.
      intros.
      eapp dynSemStarNotModifiesH.
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
    
    assert (evalphi finalHeap' finalRho' finalAccess' phi_post')
    as eph_phi_post'.
      apply INV2.
    
    assert (evalphi finalHeap' finalRho' finalAccess' phi_post)
    as eph_phi_post.
      inversionx eph_phi_post'.
      inversionx H10.
      inversionx H13.
      simpl in H15. common.
      apply H15.
    
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
      
      Check Hinv.
      

(* Lemma evale'ChangeHeap : forall r1 r2 H e,
   (∀ A' v, In A' A 
      → evalA'_d H1 A' = Some v
      → evalA'_d H2 A' = Some v) ->
  evale' H r1 e = evale' H r2 e.
Proof.
  induction e0; intros; simpl in *.
  - tauto.
  - apply H1.
    tauto.
  - rewrite IHe0;
    tauto.
Qed. *)

Lemma footprint'ChangeHeap : forall H1 H2 r p,
  goodFP H1 r p ->
   (∀ A' v, In A' (footprint' H1 r p)
      → evalA'_d H1 A' = Some v
      → evalA'_d H2 A' = Some v) ->
  footprint' H1 r p = footprint' H2 r p.
Proof.
  unfold goodFP, A'_s2A'_d, evalA'_d.
  intros.
  destruct p0; try tauto.
  simpl in *.
  destruct (evale' H1 r e0) eqn: ee; try discriminate.
  destruct v0; try discriminate.
  specialize (H3 (o0, f0)).
  simpl in *.
  destruct (v0); try apply inclEmpty.
Admitted.
  
(* Lemma evalphi'ChangeHeap : forall r1 r2 H p A,
  (∀ A' v, In A' A 
    → evalA'_d H1 A' = Some v
    → evalA'_d H2 A' = Some v) ->
  evalphi' H r1 A p ->
  evalphi' H r2 A p.
Proof.
  intros; simpl in *.
  inversionx H2.
  - constructor.
  - simpl in *.
    eca; unfold evale in *;
    erewrite evale'ChangeRho in H4, H5; eauto;
    intros; intuition.
  - simpl in *.
    eca; unfold evale in *;
    erewrite evale'ChangeRho in H4, H5; eauto;
    intros; intuition.
  - simpl in *.
    eca; unfold evale in *;
    erewrite evale'ChangeRho in H4; eauto;
    intros; intuition.
  - simpl in *.
    eca.
    rewrite H1 in H4; auto.
Qed. *)

Lemma evalphiChangeHeap : ∀ H1 H2 r p A,
       (∀ A' v, In A' A 
          → evalA'_d H1 A' = Some v
          → evalA'_d H2 A' = Some v)
       → evalphi H1 r A p → evalphi H2 r A p.
Proof.
  induction p0; intros; simpl in *; try constructor.
  inversionx H3.
  eca.
  admit.
  admit.
  eapp IHp0.
  
  

      Check evalphiImpliesAccess.
      subst fp.
      Check evalphiChangeHeap.
      admit. admit.

    assert (evalphi
        finalHeap'
        finalRho
        (Aexcept initialAccess fp ++ footprint finalHeap' finalRho' phi_post)
        phi_end)
    as eph_phi_end.
      subst phi_end.
      apply evalphiSymm.
      apply evalphiComposeDisjointFP.
        subst fp.
          admit.
        subst fp preI.
          rewrite app_comm_cons in ep_preI.
          apply evalphiApp in ep_preI. inversionx ep_preI.
          simpl in H1.
          unfold phiSubsts2 in H1.
          rewrite (footprintPhiSubsts2RhoFrom3 _ _ _ v2 _ _ T_r vo1)
          in H1; auto. (*3*)
            apply mmwd.
            apply hdtX2.
            apply hdtX1.
        admit.
        
      apply evalphiAppRev.
    (**)eapp evalphiIncl.
        apply (evalphi2PhiSubsts3
                finalHeap'
                initialRho
                finalRho'
                x0 x1 x2 vo1 v2 vresult z
                phi_post
                finalAccess') in eph_phi_post; eauto. (*8*)
          apply mmwd.
          apply hdtX1.
          apply hdtX2.
          eapply (dynSemStarNotModifies xthis _ _ _ r' finalRho') in part2'; eauto. apply mmwd.
          eapply (dynSemStarNotModifies (xUserDef z) _ _ _ r' finalRho') in part2'; eauto. rewrite r'xUDz in *. rewrite part2'. tauto. apply mmwd.
          simpl in xDist. intuition.
          simpl in xDist. intuition.
          simpl in xDist. intuition.
    (**)subst preI.
        rewrite app_comm_cons in ep_preI.
        apply evalphiApp in ep_preI.
        inversionx ep_preI.
        
        subst finalRho.
        eapp evalphiRemoveRhoSubst.
        
        eapp evalphiIncl.
        apply evalphiImpliesAccess in H1.
        apply inclAexceptDisjoint in H1.
        admit.
  
(* 
Lemma footprintLength : forall H1 H2 r A p,
  evalphi H1 r A p ->
  length (footprint H1 r p) >= length (footprint H2 r p).
Proof.
  induction p0; intros; simpl in *; try auto.
  inversionx H0.
  apply evalphiAexcept in H13.
  apply IHp0 in H13.
  destruct a; simpl in *; auto.
  inversionx H12.
  destruct (evale' H1 r e0); try tauto.
  destruct v0; try tauto.
  repeat rewrite app_length.
  simpl.
  destruct (evale' H2 r e0); auto with arith.
  destruct v0; auto with arith.
Qed.

Lemma eq_le_ge : forall a1 a2 b1 b2,
  a1 + a2 = b1 + b2 ->
  a2 >= b2 ->
  a1 <= b1.
Proof.
  intros.
  assert (a1 + a2 ≥ a1 + b2).
    auto with arith.
  rewrite H0 in H2.
  unfold ge in *.
  SearchAbout le.
  rewrite (plus_comm a1 b2) in H2.
  rewrite (plus_comm b1 b2) in H2.
  eapp plus_le_reg_l.
Qed.

Lemma appEqFootprint : forall H1 H2 r a p A,
  evalphi H1 r A (a :: p) ->
  footprint H1 r (a :: p) = footprint H2 r (a :: p) ->
  footprint' H1 r a = footprint' H2 r a /\
  footprint H1 r p = footprint H2 r p.
Proof.
  destruct a; try (simpl in *; tauto).
  intros.
  inversionx H0.
  apply (footprintLength H1 H2) in H14.
  assert (length (footprint' H1 r (phiAcc e0 f0)) 
       <= length (footprint' H2 r (phiAcc e0 f0))).
    apply lengthId in H3. simpl in H3.
    repeat rewrite app_length in H3.
    eapp eq_le_ge.
  
  inversionx H13. common.
  
  simpl in *.
  rewrite H11 in *.
  simpl in *.
  destruct (evale' H2 r e0); try (contradict H0; auto with arith; fail).
  destruct (v0); try (contradict H0; auto with arith; fail).
  simpl in *.
  inversionx H3.
  auto.
Qed.

Lemma evale'ChangeHeap : forall H1 H2 r e f o A p,
  evalphi H1 r A p ->
  footprint H1 r p = footprint H2 r p ->
  In (e, f) (staticFootprint p) ->
  evale' H1 r e = Some (vo o) ->
  evale' H2 r e = Some (vo o).
Proof.
  induction p0; intros; simpl in *; try tauto.
  
  eapply appEqFootprint in H3; eauto. unf.
  
  apply in_app_iff in H4.
  inversionx H4.
  - destruct a; try (simpl in *; tauto).
    simpl in H3. intuition. inversionx H4.
    simpl in H6. 
    rewrite H5 in *.
    destruct (evale' H2 r e0); try discriminate.
    destruct v0; try discriminate.
    inversionx H6.
    tauto.
  - eapp IHp0.
    inversionx H0.
    eapp evalphiAexcept.
Qed.

Lemma evalphiChangeHeap : forall H1 H2 r A p,
  sfrmphi [] p ->
  footprint H1 r p = footprint H2 r p ->
  evalphi H1 r A p ->
  evalphi H2 r A p.
Proof.
  intros.
  assert (forall e f, edotInPhi p0 e f -> In (e, f) (staticFootprint p0))
  as sfp.
    intros. eapp edotphiStaticFootprint.
  
  assert (forall e f, edotInPhi p0 e f -> exists o, evale' H1 r e = Some (vo o) /\ In (o, f) (footprint H1 r p0))
  as dfp.
    intros. eapp edotphiFootprintX.
  
  assert (forall e f, edotInPhi p0 e f -> evale' H1 r e = evale' H2 r e)
  as evt.
    intros.
    assert (In (e0, f0) (staticFootprint p0)).
      eapp sfp.
    apply dfp in H5. unf.
    rewrite H5.
    eapply evale'ChangeHeap in H5; eauto.
  
  
  
Lemma evalphiChangeHeapEdotInPhi : forall H1 H2 r p A,
  footprint H1 r p = footprint H2 r p ->
  (∀ (e : e) (f : f), edotInPhi p e f → evale' H1 r e = evale' H2 r e) ->
  evalphi H1 r A p -> evalphi H2 r A p.
Proof.
  induction p0; intros; simpl in *; try constructor.
  eapply appEqFootprint in H0; eauto. unf.
  inversionx H4.
  eca.
  inversionx H15.
  - constructor.
  - simpl in H3, H5.
    
  
Lemma edotInEevale'irrelevance : forall H1 H2 r e,
  (∀ e' f', edotInE e e' f' → evale' H1 r e' = evale' H2 r e') ->
  evale' H1 r e = evale' H2 r e.
Proof.
  intros.
  destruct e0; try tauto.
  simpl.
  erewrite H0; eauto.
  
  induction e0 eqn: et; intros; simpl in *; try tauto.
  erewrite H0; eauto.
  destruct ()

    eca; unfold evale in *.
    simpl 
  destruct a.
  
  
  
  intro p0.
  intro sfr.
  assert (∀ (e0 : e) (f0 : f), edotInPhi p0 e0 f0 → In (e0, f0) (staticFootprint p0)).
    intros. eapp edotphiStaticFootprint.
  
  Check staticVSdynamicFP.
  
  induction p0; intros; simpl in *; try constructor.
  inversionx H4.
  destruct a.
  
  inversionx H3.
  rewrite H0 in H8; try tauto.
  rewrite H0 in H13; try tauto.
  rewrite H0 in H14; try tauto.
  apply IHp0 in H14; try (intros; apply H0; tauto).
  
  eca.




(* Lemma sfrmphiEvalphi'ChangeHeap : forallH1 H2 r p,
  footprint' H1 r p = footprint' H2 r p ->
  evalphi' H1 r (footprint' H1 r p) p ->
  evalphi' H2 r (footprint' H2 r p) p.

  inversionx H13.
  - constructor.
  - eca. *)

(* Lemma footprint'EqLength : forall H1 H2 r p,
  length (footprint' H1 r p) =
  length (footprint' H2 r p).
Proof.
  intros.
  destruct p0; simpl; try tauto. *)

Lemma app_eq_split : forall {T : Type} (B2 B1 A2 A1 : list T),
  length A1 = length A2 ->
  A1 ++ B1 = A2 ++ B2 ->
  A1 = A2 /\
  B1 = B2.
Proof.
  induction A2; intros; simpl in *.
  - rewrite length_zero_iff_nil in H0.
    subst.
    tauto.
  - destruct A1; simpl in *; try discriminate.
    inversionx H0.
    inversionx H1.
    apply IHA2 in H3; auto.
    unf.
    subst.
    tauto.
Qed.

(* Lemma InFootprintFV : forall
  incl (FV p) xs ->
  In (ao, af) (footprint H r p) ->
  
      
    apply InAexcept
    apply InAexceptConstr.
    
    rewrite AexceptAppFirst. apply incl_appr.
    rewrite AexceptAppFirst. apply incl_appr.
    rewrite AexceptApp.
    
    generalize ppost H9.
    
    Check footprint'PhiSubsts2RhoFrom3.

Lemma footprint'PhiSubsts3RhoFrom3 : forall H r z v2 x1 x2 T_r vo1 a,
  incl (FV' a) [xUserDef z; xthis] ->
  r x2 = Some v2 ->
  r x1 = Some (vo vo1) ->
  r x0 = Some vresult ->
  footprint' H r (phi'Substs [(xthis, x1); (xUserDef z, x2); (xresult, x0)] a) =
  footprint' H (rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) (xUserDef z) v2) a.
Proof.
  intros.
  destruct a; simpl in *; try tauto.
  erewrite evale'eSubsts2RhoFrom3; auto.
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
Qed. *)

     *)
    
    (*CONT...*)
    assert (invAll
        finalHeap'
        finalRho
        (Aexcept initialAccess fp ++ footprint finalHeap' finalRho' phi_post)
        phi_end)
    as INV3.
      assert (sfrmphi [] phi_post') as tmp_sfrm. apply INV2.
      uninv. repeat split. (*5*)
   (**) subst phi_end.
        apply sfrmphiApp.
        unfold phiSubsts3.
          assert (sfrmphi [] phi_post) as sfp. apply INV2. eapply sfrmphiPhiSubsts3 in sfp. apply sfp.
          eapp sfrmIncl. apply inclEmpty.
      (*inversionx tmp_sfrm. inversionx H1. inversionx H3. apply H4. *)
   (**) apply eph_phi_end.
   (**) induction e0; intros; inversionx H0; simpl in *. (*4*)
          eex. eca.
          eex. eca.
          apply H3 in eph_phi_end.
            inversionx eph_phi_end.
            inversionx H10.
            eex.
          apply H5 in eph_phi_end.
            inversionx eph_phi_end.
            inversionx H12.
            apply IHe0 in H3.
            inversionE H3. inversionx H0.
            common.
            rewrite H1 in *. inversionx H4. inversionx H11.
            inversionx H2; try tauto.
            eapply INV2 in H7; eauto. inversionx H7. inversionx H0.
            eex.
            unfold evale. simpl. rewrite H1, H9. simpl. assumption.
   (**) apply INV2.
   (**) decompose [and] INV0. invE H5 omin0.
        decompose [and] INV1. invE H10 omin1.
        decompose [and] INV2. invE H15 omin2.
        exists (max omin0 omin2). intro o'. intro o'max.
        assert (omin0 <= o') as om0. eapply le_trans. eapp Nat.le_max_l. eauto.
        assert (omin2 <= o') as om2. eapply le_trans. eapp Nat.le_max_r. eauto.
        apply H5  in om0.
        apply H15 in om2.
        split. apply om2.
        intros. unfold not in *. intro inn. apply in_app_iff in inn.
        inversionx inn.
          apply InAexcept in H14. apply om0 in H14. tauto.
          apply evalphiImpliesAccess in eph_phi_post. apply eph_phi_post in H14. apply om2 in H14. tauto.
    
    (*MERGE*)
    assert (forall a b c d, dynSem a b -> dynSemStar b c -> dynSem c d -> dynSemStar a d)
    as strat.
      intros. eca. eapp dynSemStarBack.
    
    eex.
    
  - unfoldINV INV.
    (*sReturn*)
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
    * induction e0; intros.
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
        eapply INVHELPER in H12; eauto. unf.
        eex.
        unfold evale.
        simpl.
        rewrite H10.
        rewrite H11.
        simpl.
        assumption.
    * apply INVHELPER.
    * eax.
  - unfoldINV INV.
    (*sAssert*)
    do 4 eexists; try emagicProgress. (*progress*)
    repeat split; repeat constructor.
    * assumption.
    * assumption.
    * assumption.
    * assumption.
    * eax.
  - unfoldINV INV.
    (*sRelease*)
    applyINVphi2 INVphi2 H1.
    do 4 eexists; try emagicProgress; 
    try (apply evalphiPrefix in evp; assumption). (*progress*)
    repeat split; repeat constructor.
    * assumption.
    * apply evalphiApp in evp. intuition.
    * intros.
      apply phiImpliesSuffix in H1.
      eapply phiImpliesStaticType in H1; eauto.
    * apply INVHELPER.
    * eexists omin.
      intros.
      apply INVheapNT in H0. unf.
      split; auto.
      intros.
      unfold not in *.
      specialize (H4 f0).
      intros.
      contradict H4.
      apply InAexcept in H0.
      assumption.
  - unfoldINV INV.
    (*sDeclare*)
    do 4 eexists; try emagicProgress. (*progress*)
    assert (evalphi
        initialHeap
        (rhoSubst x0 (defaultValue t) initialRho)
        initialAccess
        (phiType x0 t :: phiEq (ex x0) (ev (defaultValue' t)) :: phi'0)) as eph.
      apply H2 in INVphi2.
      econstructor; simpl; eauto.
        apply inclEmpty.
        econstructor; eauto.
          rewrite rhoSubstId.
          eauto.
          apply hasDynamicTypeDefault.
        common.
        econstructor; eauto.
          apply inclEmpty.
          eca; unfold evale; simpl; eauto.
          rewrite rhoSubstId. tauto.
          simpl.
          common.
          erewrite evalphiRemoveRhoSubst; intuition.
    repeat split; repeat constructor.
    * assumption.
    * apply eph.
    * induction e0; intros; inversionx H0; simpl in *.
      + eex. eca.
      + eex. eca.
      + apply H5 in eph.
        inversionx eph. inversionx H13.
        eex.
      + apply H8 in eph.
        inversionx eph. inversionx H15.
        
        apply IHe0 in H5. inversionx H5. unf.
        common.
        rewrite H7 in *.
        inversionx H1. inversionx H14.
        inversionx H3; try tauto.
        
        eapply INVHELPER in H10; eauto. unf.
        eex.
        unfold evale.
        simpl.
        rewrite H7.
        rewrite H12.
        auto.
    * apply INVHELPER.
    * eax.
Admitted.


Theorem initialINV : 
  invAll newHeap newRho newAccess [].
Proof.
  uninv. intuition; try (eca; fail).
  - unfold ehasDynamicType, evale.
    inversionx H0; simpl; try (eex; eca).
    * apply (phiImpliesTauto newHeap newRho newAccess) in H1.
      inversionx H1.
      inversionx H10.
      discriminate.
    * apply (phiImpliesTauto newHeap newRho newAccess) in H2.
      inversionx H2.
      inversionx H12.
      common.
      inversionx H10.
      inversionx H1; simpl in *.
      + inversionx H5. tauto.
      + discriminate.
      + destruct (evale' newHeap newRho e0); try discriminate.
        destruct v0; try discriminate.
  - discriminate.
Qed.