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

Ltac invE H v := inversion H as [v temp]; clear H; rename temp into H.


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

Theorem staSemSoundness : forall (s'' : s) (s' : list s) (pre post : phi) initialHeap initialRho initialAccess S',
  hoareSingle pre s'' post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s'' :: s') :: S') (finalHeap, (finalRho, finalAccess, s') :: S') /\
    invAll finalHeap finalRho finalAccess post
.
Proof.
  destruct s'';
  do 7 intro;
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
    rename H10 into phi_r_sf.
    rename H12 into phi_r_x0.
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
    set (phi_pre' := phiType (xUserDef z) T_p :: phiType xthis (TClass C0) :: phi_pre).
    set (phi_post' := phiType (xUserDef z) T_p :: phiType xthis (TClass C0) :: phiType xresult T_r :: phi_post).
    
    (*Part 1: make the call*)
    assert (dynSem 
              (initialHeap, (initialRho, initialAccess, sCall x0 x1 m0 x2 :: s') :: S')
              (initialHeap, (r', fp, underscore) :: (initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s') :: S')
           )
    as part1.
      eca; unfold evale; simpl.
        inversionx hdtX1. eauto.
        inversionx hdtX2. eauto.
        tauto.
        unf. eapp evalphiPhiSubsts2RhoFrom3.
    

        Check evalphi
        
        inversionx hdtX1. inversionx H1. apply H6.
      econstructor; unfold evale; simpl; eauto.
      apply evalphiPrefix in H17.
      admit. (*TODO: helper?*)

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