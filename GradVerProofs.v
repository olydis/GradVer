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
    set (phi_pre' := phiType (xUserDef z) T_p :: phiType xthis (TClass C0) :: phi_pre) in *.
    set (phi_post' := phiType (xUserDef z) T_p :: phiType xthis (TClass C0) :: phiType xresult T_r :: phi_post) in *.
    set (S'' := (initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s') :: S').
    set (phi_end := phiSubsts3 xthis x1 (xUserDef z) x2 xresult x0 phi_post ++ phi_r).
    
    (*Part 1: make the call*)
    assert (evalphi initialHeap r' initialAccess phi_pre)
    as ep_phi_pre_rho.
      unf. eapp evalphiPhiSubsts2RhoFrom3.
    
    assert (evalphi initialHeap r' fp phi_pre')
    as ep_phi_pre'.
      eca; simpl.
        apply inclEmpty.
        eca; try apply hdtX2.
        subst r'.
        unfold rhoFrom3.
        dec (x_dec (xUserDef z) xresult). clear de2.
        dec (x_dec (xUserDef z) xthis). clear de2.
        dec (x_dec (xUserDef z) (xUserDef z)).
        eauto.
      common.
      eca; simpl.
        apply inclEmpty.
        eca; try apply hdtX1.
        subst r'.
        unfold rhoFrom3. simpl.
        eauto.
      common.
      eapp evalphiFootprintAccess.
    
    assert (incl fp initialAccess)
    as fp_incl_ia.
      eapp evalphiImpliesAccess.
    
    assert (dynSem 
              (initialHeap, (initialRho, initialAccess, sCall x0 x1 m0 x2 :: s') 
                            :: S')
              (initialHeap, (r', fp, underscore) 
                            :: S'')
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
        unf. exists x3. intros. apply H16 in H12. intuition. apply fp_incl_ia in H12. apply H20 in H12. tauto.
    
    (*Part 2: method body*)
    assert (∃ finalHeap finalRho finalAccess,
          dynSemStar 
            (initialHeap, (r', fp, underscore) :: S'')
            (finalHeap, (finalRho, finalAccess, []) :: S'') ∧
          invAll finalHeap finalRho finalAccess phi_post')
    as call_finished.
      assert soundness as sdn. admit. (*assume that for method body*)
      specialize (sdn phi_pre' underscore phi_post' initialHeap r' fp S'').
      intuition.
    
    invE call_finished finalHeap'.
    invE call_finished finalRho'.
    invE call_finished finalAccess'.
    inversion call_finished as [part2 INV2]. clear call_finished.
    
    (*Part 3: call finished*)
    assert (exists vresult, finalRho' xresult = Some vresult)
    as vres.
      eapp RhoGetsMoreSpecific.
      subst r'. unfold rhoFrom3. simpl. eauto.
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
                          :: (initialRho, Aexcept initialAccess fp , sCall x0 x1 m0 x2 :: s') 
                          :: S')
              (finalHeap',   (finalRho  , Aexcept initialAccess fp ++ footprint finalHeap' finalRho' phi_post, s') 
                          :: S')
           )
    as part3.
      eapply HeapGetsMoreSpecific in part2; eauto. inversionE part2.
      eca; unfold evale; simpl. (*2*)
        apply hdtX1.
        unfold mpost, mcontract. rewrite mme. tauto.
    
    assert (evalphi
        finalHeap'
        finalRho
        (Aexcept initialAccess fp ++ footprint finalHeap' finalRho' phi_post)
        phi_end)
    as eph_phi_end.
      subst phi_end.
      apply evalphiAppRev.
        subst fp finalRho r'.

Lemma incl2PhiSubst3 : 
  forall fH' iR fR' x0 x1 x2 vo1 v2 vresult z T_r e0,
  let xUDz := xUserDef z in
  let r' := rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) xUDz v2 in
  let fR := rhoSubst x0 vresult iR in
  incl (FVe e0) [xUDz; xthis; xresult] ->
  iR x1 = Some (vo vo1) ->
  iR x2 = Some v2 ->
  fR' xthis = r' xthis ->
  fR' xUDz = r' xUDz ->
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
    subst xUDz r' fR.
    inversionx H0.
      rewrite H4.
      unfold rhoFrom3, xSubsts, rhoSubst. simpl.
      rewrite xd3.
      dec (x_dec x2 x0); tauto.
    inversionx H8.
      rewrite H3.
      unfold rhoFrom3, xSubsts, rhoSubst. simpl.
      dec (x_dec x1 x0); tauto.
    inversionx H0.
      rewrite H5.
      unfold xSubsts, rhoSubst. simpl.
      dec (x_dec x0 x0); tauto.
    tauto.
  - subst fR xUDz.
    erewrite IHe0; eauto.
Qed.

Lemma evalphi2PhiSubsts3 : 
  forall iH fH' iR fR' iA x0 x1 x2 vo1 v2 vresult z T_r ppre ppost fA',
  let xUDz := xUserDef z in
  let r' := rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) xUDz v2 in
  let fp := footprint iH r' ppre in
  let fR := rhoSubst x0 vresult iR in
  incl (FV ppost) [xUDz; xthis; xresult] ->
  iR x1 = Some (vo vo1) ->
  iR x2 = Some v2 ->
  fR' xthis = r' xthis ->
  fR' xUDz = r' xUDz ->
  fR' xresult = Some vresult ->
  x0 <> x2 ->
  x0 <> x1 ->
  evalphi
    fH'
    fR'
    fA'
    ppost ->
  evalphi
    fH'
    fR
   (*  (Aexcept iA fp ++ footprint fH' fR' ppost) *)
    (phiSubsts3 xthis x1 xUDz x2 xresult x0 ppost).
  induction ppost; intros; simpl in *; try constructor.
  eca.
  - (*LHS: xthis, xresult, xUDz
       --> x1, x0, x2 
       --> iR x1, vresult, iR x2
       --> vo1, vresult, v2 *)
    (*RHS: xthis, xresult, xUDz
       --> fR' xthis, fR' xresult, fR' xUDz
       --> r' xthis, vresult, r' xUDz
       --> vo1, vresult, v2 *)
    apply incl_appr.
    apply incl_appl.
    destruct a; simpl; try apply inclEmpty.
    simpl in *.
    apply inclApp in H0. inversionx H0.
    subst fR xUDz.
    erewrite incl2PhiSubst3; eauto.
    apply incl_refl.
  - rename H8 into ep.
    destruct a;
    inversion ep as [? | ? ? ? ? ? ? ? ? invc ? inva invb];
    subst; clear ep invb;
    simpl in *.
    * constructor.
    * apply inclApp in H0. unf.
      apply inclApp in H8. unf.
      inversionx inva.
      eca; unfold evale in *;
      subst fR xUDz;
      erewrite incl2PhiSubst3; eauto.
    * apply inclApp in H0. unf.
      apply inclApp in H8. unf.
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
      apply inclSingle in H8.
      inversionx inva.
      subst fR r'. unfold rhoSubst, xSubsts, rhoFrom3 in *. simpl.
      inversionx H8; subst; simpl.
        rewrite H4 in H15. rewrite xd1, xd2, xd3 in H15. inversionx H15.
        eca. rewrite xd3. dec (x_dec x2 x0); tauto.
      inversionx H0; subst; simpl.
        rewrite H3 in H15. simpl in H15. inversionx H15.
        eca. dec (x_dec x1 x0); tauto.
      inversionx H8; subst; simpl.
        rewrite H5 in H15. inversionx H15.
        eca. dec (x_dec x0 x0); tauto.
      tauto.
  - rename H8 into ep.
    inversion ep as [? | ? ? ? ? ? ? ? ? invc ? inva invb]. subst. clear ep inva invc.
    apply inclApp in H0. unf.
    eapply IHppost in invb; eauto.
    eapply evalphiElemWise in invb; eauto.
    intros. rename H10 into ep'.
    assert (incl (FV' p') [x2; x1; x0]) as inclX.
      eapp inclPhiSubsts3.
    destruct p'; inversionx ep'; eca.
    simpl in *.

Lemma evale_portAccess : forall iH fH' iR fR' iA x0 x1 x2 vo1 v2 vresult z T_r ppre ppost a e0 o0 f0,
  let xUDz := xUserDef z in
  let r' := rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) xUDz v2 in
  let fp := footprint iH r' ppre in
  let fR := rhoSubst x0 vresult iR in
  incl (FVe e0) [x2; x1; x0] ->
  evale fH' (rhoSubst x0 vresult iR) e0 (vo o0) ->
  In (o0, f0) (Aexcept iA fp ++ footprint fH' fR' ppost) ->
  In (o0, f0)
    (Aexcept
     (Aexcept iA fp ++ footprint' fH' fR' a ++ footprint fH' fR' ppost)
     (footprint' fH' fR
        (phi'Substs [(xthis, x1); (xUDz, x2); (xresult, x0)] a))).
Proof.
  induction e0; intros; common; simpl in *; inversionx H1.
  - apply inclSingle in H0.
    inversionx H0.
      

      

    
    * eauto.
    * 
      
      eapp evalphiIncl; auto.
  
   eapply IHp0 in H13; eauto.
    intros.
    assert (evalphi' H0 r A2 p') as ep.
    * eapply H1.
      + apply in_cons.
        assumption.
      + eapp evalphi'Aexcept.
    * eapply evalphiFootprintAccess in ep.
      eapply evalphiImpliesAccess in H3.
    
    assert (evalphi H0 r A2 p0) as ep.
    * eapp IHp0.
      + intros.
        apply H1 in H3; auto.
        apply in_cons.
        auto.
      + eapp evalphiAexcept.
    * eapply evalphiImpliesAccess in H13.
      eapply evalphiFootprintAccess in ep.
      eapp evalphiIncl; auto.
      
      
      eapply evalphiFootprint in ep.
    eapply (IHp0 (Aexcept A1 (footprint' H0 r a))).
    * 
    * eauto.
    
    
    eapply evalphiFootprintAccess in invb.
    eapp evalphiIncl.
    
    unfold incl.
    intros. destruct a0.
    rewriteRevIn staticVSdynamicFP H0. unf.
    apply InAexceptConstr.
    rewriteRevIn staticVSdynamicFP' H0.
    unf.
    
      
      
    (* eapply evalphiFootprintAccess in invb. *)
    eapp evalphiIncl.
    
    unfold incl.
    intros.
    apply in_app_iff in H0. inversionx H0.
    * admit.
    * apply InAexceptConstr; intuition.
      destruct a0.
      rewriteRevIn staticVSdynamicFP H10.
      rewriteRevIn staticVSdynamicFP' H0.
      unf.
      
      
      
      Check staticVSdynamicFP.
Lemma InFootprintFV : forall
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
Qed.


    
    assert (incl 
        (footprint
          fH'
          (rhoSubst x0 vresult iR)
          (phiSubsts3 xthis x1 (xUserDef z) x2 xresult x0 ppost))
        (Aexcept iA
            (footprint iH
               (rhoFrom3 xresult (defaultValue T_r) xthis
                  (vo vo1) (xUserDef z) v2) ppre) ++
          footprint fH' fR' ppost)
      ) as inclfp.
      eapp evalphiImpliesAccess.

    
    rewrite AexceptAppFirst.
    rewrite AexceptAppFirst.
    rewrite AexceptApp.
    
    (Aexcept 
      iA
      (footprint iH
         (rhoFrom3 xresult (defaultValue T_r) xthis (vo vo1) (xUserDef z) v2) 
         ppre) ++
        footprint fH' fR' ppost)
          
    (Aexcept
     (Aexcept iA fp ++ 
      footprint' fH' fR' a ++ footprint fH' fR' ppost)
     (footprint' fH' fR
        (phi'Substs [(xthis, x1); (xUDz, x2); (xresult, x0)] a)))
    


      Check evalphi.
      apply evalphiApp.
    
    
    
    
    
    
    
    
    
    (*CONT...*)
    assert (invAll
        finalHeap'
        finalRho
        (Aexcept initialAccess fp ++ footprint finalHeap' finalRho' phi_post)
        phi_end)
    as INV3.
      assert (sfrmphi [] phi_post') as tmp_sfrm. apply INV2.
      uninv. repeat split. (*5*)
   (**) admit.
      (*inversionx tmp_sfrm. inversionx H1. inversionx H3. apply H4. *)
   (**) admit.
   (**) induction e0; intros; inversionx H0; simpl in *. (*4*)
          eex. eca.
          eex. eca.
          admit.
          admit.
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