Load GradVer19Theorems.
Import Semantics.

Definition phiEquals (p1 p2 : phi) :=
  forall H r A, evalphi H r A p1 <-> evalphi H r A p2.

Definition wrapHoare (hoare : phi -> s -> phi -> Prop) p1 s p2 : Prop :=
  exists p1x p2x,
  sfrmphi [] p1x /\
  phiImplies p1 p1x /\
  phiImplies p2x p2 /\
  hoare p1x s p2x.

Lemma unfoldTypeJudjFormulaTirrel : forall T1 T2 e T',
  unfoldTypeJudjFormula e T1 T' = unfoldTypeJudjFormula e T2 T'.
Proof.
  induction e0; intros; simpl in *; try tauto.
  rewrite IHe0.
  tauto.
Qed.

Lemma sfrmphiUnfoldType : forall e T T' f,
  sfrmphi [] (unfoldTypeJudjFormula e T T' ++ [phiAcc e f]).
Proof.
  induction e0; intros; simpl in *.
  - repeat eca.
  - repeat eca.
  - apply sfrmphiApp.
    split; auto.
    rewrite staticFootprintApp. simpl.
    repeat eca.
    * intuition.
    * generalize e0 f0. clear.
      induction e0; intros; simpl in *; eca.
      + rewrite staticFootprintApp.
        simpl.
        intuition.
      + eapp sfrmeIncl.
        rewrite staticFootprintApp.
        simpl.
        intuition.
Qed.

Lemma sfrmphiChain : forall p e f0 f1 A,
  sfrmphi A p ->
  In (edot e f0, f1) (staticFootprint p) ->
  In (e, f0) (A ++ staticFootprint p).
Proof.
  intros.
  eapp sfrmphiVSsfpX.
  unfold staticFootprintX, staticFootprint in *.
  apply in_flat_map.
  apply in_flat_map in H1.
  unf.
  destruct x0; try tauto.
  simpl in *. intuition. inversionx H2.
  eex.
  simpl.
  auto.
Qed.

Lemma footprintUnfoldTypeJudjASfpx : forall h r e T' T,
  footprint h r (unfoldTypeJudjFormula e T' T) = rev (footprintXe h r e).
Proof.
  unfold footprintXe.
  induction e0; intros; simpl; try tauto.
  rewrite footprintApp.
  rewrite IHe0.
  rewrite rev_app_distr.
  unfold olist, A'_s2A'_d.
  simpl.
  destruct (evale' h r e0); try tauto.
  destruct v0; tauto.
Qed.

Lemma footprintXeDot : forall e f e' f',
  In (edot e f, f') (staticFootprintXe e') ->
  In (e, f) (staticFootprintXe e').
Proof.
  induction e'; intros; simpl in *; try tauto.
  inversionx H0.
  - inversionx H1.
    simpl.
    auto.
  - apply IHe' in H1.
    auto.
Qed.

Lemma nonRecursiveFootprint : forall e f,
  ¬ In (e, f) (staticFootprintXe e).
Proof.
  induction e0; intros; try tauto.
  autounfold. intro ind.
  simpl in *.
  inversionx ind.
  - inversion H0. contradict H2.
    generalize e0. clear.
    induction e0; intros; try discriminate; simpl in *.
    unfold not in *.
    intros. contradict IHe0.
    inversion H0.
    rewrite H3 in *. clear H3.
    repeat rewriteRev H2.
    tauto.
  - specialize (IHe0 f0).
    contradict IHe0.
    eapp footprintXeDot.
Qed.

Lemma NoDupFPcontradiction : forall h r o f e0 e1 p,
  e0 <> e1 ->
  evale' h r e0 = Some (vo o) ->
  evale' h r e1 = Some (vo o) ->
  NoDup (footprint h r p) ->
  In (e0, f) (staticFootprint p) ->
  In (e1, f) (staticFootprint p) ->
  False.
Proof.
  induction p0; intros; simpl in *; try tauto.
  destruct a; try (eapp IHp0; fail).
  simpl in *.
  inversionx H4.
    inversionx H6.
    rewrite H1 in *.
    simpl in *.
    inversionx H3. contradict H7.
    inversionx H5. inversionx H3. tauto.
    rewrite dynamicASstaticFP.
    rewrite InOflatten, in_map_iff.
    eex. unfold A'_s2A'_d. simpl. rewrite H2. tauto.
  inversionx H5.
    inversionx H4.
    rewrite H2 in *.
    simpl in *.
    inversionx H3. contradict H7.
    rewrite dynamicASstaticFP.
    rewrite InOflatten, in_map_iff.
    eex. unfold A'_s2A'_d. simpl. rewrite H1. tauto.
  eapp IHp0.
  destruct (evale' h r e2); try assumption.
  destruct v0; try assumption.
  inversionx H3.
  assumption.
Qed.

Lemma unfoldTypeJudjLemma : forall e T p,
  (hasStaticType p e T /\ (exists p', phiImplies p p' /\ sfrmphi [] p' /\ sfrme (staticFootprint p') e))
  <->
  (exists T', unfoldTypeJudjPremise e T T' /\ phiImplies p (unfoldTypeJudjFormula e T T')).
Proof.
  induction e0; intros.
  - split; intros; simpl in *; unf.
    * eex.
      + inversionx H1;
        eca.
      + repeat intro.
        eca.
    * split.
      + inversionx H3;
        eca.
      + eex;
        eca.
  - split; intros; simpl in *; unf.
    * eex.
      inversionx H1.
      assumption.
    * subst.
      split; eca.
      split; eauto.
      split; repeat eca.
  - split; intros; simpl in *; unf.
    * assert (H4' := H4).
      inversionx H1.
      inversionx H4.
      assert (hasStaticType p0 e0 (TClass C0) ∧ (∃ p' : phi, phiImplies p0 p' ∧ sfrmphi [] p' ∧ sfrme (staticFootprint p') e0))
        as IH. split; auto. exists x0. auto.
      apply IHe0 in IH; auto. unf.
      eex.
      repeat intro.
      apply evalphiAppRev.
      + apply H4 in H1.
        erewrite unfoldTypeJudjFormulaTirrel.
        eauto.
      + clear H4.
        apply evalphiRemoveAexcept.
      ++  simpl.
          unfold disjoint. intros.
          apply imply_to_or. intros.
          destruct (evale' h r e0) eqn: ee; try tauto.
          destruct v0; try tauto.
          rewrite app_nil_r in *.
          apply InSingle in H4. subst.
          
          rewrite footprintUnfoldTypeJudjASfpx.
          apply H2 in H1.
          apply evalphiDistinctFP in H1.
          rewriteRev in_rev.
          apply sfrmeVSsfpX in H8.
          assert (In (o0, f0) (footprint h r x0)) as inFP.
            apply staticVSdynamicFP. eex.
          autounfold. intro inFPX.
          unfold footprintXe in inFPX.
          apply InOflatten in inFPX.
          apply in_map_iff in inFPX. unf.
          unfold A'_s2A'_d in H5. destruct x2. simpl in *.
          destruct (evale' h r e1) eqn: ee2; try discriminate.
          destruct v0; try discriminate.
          inversionx H5.
          assert (e0 <> e1) as uneq.
            autounfold. intro eqq. subst.
            contradict H10.
            eapp nonRecursiveFootprint.
          apply H8 in H10.
          
          eapp NoDupFPcontradiction.
      ++  apply H2 in H1.
          assert (fp := H1).
          apply evalphiImpliesAccess in fp.
          apply evalphiVSfp in H1.
          eappIn evalsInIn H6. unf.
          unfold A'_s2A'_d in *. simpl in *.
          destruct (evale' h r e0) eqn: ee; try discriminate.
          destruct v0; try discriminate. simpl in *.
          inversionx H5.
          apply fp in H6.
          assert (footprint' h r (phiAcc e0 f0) = [(o0, f0)]) as ffp.
            simpl. rewrite ee. tauto.
          eca; rewrite ffp.
            apply inclSingle. assumption.
            eca. apply in_eq.
          eca.
    * assert (hasStaticType p0 e0 (TClass x1) ∧ (∃ p' : phi, phiImplies p0 p' ∧ sfrmphi [] p' ∧ sfrme (staticFootprint p') e0))
        as IH. 
        eapp IHe0. eex.
        repeat intro.
        apply H2 in H1.
        apply evalphiPrefix in H1.
        erewrite unfoldTypeJudjFormulaTirrel. eauto.
      unf.
      split.
      + eca.
      + exists (unfoldTypeJudjFormula e0 T0 x0 ++ [phiAcc e0 f0]).
        eca.
        split. apply sfrmphiUnfoldType.
        unfold staticFootprint.
        rewrite flat_map_app.
        simpl.
        eca. intuition.
        apply (sfrmeIncl _ (flat_map staticFootprint' (unfoldTypeJudjFormula e0 T0 x0)) _).
          intuition.
        generalize e0. clear.
        induction e0; eca; simpl.
      ++  rewrite flat_map_app.
          simpl.
          intuition.
      ++  rewrite flat_map_app.
          eapp sfrmeIncl.
          intuition.
Qed.

Theorem hoareMiniEquals : forall p1 p2 s,
  wrapHoare hoareSinglePreMini p1 s p2 <->
  wrapHoare hoareSingle        p1 s p2.
Proof.
  unfold wrapHoare. split; intros; unf.
  - (*if old rule holds, then mini rule also holds*)
    rename H1 into sf.
    rename H0 into im1.
    rename H2 into im2.
    rename H4 into ho.
    inversionx ho.
    * repeat eexists.
      Focus 4. eca.
      + repeat eca.
      + unfold phiImplies. intros.
        apply im1 in H5.
        eca.
      ++  apply inclEmpty.
      ++  inversionx H3.
          apply H8 in H5.
          inversionx H5.
          assumption.
      ++  apply H0 in H5.
          simpl.
          rewrite AexceptEmpty.
          assumption.
      + assumption.
    * repeat eexists.
      Focus 4. eca.
      + repeat eca. simpl.
        rewriteRev sfrmphiApp.
        split; eauto.
        repeat eca.
      + unfold phiImplies. intros.
        apply im1 in H5.
        inversionx H2.
        inversionx H3.
        eca.
      ++  apply inclEmpty.
      ++  apply H8 in H5.
          inversionx H5.
          assumption.
      ++  simpl.
          rewrite AexceptEmpty.
          eca.
            apply inclEmpty.
            apply H7 in H5. inversionx H5. assumption.
          simpl.
          rewrite AexceptEmpty.
          rewrite app_comm_cons.
          apply evalphiSymm.
          simpl.
          eapp H0.
      + assumption.
    * assert (∃ T' : T, unfoldTypeJudjPremise e0 T0 T'
              ∧ phiImplies p1 (unfoldTypeJudjFormula e0 T0 T'))
      as co.
        apply unfoldTypeJudjLemma.
        split. eapp phiImpliesStaticType.
        exists phi'0.
        split; auto.
        eapp phiImpliesTrans.
      unf.
      repeat eexists.
      Focus 4. eca.
      + repeat eca. simpl.
        rewriteRev sfrmphiApp.
        split. eapp sfrmphiApp. apply sfrmphiUnfoldType.
        eapp sfrmIncl.
        apply inclEmpty.
      + repeat intro.
        eca.
          apply inclEmpty.
          apply im1 in H7. inversionx H4. apply H12 in H7. inversionx H7. assumption.
        common.
        apply evalphiAppRev. eapp H9.
        apply im1 in H7.
        apply H0 in H7.
        rewrite footprintUnfoldTypeJudjASfpx.
        eapp evalphiRemoveAexcept.
        admit.
      + repeat intro.
        apply im2.
        eapp evalphiSuffix.
    * repeat eexists.
      Focus 4. eca.
      + repeat eca.
      + unfold phiImplies. intros.
        apply im1 in H5.
        inversionx H3.
        inversionx H4.
        eca.
          apply inclEmpty.
          apply H8 in H5. inversionx H5. eassumption.
        eca.
          apply inclEmpty.
          apply H7 in H5. inversionx H5. eassumption.
        common.
        eapp H0.
      + assumption.
    * repeat eexists.
      Focus 4. eca.
      + repeat eca.
        simpl.
        rewriteRev sfrmphiApp.
        split; auto.
        repeat eca. simpl.
        apply IsMethodWellDef in H1.
        inversionx H1. unf.
        eapply sfrmphiPhiSubsts2 in H10.
        eapp sfrmIncl.
        apply inclEmpty.
      + repeat intro.
        apply im1 in H8.
        inversionx H0.
        inversionx H2.
        inversionx H3.
        eca.
          apply inclEmpty.
          apply H10 in H8. inversionx H8. assumption.
        eca.
          apply inclEmpty.
          apply H11 in H8. inversionx H8. assumption.
        eca.
          apply inclEmpty.
          apply H9 in H8. inversionx H8. assumption.
        common.
        eapp evalphiSymm.
      + eapp phiImpliesAppCommA.
    * repeat eex. eca.
    * repeat eexists.
      Focus 4. eca.
      Focus 3. eauto.
      Focus 2. repeat intro. apply im1 in H2. apply H0 in H2. eapp evalphiSymm.
      rewriteRev sfrmphiApp.
      split; auto.
      admit.
    * repeat eexists.
      Focus 4. eca.
      + assumption.
      + eapp phiImpliesTrans.
      + assumption.
  - (*if mini rule holds, then old rule also holds*)
    rename H1 into sf.
    rename H0 into im1.
    rename H2 into im2.
    rename H4 into ho.
    inversionx ho.
    * repeat eex.
      eca.
      + rewrite cons2app.
        eapp phiImpliesSuffix.
      + inversionx sf.
        assumption.
      + eca. rewrite cons2app.
        eapp phiImpliesPrefix.
    * repeat eex.
      eca.
      + unfold phiImplies.
        intros.
        rewrite cons2app2 in H1.
        apply evalphiSuffix in H1.
        rewrite app_comm_cons in H1.
        apply evalphiSymm in H1.
        assumption.
      + inversionx sf.
        inversionx H2.
        inversionx H4.
        simpl in *.
        apply sfrmphiApp in H5.
        tauto.
      + eca. rewrite cons2app.
        eapp phiImpliesPrefix.
      + eca.
        unfold phiImplies. intros.
        rewrite cons2app in H1.
        apply evalphiSuffix in H1.
        rewrite cons2app in H1.
        apply evalphiPrefix in H1.
        assumption.
    * (* assert (∃ T' : T, unfoldTypeJudjPremise e0 T0 T'
             ∧ phiImplies p1 (unfoldTypeJudjFormula e0 T0 T'))
      as conv.
        eex.
        repeat intro.
        apply im1 in H3.
        rewrite cons2app in H3.
        apply evalphiSuffix in H3.
        apply evalphiPrefix in H3.
        assumption. *)
      assert (∃ T0' : T, unfoldTypeJudjPremise e0 T0 T0'
             ∧ phiImplies (phiType x2 T0 :: unfoldTypeJudjFormula e0 T0 T' ++ phi'0) (unfoldTypeJudjFormula e0 T0 T0'))
      as conv.
        eex.
        repeat intro.
        rewrite cons2app in H3.
        apply evalphiSuffix in H3.
        apply evalphiPrefix in H3.
        assumption.
      
      apply unfoldTypeJudjLemma in conv. unf.
      
      repeat eex.   eapp phiImpliesTrans.
      rewrite app_assoc.
      eca.
      + admit.
      + inversionx sf.
        assumption.
      + rewrite FVApp.
        unfold NotIn, not in *.
        intros nin.
        apply in_app_iff in nin.
        contradict H1.
        inversionx nin; try tauto.
        generalize e0 H1. clear.
        induction e0; intros; simpl in *; try tauto.
        rewrite FVApp, in_app_iff in H1.
        simpl in *.
        rewrite app_nil_r in H1.
        intuition.
      + eca.
        admit.
      + admit.
      + admit.
    * repeat eex.
      eca.
      + unfold phiImplies.
        intros.
        inversionx H1.
        inversionx H12.
        common.
        assumption.
      + inversionx sf.
        inversionx H2.
        assumption.
      + eca. rewrite cons2app.
        eapp phiImpliesPrefix.
      + eca.
        unfold phiImplies. intros.
        rewrite cons2app in H1.
        apply evalphiSuffix in H1.
        rewrite cons2app in H1.
        apply evalphiPrefix in H1.
        assumption.
    * apply phiImpliesAppCommA in im2.
      repeat eex.
      eca.
      + eca.
        repeat intro.
        rewrite cons2app in H3.
        apply evalphiSuffix in H3.
        rewrite cons2app in H3.
        apply evalphiPrefix in H3.
        assumption.
      + eca.
        repeat intro.
        rewrite cons2app in H3.
        eapp evalphiPrefix.
      + eca.
        repeat intro.
        rewrite cons2app in H3.
        apply evalphiSuffix in H3.
        rewrite cons2app in H3.
        apply evalphiSuffix in H3.
        rewrite cons2app in H3.
        eapp evalphiPrefix.
      + unfold phiImplies.
        intros.
        inversionx H3.
        inversionx H14.
        inversionx H16.
        common.
        rewrite app_comm_cons.
        eapp evalphiSymm.
      + inversionx sf.
        inversionx H4.
        inversionx H6.
        eapp sfrmphiApp.
    * repeat eex. eca.
    * repeat eex.
      eca.
      + apply phiImpliesAppCommA.
        apply phiImpliesRefl.
      + apply sfrmphiApp in sf.
        tauto.
    * repeat eex. eca.
Admitted.

(* 
Definition dfrme H r (A : A_d) (e : e) := 
  evale' H r e <> None /\ incl (footprintXe H r e) A.

Lemma dfrmeVar : forall H1 H2 r A1 A2 x, 
  dfrme H1 r A1 (ex x) <->
  dfrme H2 r A2 (ex x).
Proof.
  intros.
  unfold dfrme, footprintXe. simpl.
  split; intros; unf;
  split; auto;
  apply inclEmpty.
Qed.

Lemma dfrmeEdot : forall H r A e f, 
  dfrme H r A (edot e f) ->
  (exists o, In (o, f) A /\ evale' H r e = Some (vo o)) /\
  dfrme H r A e.
Proof.
  unfold dfrme.
  intros. unf.
  unfold footprintXe in *.
  simpl in *.
  apply inclApp in H3. unf.
  unfold A'_s2A'_d, olist in H1.
  simpl in *.
  destruct (evale' H0 r e0); try tauto.
  destruct v0; try tauto.
  simpl in *.
  apply inclSingle in H1.
  
  split.
  - eex.
  - split; auto.
    discriminate.
Qed. *)