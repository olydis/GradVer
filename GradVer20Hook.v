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

(* Lemma unfoldTypeJudjLemma : forall p e T,
  (hasStaticType p e T /\ sfrme (staticFootprint p) e)
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
      + eca.
  - split; intros; simpl in *; unf.
    * eex.
      inversionx H1.
      assumption.
    * subst.
      split; eca.
  - split; intros; simpl in *; unf.
    * inversionx H1.
      inversionx H2.
      assert (hasStaticType p0 e0 (TClass C0) ∧ sfrme (staticFootprint p0) e0)
        as IH. auto.
      apply IHe0 in IH. unf.
      eex.
      repeat intro.
      apply evalphiAppRev.
      + apply H2 in H0.
        erewrite unfoldTypeJudjFormulaTirrel.
        eauto.
      + admit.
Admitted. *)

Theorem hoareMiniEquals : forall p1 p2 s,
  wrapHoare hoareSinglePreMini p1 s p2 <->
  wrapHoare hoareSingle        p1 s p2.
Proof.
  unfold wrapHoare. split; intros; unf.
  - rename H1 into sf.
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
    * admit.
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
    * admit.
    * repeat eex. eca.
    * admit.
    * repeat eexists.
      Focus 4. eca.
      + assumption.
      + eapp phiImpliesTrans.
      + assumption.
  - rename H1 into sf.
    rename H0 into im1.
    rename H2 into im2.
    rename H4 into ho.
    inversionx ho.
    * repeat eex.
      eca.
      + rewrite cons2app.
        eapp phiImpliesSuffix.
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
    * admit.
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
    * admit.
    * repeat eex. eca.
    * admit.
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