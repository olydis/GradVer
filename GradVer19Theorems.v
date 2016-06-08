Load GradVer18LemmaHI.
Import Semantics.

Lemma evalphiComposeDisjointFP : forall H r A1 A2 p1 p2,
    disjoint A1 A2 ->
    evalphi H r A1 p1 ->
    evalphi H r A2 p2 ->
    evalphi H r (A1 ++ A2) (p1 ++ p2).
Proof.
  intros.
  eapp evalphiAppRev.
  - eapp evalphiIncl.
    intuition.
  - eapp evalphiIncl.
    rewrite AexceptAppFirst.
    rewrite (AexceptDisjoint A2).
    * intuition.
    * apply evalphiImpliesAccess in H2.
      unfold disjoint, incl in *.
      intros.
      specialize (H1 x0).
      specialize (H2 x0).
      intuition.
Qed.

Definition goodFP H r p := 
  map Some (footprint' H r p) = 
  map (A'_s2A'_d H r) (staticFootprint' p).

Lemma evalphiImpliesGoodFP2 : forall H r A p,
  evalphi' H r A p ->
  goodFP H r p.
Proof.
  unfold goodFP.
  intros.
  inversionx H1; simpl in *; try tauto.
  unfold A'_s2A'_d. simpl.
  common. rewrite H3.
  tauto.
Qed.

Lemma evalphiImpliesGoodFP : forall H r A p,
  evalphi' H r A p ->
  (forall A', In A' (footprint' H r p) ->
              exists v, evalA'_d H A' = Some v).
Proof.
  intros.
  inversionx H1; simpl in *; try tauto.
  unfold evalA'_d. 
  common. rewrite H4 in *.
  apply InSingle in H2. subst.
  simpl.
  Check odotInPhi.
Qed.

Lemma dynSemStarNotModifies : forall x ss H1 H2 r1 r2 A1 A2,
  (∀ s', In s' ss → ¬ writesTo x s') ->
  dynSemStar
    (H1, [(r1, A1, ss)])
    (H2, [(r2, A2, [])]) ->
  r1 x = r2 x.
Proof.
  induction ss; intros; simpl in *.
  - inversionx H3; try tauto.
    inversionx H4.
  - inversionx H3.
    rename H4 into ds.
    rename H5 into dss.
    assert (¬ writesTo x0 a) as wt1. apply H0. tauto.
    assert (∀ s' : s, In s' ss → ¬ writesTo x0 s') as wt2. intros. apply H0. tauto.
    inversionx ds; simpl in wt1.
    * apply IHss in dss; auto.
    * apply IHss in dss; auto.
      unfold rhoSubst in dss.
      dec (x_dec x0 x1); try tauto.
      contradict wt1.
      constructor.
    * apply IHss in dss; auto.
      unfold rhoSubst in dss.
      dec (x_dec x0 x1); try tauto.
      contradict wt1.
      constructor.
    * apply IHss in dss; auto.
      unfold rhoSubst in dss.
      dec (x_dec x0 xresult); try tauto.
      contradict wt1.
      constructor.
    * admit.
    * apply IHss in dss; auto.
    * apply IHss in dss; auto.
    * apply IHss in dss; auto.
      unfold rhoSubst in dss.
      dec (x_dec x0 x1); try tauto.
      contradict wt1.
      constructor.
Admitted.



Lemma dynSemStarNotModifiesH : forall ss H1 H2 r1 r2 A1 A2 A v,
  ~ In A A1 ->
  dynSemStar
    (H1, [(r1, A1, ss)])
    (H2, [(r2, A2, [])]) ->
  evalA'_d H1 A = Some v ->
  evalA'_d H2 A = Some v.
Proof.
  induction ss; intros; simpl in *.
  - inversionx H3; try tauto.
    inversionx H5.
  - inversionx H3.
    rename H5 into ds.
    rename H6 into dss.
    inversionx ds.
    * eapply IHss in dss; eauto.
      destruct A. unfold evalA'_d in *. simpl in *.
      unfold HSubst.
      dec (o_dec o1 o0); try tauto.
      destruct (H1 o0); try discriminate.
      destruct p0. simpl in *.
      dec (string_dec f1 f0); try tauto.
    * eapply IHss in dss; eauto.
    * eapply IHss in dss; eauto.
      + unfold not. intros.
        apply in_app_iff in H3.
        intuition.
        apply in_map_iff in H5.
        unf. subst.
        unfold evalA'_d, HeapNotSetAt in *.
        simpl in *.
        rewrite H12 in *.
        discriminate.
      + unfold Halloc.
        rewrite H13.
        destruct A. unfold evalA'_d in *. simpl in *.
        dec (o_dec o0 o1); try tauto.
        unfold HeapNotSetAt in H12. rewrite H12 in *.
        discriminate.
    * eapply IHss in dss; eauto.
    * admit.
    * eapply IHss in dss; eauto.
    * eapply IHss in dss; eauto.
      unfold not in *. intros. contradict H0.
      apply InAexcept in H3.
      assumption.
    * eapply IHss in dss; eauto.
Admitted.


