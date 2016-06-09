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
(* 
Lemma dynSemStarNotModifiesHX' : forall ss H1 H2 r1 r2 r A1 A2 A p,
  disjoint (footprint H1 r1 p) A1 ->
  dynSemStar
    (H1, [(r1, A1, ss)])
    (H2, [(r2, A2, [])]) ->
  sfrmphi [] p ->
  evalphi' H1 r A p ->
  evalphi' H2 r A p.
Proof.
   *)

Lemma evale'ChangeHeap : forall H1 H2 r e,
  (forall A', In A' (staticFootprintXe e) ->
    evalA'_s H1 r A' = evalA'_s H2 r A') ->
  evale' H1 r e = evale' H2 r e.
Proof.
  induction e0; intros; unfold evale in *; simpl in *; try tauto.
  assert (evalA'_s H1 r (e0, f0) = evalA'_s H2 r (e0, f0))
  as tracker.
    eapp H0.
  unfold evalA'_s, evalA'_d, A'_s2A'_d in tracker.
  simpl in *.
  destruct (evale' H1 r e0);
  try destruct v0;
  destruct (evale' H2 r e0);
  try destruct v0;
  try discriminate;
  try tauto;
  destruct v1;
  try tauto.
Qed.

Lemma footprint'ChangeHeap : forall H1 H2 r p,
  (forall A', In A' (staticFootprintX' p) ->
    evalA'_s H1 r A' = evalA'_s H2 r A') ->
  footprint' H1 r p = footprint' H2 r p.
Proof.
  intros.
  destruct p0; try tauto.
  simpl in *.
  erewrite evale'ChangeHeap; eauto.
Qed.

Lemma evalphi'ChangeHeap : forall H1 H2 S1 S2 r A p,
  dynSemStar (H1, S1) (H2, S2) ->
  (forall A', In A' (staticFootprintX' p) ->
    evalA'_s H1 r A' = evalA'_s H2 r A') ->
  evalphi' H1 r A p ->
  evalphi' H2 r A p.
Proof.
  intros;
  inversionx H4;
  simpl in *;
  eca;
  try rewrite in_app_iff in H3;
  unfold evale in *;
  try (rewriteRev (evale'ChangeHeap H1 H2); eauto; intros; eapp H3; intuition).
  
  inversionx H7; try constructor.
  eappIn HeapGetsMoreSpecific H5.
  unf.
  eca.
Qed.

Lemma evalphiChangeHeap : forall H1 H2 S1 S2 r p A,
  dynSemStar (H1, S1) (H2, S2) ->
  (forall A', In A' (staticFootprintX p) ->
    evalA'_s H1 r A' = evalA'_s H2 r A') ->
  evalphi H1 r A p ->
  evalphi H2 r A p.
Proof.
  induction p0; intros; simpl in *; try constructor.
  inversionx H4.
  rewrite (footprint'ChangeHeap H1 H2) in *; intuition.
  eappIn IHp0 H15; intuition.
  eappIn (evalphi'ChangeHeap H1 H2) H14; intuition.
  eca.
Qed.

(* 
Lemma dynSemStarSustainsHelper : forall ss H1 H2 r1 r2 A1 A2 r A,
  ~ In (A'_s2A'_d H1 r1 A) (map Some A1) ->
  dynSemStar
    (H1, [(r1, A1, ss)])
    (H2, [(r2, A2, [])]) ->
  evalA'_s H1 r A = evalA'_s H2 r A.
Proof.
  unfold evalA'_s, A'_s2A'_d.
  induction ss; intros; simpl in *.
  - inversionx H3; try tauto.
    inversionx H4.
  - inversionx H3.
    inversionx H4.
    * 
  intros.
  
  Check dynSemStarNotModifiesH.
  eapp (evalphiChangeHeap H1 H2).
  






Lemma dynSemStarSustains : forall ss H1 H2 r1 r2 A1 A2 r p A,
  disjoint A A1 ->
  dynSemStar
    (H1, [(r1, A1, ss)])
    (H2, [(r2, A2, [])]) ->
  evalphi H1 r A p ->
  evalphi H2 r A p.
Proof.
  intros.
  eapp (evalphiChangeHeap H1 H2).
  


 *)