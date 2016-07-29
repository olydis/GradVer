Load GradVer18LemmaHI.
Import Semantics.

Lemma dynSemStarNotModifiesHx : forall ss H1 H2 r1 r2 A1 A2 A,
  ~ In A A1 ->
  H1 (fst A) <> None ->
  dynSemStar
    (H1, [(r1, A1, ss)])
    (H2, [(r2, A2, [])]) ->
  evalA'_d H1 A = evalA'_d H2 A.
Proof.
  induction ss; intros; simpl in *.
  - inversionx H4; try tauto.
    inversionx H5.
  - inversionx H4.
    rename H5 into ds.
    rename H6 into dss.
    destruct A.
    inversionx ds.
    * eapply IHss in dss; eauto.
      + unfold evalA'_d in *. simpl in *.
        unfold HSubst in dss.
        dec (o_dec o0 o1); try tauto.
        destruct (H1 o1); try tauto.
        destruct p0. simpl in *.
        destruct o2; cut.
        dec (string_dec f0 f1); cut.
      + unfold HSubst. simpl in *.
        dec (o_dec o0 o1); try tauto.
        destruct (H1 o1); try tauto.
        destruct p0.
        discriminate.
    * eapply IHss in dss; eauto.
    * eapply IHss in dss; eauto.
      + rewriteRev dss. clear dss.
        unfold evalA'_d in *. simpl in *.
        unfold Halloc.
        rewrite H13.
        dec (o_dec o1 o0); tauto.
      + simpl in *. unfold not in *.
        intros. contradict H0.
        apply in_app_iff in H4.
        intuition.
        apply in_map_iff in H0. unf. inversionx H0.
        tauto.
      + unfold Halloc.
        rewrite H13. simpl in *.
        dec (o_dec o1 o0); tauto.
    * eapply IHss in dss; eauto.
    * admit.
    * eapply IHss in dss; eauto.
    * eapply IHss in dss; eauto.
      unfold not in *. intros. contradict H0.
      apply InAexcept in H4.
      assumption.
    * eapply IHss in dss; eauto.
Admitted.

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

Lemma evalphiComposeDisjointFPx : forall H r A p1 p2,
    disjoint (footprint H r p1) (footprint H r p2) ->
    evalphi H r A p1 ->
    evalphi H r A p2 ->
    evalphi H r A (p1 ++ p2).
Proof.
  intros.
  eapp evalphiAppRev.
  assert (incl (footprint H0 r p2) A).
    eapp evalphiImpliesAccess.
  eappIn evalphiNarrowAccess H3.
  eapp evalphiIncl.
  unfold incl, disjoint in *.
  intro AA.
  specialize (H1 AA).
  specialize (H4 AA).
  intuition.
  eapp InAexceptConstr.
Qed.

Lemma dynSemStarNoAccessInventing : forall ss H1 H2 r1 r2 A1 A2 A,
  dynSemStar
    (H1, [(r1, A1, ss)])
    (H2, [(r2, A2, [])]) ->
  In A A2 ->
  In A A1 \/ H1 (fst A) = None.
Proof.
  induction ss; intros; simpl in *.
  - inversionx H0; try tauto.
    inversionx H4.
  - inversionx H0.
    rename H4 into ds.
    rename H5 into dss.
    inversionx ds.
    * eapply IHss in dss; eauto.
      intuition.
      unfold HSubst in H0. destruct A. simpl in *.
      dec (o_dec o1 o0); try auto.
      destruct (H1 o0); try auto.
      destruct p0.
      discriminate.
    * eapply IHss in dss; eauto.
    * eapply IHss in dss; eauto.
      destruct A. simpl in *.
      inversionx dss.
      + apply in_app_iff in H0.
        intuition.
        apply in_map_iff in H4.
        unf. inversionx H4.
        auto.
      + unfold Halloc in H0.
        rewrite H12 in *.
        dec (o_dec o0 o1); tauto.
    * eapply IHss in dss; eauto.
    * admit.
    * eapply IHss in dss; eauto.
    * eapply IHss in dss; eauto.
      intuition.
      apply InAexcept in H0.
      auto.
    * eapply IHss in dss; eauto.
Admitted.

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
      rewrite H4.
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

Lemma footprintChangeHeap : forall H1 H2 r p,
  (forall A', In A' (staticFootprintX p) ->
    evalA'_s H1 r A' = evalA'_s H2 r A') ->
  footprint H1 r p = footprint H2 r p.
Proof.
  induction p0; intros; simpl in *; try tauto.
  erewrite IHp0, footprint'ChangeHeap; eauto;
  intuition.
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
  simpl in *.
  - eca.
  - eca;
    unfold evale in *;
    rewriteRev (evale'ChangeHeap H1 H2); eauto; intros; eapp H3; intuition.
  - eca;
    unfold evale in *;
    rewriteRev (evale'ChangeHeap H1 H2); eauto; intros; eapp H3; intuition.
  - assert (evale' H2 r e0 = Some (vo o0)) as ee.
      rewriteRev (evale'ChangeHeap H1 H2); eauto; intros; eapp H3; intuition.
    unfold evale in *.
    simpl in *.
    rewrite H6 in *.
    destruct H1 eqn: eeH1; cut.
    destruct p0.
    eapply HeapGetsMoreSpecific in eeH1; eauto.
    unf.
    eca.
    unfold evale. simpl. rewrite ee.
    rewrite H4.
    simpl.
(*     HeapFieldsGetMoreSpecific. *)
    admit.
Admitted.

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

Lemma footprintChangeRho : forall r1 r2 H p,
  (forall x, In x (FV p) -> r1 x = r2 x) ->
  footprint H r1 p = footprint H r2 p.
Proof.
  induction p0; intros; simpl in *; try tauto.
  erewrite IHp0, footprint'ChangeRho; eauto;
  intuition.
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
    unfold evale in *. simpl in *.
    rewrite H4 in H5.
    eca; unfold evale in *;
    erewrite evale'ChangeRho in H4; eauto;
    intros; intuition.
    simpl. rewrite H4.
    eauto.
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


Lemma evale'RemoveHSubst : forall o f v H r e,
  ~ In (o, f) (footprintXe H r e) ->
  evale' H r e = evale' (HSubst o f v H) r e.
Proof.
  induction e0; intros; simpl in *; try tauto.
  unfold footprintXe in *. simpl in *.
  rewrite in_app_iff in H1.
  apply not_or_and in H1. unf.
  rewriteRev IHe0; auto.
  unfold A'_s2A'_d in *. simpl in *.
  destruct (evale' H0 r e0); try tauto.
  destruct v1; try tauto.
  simpl in *.
  unfold HSubst.
  dec (o_dec o1 o0); cut.
  destruct (H0 o0); cut. destruct p0. simpl.
  destruct o2; cut.
  dec (string_dec f1 f0); cut.
  contradict H2.
  auto.
Qed.

Lemma footprint'RemoveHSubst : forall o f v H r p,
  ~ In (o, f) (footprintX' H r p) ->
  footprint' H r p = footprint' (HSubst o f v H) r p.
Proof.
  intros.
  destruct p0; try tauto.
  unfold footprintX' in *.
  simpl in *.
  eappIn evale'RemoveHSubst H1.
  rewriteRev H1.
  tauto.
Qed.

Lemma evalphi'RemoveHSubst : forall o f v H r p A,
  ~ In (o, f) (footprintX' H r p) ->
  evalphi' H r A p <->
  evalphi' (HSubst o f v H) r A p.
Proof.
  intros.
  unfold footprintX' in H1.
  destruct p0; simpl in *;
  try rewrite map_app in H1;
  try rewrite oflattenApp in H1;
  try rewrite in_app_iff in H1;
  try apply not_or_and in H1;
  unf.
  - split; constructor.
  - split; intros;
    inversionx H1; eca; unfold evale in *;
    try rewriteRev evale'RemoveHSubst; eauto;
    try erewrite evale'RemoveHSubst; eauto.
  - split; intros;
    inversionx H1; eca; unfold evale in *;
    try rewriteRev evale'RemoveHSubst; eauto;
    try erewrite evale'RemoveHSubst; eauto.
  - split; intros; inv H2; unfold evale in *;
    simpl in *; rewrite H6 in *.
    * erewrite evale'RemoveHSubst in H6; eauto.
      eca.
      unfold evale. simpl.
      rewrite H6.
      instantiate (1 := if o_decb o1 o0 && f_decb f1 f0 then v0 else v1).
      unfold HSubst.
      dec (o_dec o1 o0); eauto.
      destruct H0; cut.
      destruct p0.
      simpl in *.
      rewrite H10.
      auto.
    * rewriteRevIn evale'RemoveHSubst H6; eauto.
      unfold HSubst in *.
      dec (o_dec o1 o0).
        Focus 2. eca. unfold evale. simpl. rewrite H6. eauto.
      destruct H0 eqn: eeH0; cut.
      destruct p0.
      simpl in *.
      destruct o2 eqn: eeo2; cut.
      eca.
      unfold evale. simpl. rewrite H6.
      rewrite eeH0.
      simpl.
      eauto.
Qed.

Lemma evalphiRemoveHSubst : forall o f v H r p A,
  ~ In (o, f) (footprintX H r p) ->
  evalphi H r A p <->
  evalphi (HSubst o f v H) r A p.
Proof.
  induction p0; intros; simpl in *; split; try constructor; intros.
  - inversionx H2.
    unfold footprintX in H1.
    simpl in H1.
    rewrite map_app in H1.
    rewrite oflattenApp in H1.
    rewrite in_app_iff in H1.
    apply not_or_and in H1.
    eca.
    * rewriteRev footprint'RemoveHSubst; eauto; try apply H1.
    * rewriteRev footprint'RemoveHSubst; eauto; try apply H1.
      rewriteRev evalphi'RemoveHSubst; try apply H1.
      eauto.
    * rewriteRev footprint'RemoveHSubst; eauto; try apply H1.
      eapp IHp0.
      tauto.
  - inversionx H2.
    unfold footprintX in H1.
    simpl in H1.
    rewrite map_app in H1.
    rewrite oflattenApp in H1.
    rewrite in_app_iff in H1.
    apply not_or_and in H1.
    eca.
    * erewrite footprint'RemoveHSubst; eauto; try apply H1.
    * erewrite footprint'RemoveHSubst; eauto; try apply H1.
      erewrite evalphi'RemoveHSubst; try apply H1.
      eauto.
    * erewrite footprint'RemoveHSubst; eauto; try apply H1.
      eapp IHp0.
      tauto.
Qed.


Theorem framedOff : forall ss H1 H2 r1 r2 A1 A2 r A p,
  dynSemStar (H1, [(r1, A1, ss)]) (H2, [(r2, A2, [])]) ->
  (forall A', In A' A -> exists v, H1 (fst A') = Some v) ->
  disjoint A A1 ->
  sfrmphi [] p ->
  evalphi H1 r A p ->
  evalphi H2 r (A ++ A2) p.
Proof.
  induction ss; intros; simpl in *.
  - inversionx H0; try inversionx H7.
    eapp evalphiIncl.
    intuition.
  - inversionx H0.
    inversionx H7.
    * eappIn IHss H8.
        intros.
        apply H3 in H0. unf.
        destruct A'. simpl in *.
        unfold HSubst.
        dec (o_dec o1 o0); try (eex; fail).
        rewrite H7. destruct x1. eex.
      apply evalphiRemoveHSubst; auto.
      specialize (H4 (o0, f0)).
      intuition.
      eapply sfrmphiVSdfpX in H5. apply H5 in H0.
      apply evalphiImpliesAccess in H6. apply H6 in H0.
      tauto.
    * eappIn IHss H8.
    * assert (evalphi (Halloc o0 C0 H1) r A p0).
        eapp evalphiRemoveHalloc.
      eappIn IHss H8.
        intros.
        apply H3 in H7. unf.
        destruct A'. simpl in *.
        unfold Halloc.
        rewrite H17.
        dec (o_dec o0 o1); eex.
      assert (disjoint A (map (λ cf' : T * f, (o0, snd cf')) Tfs)).
        unfold disjoint. intros.
        apply imply_to_or. intro.
        unfold not. intro.
        apply in_map_iff in H9. unf. subst.
        apply H3 in H7. unf. simpl in *.
        rewrite H16 in H9. discriminate.
      unfold disjoint. intros.
      specialize (H4 x1).
      specialize (H7 x1).
      rewrite in_app_iff. intuition.
    * eappIn IHss H8.
    * admit.
    * eappIn IHss H8.
    * eappIn IHss H8.
      unfold disjoint. intros.
      specialize (H4 x0).
      intuition.
      apply or_intror.
      intro. contradict H0.
      eapp InAexcept.
    * eappIn IHss H8.
Admitted.

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
    * eapply IHss in H5; eauto.
      + rewriteRev H5. clear H5.
        
      rewrite H0.
      eauto.
      destruct A. simpl in *.
      destruct (evale' H1 r1 e0) eqn: ee.
      
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