Load GradVer20Hook.
Import Semantics.

(* disjunciton of phi *)
Definition phid := list phi.

Definition evalphid H r A (pd : phid) :=
  exists p, In p pd /\ evalphi H r A p.

(* helping defs *)
Definition isIntersection (pd1 pd2 pdi : phid) :=
  forall H r A, evalphid H r A pd1 /\ evalphid H r A pd2 <-> evalphid H r A pdi.

Definition splitPhi (p : phi) : prod A_s phi :=
  fold_right
    (fun p pr => 
      match p with
      | phiAcc e f => ((e, f) :: fst pr, snd pr)
      | _ => (fst pr, p :: snd pr)
      end)
    ([], [])
    p.

Lemma splitPhiAlt : forall p,
  splitPhi p = 
    (staticFootprint p, 
     filter (fun p' => match p' with
                         | phiAcc _ _ => false
                         | _ => true
                         end) p).
Proof.
  induction p0; intros; simpl in *; try tauto.
  rewrite IHp0. simpl.
  destruct a; tauto.
Qed.


Definition mergePhi (pa : A_s) (pb : phi) : phi :=
  map (fun p => phiAcc (fst p) (snd p)) pa ++ pb.

(* meet operation *)
Fixpoint meetSplit (pa1 pa2 : A_s) (pb1 pb2 : phi) : phid :=
  match pa1 with
  | [] => [map (fun p => phiAcc (fst p) (snd p)) pa2 ++ pb1 ++ pb2]
  | A :: pa1 => 
    flat_map
    (fun p => (phiAcc (fst A) (snd A) :: p) :: 
              map 
                (fun A' => (phiEq (fst A) (fst A')) :: p) 
                (filter (fun A' => f_decb (snd A) (snd A')) pa2))
    (meetSplit pa1 pa2 pb1 pb2)
  end.

Definition meetSingle (p1 p2 : phi) : phid :=
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  meetSplit (fst ps1) (fst ps2) (snd ps1) (snd ps2).

Definition meet (pd1 pd2 : phid) : phid :=
  flat_map (fun ps => meetSingle (fst ps) (snd ps)) (list_prod pd1 pd2).

(*BEGIN test*)
Open Scope string.
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"] [].
Eval compute in meetSingle [] [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"].
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"] [phiAcc (ex (xUserDef "b")) "f"].
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"] [phiAcc (ex (xUserDef "b")) "g"].
Close Scope string.
(*END test*)

Lemma flat_map_app : forall {T U : Type} (f : T -> list U) l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros.
  rewrite flat_map_concat_map.
  rewrite map_app.
  rewrite concat_app.
  repeat rewriteRev flat_map_concat_map.
  tauto.
Qed.

Lemma evalphiSplitMerge : forall p,
  let ps := splitPhi p in
  forall H r A,
  evalphi H r A p ->
  evalphi H r A (map (λ p, phiAcc (fst p) (snd p)) (fst ps) ++ snd ps)
  .
Proof.
  induction p0; intros; simpl in *; try tauto.
  inversionx H1.
  apply IHp0 in H12.
  destruct a; subst ps; simpl in *;
  try (apply evalphiSymm;
      rewriteRev app_comm_cons;
      eca; simpl;
      apply evalphiSymm;
      assumption).
  eca.
Qed.

Lemma evalphiSplitMergeRev : forall p,
  let ps := splitPhi p in
  forall H r A,
  evalphi H r A (map (λ p, phiAcc (fst p) (snd p)) (fst ps) ++ snd ps) ->
  evalphi H r A p
  .
Proof.
  induction p0; intros; simpl in *; try tauto.
  subst ps.
  destruct a; simpl in *;
  try (apply evalphiSymm in H1;
      rewriteRevIn app_comm_cons H1;
      inversionx H1;
      eca;
      common;
      apply evalphiSymm in H12;
      eapp IHp0).
  inversionx H1.
  eca.
Qed.

Lemma meetSplitAugment1 : forall ps1a ps1b ps2a ps2b p' H r A,
   footprint' H r p' = [] ->
   evalphi' H r [] p' ->
   (∃ p0 : phi, In p0 (meetSplit ps1a ps2a ps1b ps2b) ∧ evalphi H r A p0) ->
   (∃ p0 : phi, In p0 (meetSplit ps1a ps2a (p' :: ps1b) ps2b) ∧ evalphi H r A p0).
Proof.
  induction ps1a; intros; unf; simpl in *.
  - eex.
    intuition. subst.
    apply evalphiSymm.
    rewriteRev app_comm_cons.
    eca; rewrite H1.
    * apply inclEmpty.
    * assumption.
    * apply evalphiSymm.
      common.
      assumption.
  - apply in_flat_map in H3. unf.
    inversionx H6.
    * inversionx H5.
      eappIn IHps1a H1.
      unf.
      exists (phiAcc (fst a) (snd a) :: x0).
      split.
      + apply in_flat_map.
        eex.
        apply in_eq.
      + eca.
    * apply in_map_iff in H4. unf. subst.
      inversionx H5. simpl in *. common.
      eappIn IHps1a H1. unf.
      exists (phiEq (fst a) (fst x2) :: x0).
      split.
      + apply in_flat_map.
        eex.
        apply in_cons.
        apply in_map_iff.
        eex.
      + eca.
        simpl.
        common.
        assumption.
Qed.

Lemma meetSplitAugment1Rev : forall ps1a ps1b ps2a ps2b p' H r A,
   footprint' H r p' = [] ->
   (∃ p0 : phi, In p0 (meetSplit ps1a ps2a (p' :: ps1b) ps2b) ∧ evalphi H r A p0) ->
   evalphi' H r [] p' /\
   (∃ p0 : phi, In p0 (meetSplit ps1a ps2a ps1b ps2b) ∧ evalphi H r A p0).
Proof.
  induction ps1a; intros; unf; simpl in *.
  - inversionx H2; try tauto.
    apply evalphiSymm in H4.
    rewriteRevIn app_comm_cons H4.
    inversionx H4.
    rewrite H1 in *.
    split; auto.
    common.
    apply evalphiSymm in H13.
    eex.
  - apply in_flat_map in H2. unf.
    inversionx H5.
    * inversionx H4.
      eappIn IHps1a H1; try apply H1.
      unf.
      exists (phiAcc (fst a) (snd a) :: x0).
      split.
      + apply in_flat_map.
        eex.
        apply in_eq.
      + eca.
    * apply in_map_iff in H3. unf. subst.
      inversionx H4. simpl in *. common.
      eappIn IHps1a H1; try apply H1. unf.
      exists (phiEq (fst a) (fst x2) :: x0).
      split.
      + apply in_flat_map.
        eex.
        apply in_cons.
        apply in_map_iff.
        eex.
      + eca.
        simpl.
        common.
        assumption.
Qed.

Lemma footprintApp : forall H r p1 p2,
  footprint H r (p1 ++ p2) = footprint H r p1 ++ footprint H r p2.
Proof.
  induction p1; intros; simpl in *; try tauto.
  rewrite IHp1.
  rewrite app_assoc.
  tauto.
Qed.

Lemma footprintMapAccStaticFootprint : forall H r p,
  footprint H r (map (λ p, phiAcc (fst p) (snd p)) (staticFootprint p)) =
  footprint H r p.
Proof.
  induction p0; intros; simpl in *; try tauto.
  rewriteRev IHp0.
  rewrite map_app.
  destruct a; tauto.
Qed.

Lemma meetFPnotContains' : forall H r p1a p2a p1b p2b p o f,
  footprint H r p1b = [] ->
  footprint H r p2b = [] ->
  In p (meetSplit (staticFootprint p1a) (staticFootprint p2a) p1b p2b) ->
  ¬ In (o, f) (footprint H r p1a) ->
  ¬ In (o, f) (footprint H r p2a) ->
  ¬ In (o, f) (footprint H r p).
Proof.
  induction p1a; intros; simpl in *.
  - intuition.
    subst.
    repeat rewrite footprintApp in H6.
    repeat rewrite in_app_iff in H6.
    rewrite H1, H2 in H6.
    intuition.
    rewrite footprintMapAccStaticFootprint in H3.
    tauto.
  - destruct a; simpl in *;
    try (eapp (IHp1a p2a p1b p2b p0); fail).
    rewrite in_app_iff in H4.
    apply not_or_and in H4. unf.
    apply in_flat_map in H3. unf.
    eappIn (IHp1a p2a p1b p2b x0) H3.
    unfold not. intro ff. contradict H3.
    inversionx H8.
    * unfold footprint in *.
      rewrite in_flat_map.
      rewrite in_flat_map in ff. unf.
      eex.
      inversionx H4; tauto.
    * apply in_map_iff in H3. unf. subst.
      unfold footprint in *.
      rewrite in_flat_map.
      rewrite in_flat_map in ff. unf.
      eex.
      inversionx H4; tauto.
Qed.

Lemma meetFPnotContains : forall H r p1 p2 p o f,
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  In p (meetSplit (fst ps1) (fst ps2) (snd ps1) (snd ps2)) ->
  ~ In (o, f) (footprint H r p1) ->
  ~ In (o, f) (footprint H r p2) ->
  ~ In (o, f) (footprint H r p).
Proof.
  intros.
  subst ps1 ps2.
  repeat rewrite splitPhiAlt in *. simpl in *.

  assert (forall p, footprint H0 r
          (filter
             (λ p' : phi',
              match p' with
              | phiTrue => true
              | phiEq _ _ => true
              | phiNeq _ _ => true
              | phiAcc _ _ => false
              | phiType _ _ => true
              end) p) = []).
    induction p3; simpl; try tauto.
    unfold footprint in *.
    destruct a; simpl; tauto.
  
  eapp meetFPnotContains'.
Qed.

Lemma meetFPnotContains'Rev : forall H r A p1a p2a p1b p2b p o f,
  evalphi H r A p ->
  In p (meetSplit (staticFootprint p1a) (staticFootprint p2a) p1b p2b) ->
  ¬ In (o, f) (footprint H r p) ->
  ¬ In (o, f) (footprint H r p1a) /\
  ¬ In (o, f) (footprint H r p2a).
Proof.
  induction p1a; intros; simpl in *.
  - intuition.
    subst.
    contradict H3.
    repeat rewrite footprintApp.
    repeat rewrite in_app_iff.
    constructor.
    rewrite footprintMapAccStaticFootprint.
    tauto.
  - destruct a; simpl in *;
    try (eapp (IHp1a p2a p1b p2b p0); fail).
    apply in_flat_map in H2. unf.
    apply not_or_and. unfold not. intros ii.
    eappIn (IHp1a p2a p1b p2b x0 o0 f0) H2.
    * unf.
      inversionx ii; try tauto.
      apply in_app_iff in H2.
      inversionx H2; try tauto.
      destruct (evale' H0 r e0) eqn: ee; try tauto.
      destruct v0; try tauto.
      apply InSingle in H7. inversionx H7.
      contradict H3.
      inversionx H5.
      + unfold footprint.
        rewrite in_flat_map.
        eex; try apply in_eq.
        simpl.
        rewrite ee.
        apply in_eq.
      + rewrite in_map_iff in H2. unf. subst.
        rewrite filter_In in H5. subst.
        destruct x1. simpl in *. unf.
        dec (string_dec f1 s0); try discriminate.
        contradict H6.
        inversionx H1. inversionx H14. common.
        rewrite ee in *. inversionx H7.
        apply staticVSdynamicFP.
        eex.
    * inversionx H5.
      + inversionx H1.
        eapp evalphiAexcept.
      + apply in_map_iff in H4. unf.
        subst.
        inversionx H1.
        eapp evalphiAexcept.
    * unfold not. intros ff. contradict H3.
      inversionx H5.
      + unfold footprint in *.
        apply in_flat_map.
        apply in_flat_map in ff.
        unf.
        eex.
        eapp in_cons.
      + apply in_map_iff in H3. unf.
        subst.
        unfold footprint in *.
        apply in_flat_map.
        apply in_flat_map in ff.
        unf.
        eex.
        eapp in_cons.
Qed.

Lemma meetFPnotContainsRev : forall H r A p1 p2 p o f,
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  evalphi H r A p ->
  In p (meetSplit (fst ps1) (fst ps2) (snd ps1) (snd ps2)) ->
  ~ In (o, f) (footprint H r p) ->
  ~ In (o, f) (footprint H r p1) /\
  ~ In (o, f) (footprint H r p2).
Proof.
  intros.
  subst ps1 ps2.
  repeat rewrite splitPhiAlt in *. simpl in *.

  assert (forall p, footprint H0 r
          (filter
             (λ p' : phi',
              match p' with
              | phiTrue => true
              | phiEq _ _ => true
              | phiNeq _ _ => true
              | phiAcc _ _ => false
              | phiType _ _ => true
              end) p) = []).
    induction p3; simpl; try tauto.
    unfold footprint in *.
    destruct a; simpl; tauto.
  
  eapp meetFPnotContains'Rev.
Qed.

Lemma meetSplitWorks : forall p1 p2,
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  forall H r A,
  (evalphi H r A p1 /\ evalphi H r A p2) ->
  (exists p, In p (meetSplit (fst ps1) (fst ps2) (snd ps1) (snd ps2)) /\
             evalphi H r A p).
Proof.
  induction p1; intros; simpl in *; unf.
  - eex.
    eapp evalphiSplitMerge.
  - inversionx H2.
    assert (evalphi H0 r A p1 ∧ evalphi H0 r A p2) as IH.
      apply evalphiAexcept in H13. auto.
    apply IHp1 in IH. invE IH p'.
    destruct a;
    try eapp meetSplitAugment1.
    subst ps1 ps2.
    unf.
    destruct (footprint' H0 r (phiAcc e0 f0)) eqn: fp.
    * exists (phiAcc e0 f0 :: p').
      split.
      + apply in_flat_map.
        eex.
        apply in_eq.
      + eca;
        rewrite fp;
        common; auto.
    * simpl in *.
      destruct (evale' H0 r e0) eqn: ee; inversionx fp.
      destruct v0; inversionx H5.
      destruct (classic (In (o0, f0) (footprint H0 r p2))).
      + apply staticVSdynamicFP in H4. invE H4 e'. unf.
        exists (phiEq e0 e' :: p').
        split.
        ++apply in_flat_map.
          eex.
          apply in_cons.
          apply in_map_iff.
          exists (e', f0). simpl. split; auto.
          apply filter_In.
          rewrite splitPhiAlt. simpl.
          split; auto.
          dec (string_dec f0 f0). tauto.
        ++eca; simpl.
        +++ apply inclEmpty.
        +++ eca.
        +++ common.
            assumption.
      + exists (phiAcc e0 f0 :: p').
        split.
        ++apply in_flat_map.
          eex.
          apply in_eq.
        ++eca; simpl; rewrite ee; try assumption.
          eapp evalphiRemoveAexcept.
          unfold disjoint. intros. apply or_comm. apply imply_to_or. intros. apply InSingle in H5. subst.
          apply evalphiImpliesAccess in H13.
          apply inclAexceptDisjoint in H13.
          specialize (H13 (o0, f0)). inversionx H13; try (contradict H5; apply in_eq).
          eapp meetFPnotContains.
Qed.

Lemma meetSplitWorksRev : forall p1 p2,
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  forall H r A,
  (exists p, In p (meetSplit (fst ps1) (fst ps2) (snd ps1) (snd ps2)) /\
             evalphi H r A p) ->
  (evalphi H r A p1 /\ evalphi H r A p2).
Proof.
  induction p1; intros; simpl in *; unf.
  - split; try constructor.
    intuition. subst.
    eapp evalphiSplitMergeRev.
  - destruct (classic (exists e f, a = phiAcc e f)).
    * invE H2 e0. invE H2 f0. subst.
      simpl in *.
      rewrite in_flat_map in H1. unf.
      assert (evalphi H0 r A p1 ∧ evalphi H0 r A p2) as ev.
        eapp IHp1. eex.
        inversionx H4.
          inversionx H3. eapp evalphiAexcept.
        apply in_map_iff in H2. unf. subst.
        inversionx H3. eapp evalphiAexcept.
      unf. split; auto.
      inversionx H4.
      + inversionx H3.
        eca.
        eapp evalphiRemoveAexcept.
        unfold disjoint. intros. apply or_comm. apply imply_to_or. intros.
        assert (¬ In x0 (footprint H0 r x1)).
          apply evalphiImpliesAccess in H15.
          apply inclAexceptDisjoint in H15.
          specialize (H15 x0).
          inversionx H15; try tauto.
        destruct x0.
        eappIn meetFPnotContainsRev H15.
        unf.
        assumption.
      + apply in_map_iff in H6. unf. subst.
        apply filter_In in H7. unf.
        destruct x2. simpl in *.
        dec (string_dec f0 s0); try discriminate.
        subst ps1 ps2. rewrite splitPhiAlt in *. simpl in *.
        inversionx H3. simpl in *.
        inversionx H16. common.
        assert (In (phiAcc e1 s0) p2).
          unfold staticFootprint in H4.
          apply in_flat_map in H4. unf.
          destruct x0; try tauto. simpl in *. intuition.
          inversionx H3. assumption.
        eappIn evalphiIn H3. inversionx H3. common.
        rewrite H16 in *. inversionx H14.
        assert (footprint' H0 r (phiAcc e0 s0) = [(o0, s0)]) as fp.
          simpl. rewrite H9. tauto.
        eca; rewrite fp.
        ++apply inclSingle.
          assumption.
        ++eca.
          apply in_eq.
        ++assert (In (o0, s0) (footprint H0 r p2)) as fp2.
            eapp staticVSdynamicFP.
          assert (In (o0, s0) (footprint H0 r x1)) as fpx.
            destruct (classic (In (o0, s0) (footprint H0 r x1))); try tauto.
            eappIn (meetFPnotContainsRev H0 r A p1 p2) H3. tauto.
            rewrite splitPhiAlt. simpl in *. assumption.
          
          Check meetFPnotContainsRev.
    (*cont*)
    * assert (footprint' H0 r a = []) as fp.
        destruct a; try tauto.
        contradict H2. eex.
      assert (fp' := fp).
      eapply meetSplitAugment1Rev in fp; eauto.
      + unf.
        lapply (IHp1 p2 H0 r A);
        try eex;
        try apply H6.
        unf.
        eca; rewrite fp';
        try apply inclEmpty;
        common;
        assumption.
      + destruct a; simpl in *; eex.
        contradict H2. eex.
Admitted.



Theorem meetWorks : forall pd1 pd2,
  isIntersection pd1 pd2 (meet pd1 pd2).
Proof.
  unfold isIntersection, meet, meetSingle, evalphid.
  induction pd1; simpl.
  - split; intros; unf; tauto.
  - split; intros; unf.
    * rewrite flat_map_app.
      inversionx H2.
      + assert (evalphi H0 r A x1 /\ evalphi H0 r A x0) as ss.
          auto.
        apply meetSplitWorks in ss. unf.
        exists x2.
        split; auto.
        rewrite in_app_iff. constructor.
        apply in_flat_map.
        exists (x1, x0).
        split; auto.
        rewrite in_map_iff. eex.
      + specialize (IHpd1 pd2 H0 r A).
        inversionx IHpd1.
        lapply H2; intros.
          unf. eex. intuition.
        split; eex.
    * rewrite flat_map_app in H1.
      rewrite in_app_iff in H1.
      inversionx H1.
      + apply in_flat_map in H2. unf.
        apply in_map_iff in H2. unf. subst.
        simpl in *.
        assert (evalphi H0 r A a /\ evalphi H0 r A x2).
          eapp meetSplitWorksRev.
        unf.
        split; eex.
      + specialize (IHpd1 pd2 H0 r A).
        inversionx IHpd1.
        lapply H4; intros.
          unf. eex.
        eex.
Qed.
