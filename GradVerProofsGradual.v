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
      + 




(*cont*)

      + specialize (IHpd1 pd2 H0 r A).
        inversionx IHpd1.
        lapply H2; intros.
          unf. eex. intuition.
        split; eex.
    * rewrite flat_map_app in H1.
      rewrite in_app_iff in H1.
      inversionx H1.
      + admit.
      + specialize (IHpd1 pd2 H0 r A).
        inversionx IHpd1.
        lapply H4; intros.
          unf. eex.
        eex.
Admitted.


Lemma phiMeetEmpty : forall a, In a (phiMeet a []).
Proof.
  induction a; simpl; try tauto.
  destruct a; try (apply in_map; assumption).
  apply in_flat_map.
  exists a0.
  intuition.
  unfold phiEnsureAccess.
  constructor.
  tauto.
Qed.

Lemma evalphiFalse : forall a H r A x f, In (phiAcc x f) a -> ~ evalphi H r A (phiAcc x f :: a).
Proof.
  induction a; intros; inversionx H1; intuition.
  - inversionx H1.
    inversionx H12.
    inversionx H11.
    inversionx H9.
    unfold footprint' in *.
    rewrite H1 in *; clear H1.
    apply H5 in H10.
    unfold Aexcept, except in H10.
    apply filter_In in H10.
    inversionx H10.
    contradict H2.
    apply not_true_iff_false.
    apply negb_false_iff.
    simpl.
    unfold A_d'_decb, o_decb, string_decb, dec2decb.
    destruct (o_dec (fst (o0, f0)) (fst (o0, f0))); try (contradict n; tauto).
    destruct (string_dec (snd (o0, f0)) (snd (o0, f0))); try (contradict n; tauto).
    auto.
  - specialize (IHa H0 r A x0 f0).
    apply IHa; try assumption. clear IHa.
    inversionx H1.
    econstructor; eauto.
    inversionx H13.
    apply evalphiAexcept in H15.
    assumption.
Qed.

Lemma evalphi'incl : forall A A' H r p, incl A' A -> evalphi' H r A' p -> evalphi' H r A p.
Proof.
  intros.
  inversionx H2;
  econstructor; eauto.
Qed.

Lemma evalphiIn : forall b b' H r A, In b' b -> evalphi H r A b -> evalphi' H r A b'.
Proof.
  induction b; intros.
  - inversion H1.
  - inversionx H1.
    * inversionx H2.
      eapply evalphi'incl; eauto.
    * inversionx H2.
      eapply IHb in H13; eauto.
      apply evalphi'Aexcept in H13.
      assumption.
Qed.
