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

(* mapRem *)
Definition isCutAt {T : Type} xs ys1 (y : T) ys2 : Prop := xs = ys1 ++ y :: ys2.

Lemma isCutAtClassic : forall {T : Type} xs ys1 (y : T) ys2,
  isCutAt xs ys1 y ys2 ->
  In y xs /\ incl ys1 xs /\ incl ys2 xs.

Fixpoint mapRem {T U : Type} (f : T -> list T -> U) (xs : list T) :=
  match xs with
  | [] => []
  | x :: xs => f x xs :: mapRem (fun y ys => f y (x :: ys)) xs
  end.

Lemma in_mapRem_iff : forall {T U : Type} y xs (f : T -> list T -> U),
  In y (mapRem f xs) <->
  exists xs1 x xs2, f x (xs1 ++ xs2) = y /\ isCutAt xs xs1 x xs2.
Proof.
  induction xs; intros; simpl in *.
  - split; intros; try tauto.
    unf. inversionx H2.
    destruct x0; discriminate.
  - split; intros.
    * inversionx H0.
      + exists []. exists a. exists xs.
        unfold isCutAt.
        split; tauto.
      + apply IHxs in H1. unf. subst.
        unfold isCutAt in H2. subst.
        exists (a :: x0). exists x1. exists x2.
        unfold isCutAt.
        split; tauto.
    * unf. subst.
      inversionx H2.
      destruct x0; simpl in *.
      + inversionx H1.
        auto.
      + inversionx H1.
        apply or_intror.
        apply IHxs.
        repeat eex.
Qed.

Fixpoint cSuffixes {T : Type} (l : list T) : list (list T) :=
  match l with
  | [] => []
  | x :: xs => (x :: xs) :: (cSuffixes xs)
  end.

Fixpoint cPrefixes {T : Type} (l : list T) : list (list T) :=
  match l with
  | [] => []
  | x :: xs => [] :: map (fun y => x :: y) (cPrefixes xs)
  end.

Definition cycles {T : Type} (l : list T) : list (list T) :=
  map (fun x => fst x ++ snd x) (combine (cSuffixes l) (cPrefixes l)).

Fixpoint isPermutation {T : Type} (a : list T) (b : list T) : Prop :=
  match a with
  | [] => a = b
  | x :: xs => exists ys, In (x :: ys) (cycles b) /\ isPermutation xs ys
  end.

Eval compute in cPrefixes [1 ; 2 ; 3 ; 4 ; 5].
Eval compute in cSuffixes [1 ; 2 ; 3 ; 4 ; 5].
Eval compute in cycles [1 ; 2 ; 3 ; 4 ; 5].
Eval compute in cycles [].

Lemma permutEvalphi : forall H r A p1 p2,
  isPermutation p1 p2 ->
  (evalphi H r A p1 <-> evalphi H r A p2).
Proof.
  auto.
Admitted.

(* meet operation *)
Fixpoint meetSplit (pa1 pa2 : A_s) (pb : phi) : phid :=
  match pa1 with
  | [] => [map (fun p => phiAcc (fst p) (snd p)) pa2 ++ pb]
  | A :: pa1 =>
    map (fun p => phiAcc (fst A) (snd A) :: p)
    (
      meetSplit pa1 pa2 pb
      ++
      concat
      (
        mapRem
        (fun A' pa2 =>
          if f_decb (snd A) (snd A')
          then map (fun p => phiEq (fst A) (fst A') :: p) (meetSplit pa1 pa2 pb)
          else []
        )
        pa2
      )
    )
  end.

(* Lemma permutMeetSplit2a : forall pa1 pa2 pa2' pb1 pb2 H r A,
  isPermutation pa2 pa2' ->
  (evalphid H r A (meetSplit pa1 pa2  pb1 pb2) <->
   evalphid H r A (meetSplit pa1 pa2' pb1 pb2)).
Proof.
  auto.
Admitted. *)

Definition meetSingle (p1 p2 : phi) : phid :=
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  meetSplit (fst ps1) (fst ps2) (snd ps1 ++ snd ps2).

Definition meet (pd1 pd2 : phid) : phid :=
  flat_map (fun ps => meetSingle (fst ps) (snd ps)) (list_prod pd1 pd2).

(*BEGIN test*)
Open Scope string.
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"] [].
Eval compute in meetSingle [] [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"].
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"] [phiAcc (ex (xUserDef "b")) "f"].
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"] [phiAcc (ex (xUserDef "b")) "g"].
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"] [phiAcc (ex (xUserDef "c")) "f"].
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"]
                           [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"].
Close Scope string.
(*END test*)

Lemma evalphiSplitMerge : forall p,
  let ps := splitPhi p in
  forall H r A,
  evalphi H r A p <->
  evalphi H r A (map (λ p, phiAcc (fst p) (snd p)) (fst ps) ++ snd ps)
  .
Proof.
  induction p0; intros; simpl in *; try tauto.
  subst ps.
  split; intros.
  - inversionx H1.
    apply IHp0 in H12.
    destruct a; simpl in *;
    try (apply evalphiSymm;
        rewriteRev app_comm_cons;
        eca; simpl;
        apply evalphiSymm;
        assumption).
    eca.
  - destruct a; simpl in *;
    try (apply evalphiSymm in H1;
        rewriteRevIn app_comm_cons H1;
        inversionx H1;
        eca;
        common;
        apply evalphiSymm in H12;
        eapp IHp0).
    inversionx H1.
    eca.
    eapp IHp0.
Qed.

Lemma evalphidApp : forall H r A p1 p2,
  evalphid H r A (p1 ++ p2) <->
  evalphid H r A p1 \/ evalphid H r A p2.
Proof.
  unfold evalphid. intros.
  split; intros; unf.
  - apply in_app_iff in H1.
    inversionx H1.
    * apply or_introl. eex.
    * apply or_intror. eex.
  - inversionx H1; unf; eex; intuition.
Qed.

Lemma mapConcat : forall {T U : Type} (f : T -> U) xs,
  map f (concat xs) = flat_map (map f) xs.
Proof.
  intros.
  rewrite flat_map_concat_map.
  rewrite concat_map.
  tauto.
Qed.

Lemma meetSplitAugment1 : forall ps1 ps2 ps p H r A,
  let mc := map (cons (phiAcc (fst p) (snd p))) in
    (evalphid H r A (mc (meetSplit ps1 ps2 ps)) \/
     exists xs1 x xs2, 
      isCutAt ps2 xs1 x xs2 /\ snd p = snd x /\
      evalphid H r A (mc (map (cons (phiEq (fst p) (fst x))) (meetSplit ps1 (xs1 ++ xs2) ps))))
    <->
    (evalphid H r A (meetSplit (p :: ps1) ps2 ps))
   .
Proof.
  split; simpl in *; unfold evalphid in *; intuition; unf; intuition.
  - apply in_map_iff in H2. unf. subst.
    eex.
    apply in_map_iff. eex.
    intuition.
  - apply in_map_iff in H4. unf. subst.
    destruct p0, x1. simpl in *. subst.
    eex.
    apply in_map_iff. eex.
    apply in_app_iff. apply or_intror.
    apply in_concat. eex.
    apply in_mapRem_iff. repeat eex.
    simpl.
    dec (string_dec f1 f1).
    tauto.
  - apply in_map_iff in H1. unf. subst.
    apply in_app_iff in H4.
    inversionx H4.
    * constructor. eex.
      apply in_map_iff. eex.
    * apply in_concat in H1. unf.
      apply in_mapRem_iff in H1. unf. subst.
      destruct p0, x3. simpl in *.
      dec (string_dec f0 s0); try tauto.
      apply in_map_iff in H4. unf. subst.
      apply or_intror. repeat eex.
      apply in_map_iff. eex.
      apply in_map_iff. eex.
Qed.

Lemma meetSplitSymm : forall ps1 ps2 ps H r A,
  evalphid H r A (meetSplit ps1 ps2 ps) ->
  evalphid H r A (meetSplit ps2 ps1 ps).
Proof.
  admit.
Admitted.

Lemma meetSplitAugment : forall ps1 ps2 ps p' H r A,
   footprint' H r p' = [] ->
   (
    (evalphid H r A (meetSplit ps1 ps2 ps) /\ evalphi' H r [] p')
    <->
    (evalphid H r A (meetSplit ps1 ps2 (p' :: ps)))
   ).
Proof.
  induction ps1; intros; unf; simpl in *.
  - split; intros; unfold evalphid in *; unf; simpl in *.
    * inversionx H3; try tauto.
      eex.
      apply evalphiSymm. simpl.
      eca; rewrite H1.
      + apply inclEmpty.
      + assumption.
      + apply evalphiSymm.
        common.
        assumption.
    * inversionx H2; try tauto.
      apply evalphiSymm in H4.
      simpl in H4.
      inversionx H4. rewrite H1 in *.
      eex.
      eex.
      apply evalphiSymm in H13.
      common.
      assumption.
  - destruct a. simpl in *.
    split; intros; unfold evalphid in *; unf; simpl in *.
    * apply in_map_iff in H3. unf.
      apply in_app_iff in H6.
      inversionx H6.
      + inversionx H5. inversionx H14. common.
        simpl in *. rewrite H11 in *.
        apply (IHps1 ps2 ps p' H0 r (Aexcept A [(o0, f0)])) in H1. unf.
        lapply H3; intros; eauto.
        unf. exists (phiAcc e0 f0 :: x0).
        split.
          apply in_map_iff. eex. intuition.
        eca; simpl; rewrite H11; auto.
        eca.
      + apply in_concat in H2. unf.
        apply in_mapRem_iff in H2. unf. subst.
        destruct x3. simpl in *.
        dec (string_dec f0 s0); try tauto.
        apply in_map_iff in H6. unf. subst.
        inversionx H5. inversionx H15.
        simpl in *. rewrite H12 in *.
        apply (IHps1 (x2 ++ x4) ps p' H0 r (Aexcept A [(o0, s0)])) in H1. unf.
        lapply H2; intros.
          unf. exists (phiAcc e0 s0 :: phiEq e0 e1 :: x1).
          split.
            apply in_map_iff. eex.
            apply in_app_iff. apply or_intror.
            apply in_concat. eex.
              apply in_mapRem_iff. repeat eex.
              simpl. dec (string_dec s0 s0).
              apply in_map_iff. eex.
            eca; simpl; rewrite H12; auto.
              eca.
            inversionx H16.
            inversionx H21.
            eca; simpl. eca.
            common.
            assumption.
        split; auto.
        eex.
        inversionx H16.
        common.
        assumption.
    * apply in_map_iff in H2. unf. subst.
      apply in_app_iff in H5.
      inversionx H5.
      + inversionx H4.
        inversionx H13.
        simpl in *. rewrite H10 in *.
        apply (IHps1 ps2 ps p' H0 r (Aexcept A [(o0, f0)])) in H1. unf.
        lapply H4; intros; eex; try apply H1.
        unf.
        exists (phiAcc e0 f0 :: x0). split.
          apply in_map_iff. eex.
          intuition.
        eca; simpl; rewrite H10; auto.
        eca.
      + apply in_concat in H2. unf.
        apply in_mapRem_iff in H2. unf. subst.
        destruct x3. simpl in *.
        dec (string_dec f0 s0); try tauto.
        apply in_map_iff in H5. unf. subst.
        inversionx H4. inversionx H14. simpl in *. rewrite H11 in *.
        apply (IHps1 (x2 ++ x4) ps p' H0 r (Aexcept A [(o0, s0)])) in H1. unf.
        lapply H3; intros; unf.
          split; auto.
          exists (phiAcc e0 s0 :: phiEq e0 e1 :: x1).
          split.
            apply in_map_iff. eex.
            apply in_app_iff. apply or_intror.
            apply in_concat. eex.
              apply in_mapRem_iff. repeat eex.
              simpl. dec (string_dec s0 s0).
              apply in_map_iff. eex.
            eca; simpl; rewrite H11; auto.
              eca.
            inversionx H15.
            inversionx H21.
            eca; simpl. eca.
            common.
            assumption.
        eex.
        inversionx H15. common.
        assumption.
Qed.

(*
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
 *)

Lemma InEnsuresCutAt : forall {T : Type} (x : T) p,
  In x p ->
  exists xs1 xs2, isCutAt p xs1 x xs2.
Proof.
  induction p0; intros; simpl in *; try tauto.
  inversionx H0.
  - exists []. exists p0.
    unfold isCutAt.
    tauto.
  - intuition.
    unf.
    exists (a :: x1). exists x2.
    unfold isCutAt in *.
    subst.
    tauto.
Qed.

Lemma fstSplitPhiMergePhi : forall p A,
  fst (splitPhi (mergePhi A (snd (splitPhi p)))) = A.
Proof.
  unfold mergePhi.
  induction p0; induction A; intros; simpl in *.
  - tauto.
  - destruct a. simpl.
    apply f_equal2; auto.
  - specialize (IHp0 []).
    destruct a; simpl in *; auto.
  - destruct a0. simpl.
    apply f_equal2; auto.
Qed.

Lemma sndSplitPhiMergePhi : forall p A,
  snd (splitPhi (mergePhi A (snd (splitPhi p)))) = snd (splitPhi p).
Proof.
  unfold mergePhi.
  induction p0; induction A; intros; simpl in *.
  - tauto.
  - assumption.
  - specialize (IHp0 []).
    destruct a; simpl in *;
    try apply f_equal2; auto.
  - assumption.
Qed.

Lemma meetSplitWorks : forall p1 p2,
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  forall H r A,
  (evalphi H r A p1 /\ evalphi H r A p2) <->
  (evalphid H r A (meetSplit (fst ps1) (fst ps2) (snd ps1 ++ snd ps2))).
Proof.
  induction p1; intros; simpl in *; unf.
    split; intros; unfold evalphid in *; unf.
      eappIn evalphiSplitMerge H3. subst ps2. eex. intuition.
      split; try constructor. apply InSingle in H1. subst. eapp evalphiSplitMerge.
  destruct (classic (exists e0 f0, a = phiAcc e0 f0)).
  - unf. subst. subst ps1 ps2.
    split; unfold evalphid in *; intros; unf.
    * inversionx H2. inversionx H12. simpl in *. rewrite H9 in *.
      destruct (classic (In (o0, x1) (footprint H0 r p2))) as [fp2 | fp2].
      + apply staticVSdynamicFP in fp2. unf.
        apply InEnsuresCutAt in H4. unf.
          
        assert (evalphi H0 r (Aexcept A [(o0, x1)]) p1 ∧ 
                evalphi H0 r (Aexcept A [(o0, x1)]) (mergePhi (x3 ++ x4) (snd (splitPhi p2)))) as IH.
          split; auto. admit.
        apply IHp1 in IH. unf.
        exists (phiAcc x0 x1 :: phiEq x0 x2 :: x5).
        split.
          apply in_map_iff. eex.
          apply in_app_iff. apply or_intror.
          apply in_concat.
          exists (map (λ p0, phiEq x0 x2 :: p0) (meetSplit (fst (splitPhi p1)) (x3 ++ x4) (snd (splitPhi p1) ++ snd (splitPhi p2)))).
          split.
            apply in_mapRem_iff.
            exists x3. exists (x2, x1). exists x4.
            split.
              simpl.
              dec (string_dec x1 x1). tauto.
            rewrite splitPhiAlt. assumption.
          apply in_map_iff. eex.
          rewrite fstSplitPhiMergePhi in H5.
          rewrite sndSplitPhiMergePhi in H5.
          assumption.
        eca; simpl; rewrite H9.
          auto.
          eca.
        eca; simpl.
          apply inclEmpty.
          eca.
        common.
        assumption.
      + assert (evalphi H0 r (Aexcept A [(o0, x1)]) p1 ∧ 
                evalphi H0 r (Aexcept A [(o0, x1)]) p2) as IH.
          split; auto. eapp evalphiRemoveAexcept.
          unfold disjoint. intros. apply or_comm. apply imply_to_or. intros. simpl in *.
          inversionx H1; tauto.
        apply IHp1 in IH. unf.
        exists (phiAcc x0 x1 :: x2).
        split.
          apply in_map_iff. eex.
          apply in_app_iff. auto.
        eca; simpl; rewrite H9.
          auto.
          eca.
        assumption.
    * simpl in *.
      rewrite in_map_iff in H1. unf.
      rewrite in_app_iff in H4. inversionx H4.
      + inversionx H3. inversionx H12.
        simpl in *. rewrite H9 in *.
        assert (evalphi H0 r (Aexcept A [(o0, x1)]) p1 ∧ 
                evalphi H0 r (Aexcept A [(o0, x1)]) p2) as IH.
          eapp IHp1.
        unf.
        split.
          eca; simpl; rewrite H9.
            auto.
            eca.
            assumption.
          eapp evalphiAexcept.
      + apply in_concat in H2. unf.
        apply in_mapRem_iff in H2. unf. subst.
        destruct x5. simpl in *.
        dec (string_dec x1 s0).
        apply in_map_iff in H4. unf. subst.
        inversionx H3. inversionx H13.
        simpl in *. rewrite H10 in *.
        inversionx H14. simpl in *. common.
        assert (evalphi H0 r (Aexcept A [(o0, s0)]) p1 ∧ 
                evalphi H0 r (Aexcept A [(o0, s0)]) (mergePhi (x4 ++ x6) (snd (splitPhi p2)))) as IH.
          eapp IHp1.
          eex.
          rewrite fstSplitPhiMergePhi.
          rewrite sndSplitPhiMergePhi.
          assumption.
        unf.
        split.
          eca; simpl; rewrite H10; auto. eca.
          admit.
  - subst ps1 ps2.
    split; intros.
    * unf. inversionx H3.
      destruct a; simpl in *;
      try (contradict H1; eex; fail);
      rewriteRev meetSplitAugment;
      try tauto;
      split; auto;
      apply IHp1;
      split; common; auto.
    * destruct a; simpl in *;
      try (contradict H1; eex; fail);
      rewriteRevIn meetSplitAugment H2;
      try tauto; unf;
      apply IHp1 in H3; unf;
      split; try tauto;
      eca; simpl; common; auto;
      apply inclEmpty.
Admitted.

Lemma maxS1 : forall a b c x,
  max a b <= c ->
  max (x + a) b <= x + c.
Proof.
  intros.
  apply Nat.max_lub.
  - apply Nat.max_lub_l in H0.
    auto with arith.
  - apply Nat.max_lub_r in H0.
    eapp le_trans.
    auto with arith.
Qed.

(* Lemma meetSplitNumFP : forall H r A ps1a ps2a ps1b ps2b p,
  In p (meetSplit ps1a ps2a ps1b ps2b) ->
  length (filter (A'_d_decb A) (footprint H r p)) >= 
  max
  (length (filter (A'_d_decb A) (oflatten (map (A'_s2A'_d H r) ps1a))))
  (length (filter (A'_d_decb A) (oflatten (map (A'_s2A'_d H r) ps2a)))).
Proof.
  induction ps1a; intros; simpl in *.
  - intuition.
    subst.
    rewrite footprintApp.
    rewrite footprintMapAcc.
    rewrite filterApp.
    rewrite app_length.
    auto with arith.
  - destruct a.
    rewrite filterApp.
    rewrite app_length.
    apply in_flat_map in H1. unf.
    apply IHps1a in H1.
    unfold ge in *.
    inversionx H3; simpl in *.
    * destruct (evale' H0 r e0) eqn: ee;
      try (unfold A'_s2A'_d; simpl; rewrite ee; auto; fail).
      destruct v0;
      try (unfold A'_s2A'_d; simpl; rewrite ee; auto; fail).
      rewrite filterApp.
      rewrite app_length.
      assert (olist (A'_s2A'_d H0 r (e0, f0)) = [(o0, f0)]) as ol.
        unfold olist, A'_s2A'_d. simpl. rewrite ee. tauto.
      rewrite ol.
      simpl.
      destruct (A'_d_decb A (o0, f0)) eqn: AA; try assumption.
      eapp maxS1.
    * apply in_map_iff in H2. unf. subst.
      apply filter_In in H4. unf.
      
      simpl.
      eappIn le_trans H1.
      
      unfold A'_s2A'_d.
    
    
  apply length_zero_iff_nil in H2. *)


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
        apply meetSplitWorks in ss. unfold evalphid in ss. unf.
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
          eapp meetSplitWorks.
        unfold evalphid.
        eex. unf.
        split; eex.
      + specialize (IHpd1 pd2 H0 r A).
        inversionx IHpd1.
        lapply H4; intros.
          unf. eex.
        eex.
Qed.
