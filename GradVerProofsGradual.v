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
(* Fixpoint meetSplit (pa1 pa2 : A_s) (pb1 pb2 : phi) : phid :=
  match pa1 with
  | [] => [map (fun p => phiAcc (fst p) (snd p)) pa2 ++ pb1 ++ pb2]
  | A :: pa1 =>
    map (fun p => phiAcc (fst A) (snd A) :: p)
    (
      meetSplit pa1 pa2 pb1 pb2
      ++
      concat
      (
        mapRem
        (fun A' pa2 =>
          if f_decb (snd A) (snd A')
          then map (fun p => phiEq (fst A) (fst A') :: p) (meetSplit pa1 pa2 pb1 pb2)
          else []
        )
        pa2
      )
    )
  end. *)

Fixpoint meetSplit (pa1 pa2 : A_s) (pb1 pb2 : phi) : phid :=
  match pa1 with
  | [] => [map (fun p => phiAcc (fst p) (snd p)) pa2 ++ pb1 ++ pb2]
  | A :: pa1 =>
    map (fun p => phiAcc (fst A) (snd A) :: p)
    (
      meetSplit pa1 pa2 pb1 pb2
      ++
      concat
      (
        map
        (fun pa2 =>
          match pa2 with
          | [] => []
          | A' :: pa2 =>
            if f_decb (snd A) (snd A')
            then map (fun p => phiEq (fst A) (fst A') :: p) (meetSplit pa1 pa2 pb1 pb2)
            else []
          end
        )
        (cycles pa2)
      )
    )
  end.

Lemma permutMeetSplit2a : forall pa1 pa2 pa2' pb1 pb2 H r A,
  isPermutation pa2 pa2' ->
  (evalphid H r A (meetSplit pa1 pa2  pb1 pb2) <->
   evalphid H r A (meetSplit pa1 pa2' pb1 pb2)).
Proof.
  auto.
Admitted.

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
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"] [phiAcc (ex (xUserDef "c")) "f"].
Close Scope string.
(*END test*)

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
   (
    (evalphid H r A (meetSplit ps1a ps2a ps1b ps2b) /\ evalphi' H r [] p')
    <->
    (evalphid H r A (meetSplit ps1a ps2a (p' :: ps1b) ps2b))
   ).
Proof.
  induction ps1a; intros; unf; simpl in *.
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
      eex.
      aapply evalphiSymm in H4. simpl in *.
  - apply in_map_iff in H5. unf.
    apply in_app_iff in H8.
    inversionx H8.
    * inversionx H7.
      eappIn IHps1a H3.
      + unf.
        exists (phiAcc (fst a) (snd a) :: x0).
        split; try eca.
        apply in_map_iff. eex.
        apply in_app_iff. eauto.
      + inversionx H1. assumption.
    * apply in_flat_map in H6. unf.
      destruct a, x0. simpl in *.
      dec (string_dec f0 s0); subst; try tauto.
      apply in_map_iff in H8. unf. subst.
      inversionx H7.
      inversionx H17.
      inversionx H18.
      inversionx H20.
      common.
      simpl in *. rewrite H14 in *.
      inversionx H10.
      eappIn (IHps1a ps1b (remove A'_s_dec (e1, s0) ps2a) ps2b) H3; unf.
      + exists (phiAcc e0 s0 :: phiEq e0 e1 :: x1). split.
          apply in_map_iff. eex.
          apply in_app_iff. apply or_intror.
          apply in_flat_map. eex. simpl.
          dec (string_dec s0 s0).
          apply in_map_iff. eex.
        eca; simpl; rewrite H14; auto; eca; common; auto.
        eca.
      + inversionx H1. assumption.
      + apply NoDupRemove.
        assumption.
Qed.
 *)
(* Lemma meetSplitAugment1Rev : forall ps1a ps1b ps2a ps2b p' H r A,
   NoDup ps1a ->
   NoDup ps2a ->
   footprint' H r p' = [] ->
   (∃ p0 : phi, In p0 (meetSplitDistinct ps1a ps2a (p' :: ps1b) ps2b) ∧ evalphi H r A p0) ->
   evalphi' H r [] p' /\
   (∃ p0 : phi, In p0 (meetSplitDistinct ps1a ps2a ps1b ps2b) ∧ evalphi H r A p0).
Proof.
  induction ps1a; intros; unf; simpl in *.
  - inversionx H4; try tauto.
    apply evalphiSymm in H6.
    rewriteRevIn app_comm_cons H6.
    inversionx H6.
    rewrite H3 in *.
    split; auto.
    common.
    apply evalphiSymm in H15.
    eex.
  - apply in_map_iff in H4. unf.
    apply in_app_iff in H7.
    inversionx H7.
    * inversionx H6.
      assert (NoDup ps1a). inversionx H1. assumption.
      eappIn (IHps1a ps1b ps2a) H3; try apply H3.
      unf.
      exists (phiAcc (fst a) (snd a) :: x0).
      split.
      + apply in_map_iff.
        eex.
        intuition.
      + eca.
    * apply in_flat_map in H5. unf.
      destruct a, x0. simpl in *.
      dec (string_dec f0 s0); try tauto.
      apply in_map_iff in H7. unf. subst.
      inversionx H6. inversionx H16.
      inversionx H17. inversionx H19.
      common.
      simpl in *.
      rewrite H9 in *. inversionx H13.
      eappIn (IHps1a ps1b (remove A'_s_dec (e1, s0) ps2a)) H3; try apply H3. 
      + unf.
        exists (phiAcc e0 s0 :: phiEq e0 e1 :: x1).
        split.
        ++apply in_map_iff. eex.
          apply in_app_iff. apply or_intror.
          apply in_flat_map. eex.
          simpl.
          dec (string_dec s0 s0).
          eapp in_map.
        ++eca;
          simpl;
          rewrite H9;
          try assumption;
          eca; common;
          try assumption.
          eca.
      + inversionx H1. assumption.
      + apply NoDupRemove. assumption.
Qed. *)

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

Lemma meetSplitWorks : forall p2 p1,
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  forall H r A,
  (evalphi H r A p1 /\ evalphi H r A p2) <->
  (evalphid H r A (meetSplit (fst ps1) (fst ps2) (snd ps1) (snd ps2))).
Proof.
  induction p1; intros; simpl in *; unf.
    split; intros; unfold evalphid in *; unf.
      eappIn evalphiSplitMerge H3. subst ps2. eex. intuition.
      split; try constructor. apply InSingle in H1. subst. eapp evalphiSplitMergeRev.
  split; unfold evalphid in *; intros; unf.
  - 
  destruct (classic (~ exists e0 f0, a = phiAcc e0 f0)).
    split; intros; unfold evalphid in *; unf.
  inversionx H4.
  assert (evalphi H2 r A p1 ∧ evalphi H2 r A p2) as IH.
    apply evalphiAexcept in H15. auto.
  assert (NoDup (fst (splitPhi p1))) as nd1.
    subst ps1. destruct a; simpl in *; auto. inversionx H0. assumption.
  eappIn IHp1 IH. invE IH p'.
  destruct a;
  try eapp meetSplitDistinctAugment1.
  subst ps1 ps2. simpl in *.
  inversionx H14.
  rewrite H11 in *. unf.
  
  destruct (classic (In (o0, f0) (footprint H2 r p2))).
  - apply staticVSdynamicFP in H6. invE H6 e'. unf.
    eexists (phiAcc e0 f0 :: phiEq e0 e' :: _).
    split.
      apply in_map_iff. eex.
      apply in_app_iff. apply or_intror.
      apply in_flat_map.
      assert (In (e', f0) (fst (splitPhi p2))).
        rewrite splitPhiAlt. auto.
      eex.
      simpl.
      dec (string_dec f0 f0).
      apply in_map_iff. eex.
      admit.
      admit.
  - exists (phiAcc e0 f0 :: p').
    split.
      apply in_map_iff. eex.
      apply in_app_iff. constructor.
      assumption.
    eca; simpl; rewrite H11.
      assumption.
      eca.
    eapp evalphiRemoveAexcept.
    unfold disjoint. intros.
    apply or_comm. apply imply_to_or. intros.
    apply InSingle in H7. subst.
    admit.
Admitted.

Lemma meetSplitDistinctWorksRev : forall p1 p2,
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  NoDup (fst ps1) ->
  NoDup (fst ps2) ->
  forall H r A,
  (exists p, In p (meetSplitDistinct (fst ps1) (fst ps2) (snd ps1) (snd ps2)) /\
             evalphi H r A p) ->
  (evalphi H r A p1 /\ evalphi H r A p2).
Proof.
  induction p1; intros; simpl in *; unf.
  - split; try constructor.
    intuition. subst.
    eapp evalphiSplitMergeRev.
  - destruct (classic (exists e f, a = phiAcc e f)).
    * unf. subst. subst ps1 ps2. simpl in *.
      inversionx H0.
      apply in_map_iff in H3. unf. subst.
      apply in_app_iff in H4.
      inversionx H4.
      + inversionx H5. inversionx H15.
        simpl in *; rewrite H12 in *.
        assert (evalphi H2 r (Aexcept A [(o0, x2)]) p1 ∧ evalphi H2 r (Aexcept A [(o0, x2)]) p2).
          eapp IHp1.
        unf.
        split.
          eca; simpl; rewrite H12; auto. eca.
        eapp evalphiAexcept.
      + apply in_flat_map in H0. unf. destruct x0. simpl in *.
        dec (string_dec x2 s0); try discriminate.
        apply in_map_iff in H4. unf. subst.
        inversionx H5. inversionx H16.
        inversionx H17. inversionx H19.
        common.
        simpl in *; rewrite H13 in *.
        inversionx H9.
        rewrite splitPhiAlt in H2. simpl in H2.
        inversionx H3. simpl in H9, H14, H15.
        inversionx H14. common.
        assert (In (phiAcc e1 s0) p2) as ip.
          unfold staticFootprint in H2.
          apply in_flat_map in H2. unf.
          destruct x0; try tauto. simpl in *. intuition.
          inversionx H8. assumption.
        eappIn evalphiIn ip. inversionx ip. common.
        rewrite H13 in *. inversionx H12.
        assert (footprint' H0 r (phiAcc e0 s0) = [(o0, s0)]) as fp.
          simpl. rewrite H7. tauto.
        eca; rewrite fp.
        ++apply inclSingle.
          assumption.
        ++eca.
          apply in_eq.
        ++eapp evalphiRemoveAexcept.
          unfold disjoint. intros.
          apply or_comm. apply imply_to_or. intros.
          apply InSingle in H3. subst.
          unfold not. intros fp1.
          
          unfold A'_s2A'_d in *.
          simpl in *.
          rewrite splitPhiAlt in ld_p1. simpl in *. unf.
          contradict H3.
          rewrite H7. simpl.
          apply in_map_iff.
          apply staticVSdynamicFP in fp1. unf.
          eex. simpl.
          rewrite H6. simpl.
          tauto.
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
Qed.

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

Lemma meetSplitDistinctFP : forall ps1a ps2a ps1b ps2b,
  forall H r,
  (exists p, In p (meetSplit ps1a ps2a ps1b ps2b) /\
             listDistinct (footprint H r p)) ->
  (listDistinct (oflatten (map (A'_s2A'_d H r) ps1a))) /\ (listDistinct (oflatten (map (A'_s2A'_d H r) ps2a))).
Proof.
  induction ps1a; intros; simpl in *.
  - unf. intuition.
    subst.
    repeat rewrite footprintApp in *.
    apply distinctApp in H3. unf.
    rewrite footprintMapAcc in H1.
    assumption.
  - unf.
    apply in_flat_map in H1. unf.
    assert (listDistinct (oflatten (map (A'_s2A'_d H0 r) ps1a))
           ∧ listDistinct (oflatten (map (A'_s2A'_d H0 r) ps2a)))
    as IH.
      eapp IHps1a. eex.
      inversionx H4. rewrite cons2app, footprintApp in H3. apply distinctApp in H3. apply H3.
      apply in_map_iff in H2. unf.
      subst.
      rewrite cons2app, footprintApp in H3. apply distinctApp in H3. apply H3.
    intuition.
    destruct (olist (A'_s2A'_d H0 r a)) eqn: ola; try tauto.
    unfold A'_s2A'_d, olist in ola.
    destruct a. simpl in *.
    destruct (evale' H0 r e0) eqn: ee; try discriminate.
    destruct v0; try discriminate.
    inversionx ola. simpl.
    split; try assumption.
    inversionx H4.
    * admit.
    * apply in_map_iff in H6. unf. subst.
      simpl in *.
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
