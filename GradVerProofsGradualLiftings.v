Load GradVer20Hook.
Import Semantics.

(* HSec *)

Inductive hoareSec (hoare : phi -> phi -> Prop) : phi -> phi -> Prop :=
| HSec : forall (p1 p2a p2b p3 : phi),
    hoare p1 p2a ->
    hoare p2b p3 ->
    phiImplies p2a p2b ->
    sfrmphi [] p2b ->
    hoareSec hoare p1 p3
.

Inductive ghoareSec (ghoare : gphi -> gphi -> Prop) : gphi -> gphi -> Prop :=
| GHSec00 : forall (p1 p2a p2b p3 : gphi),
    fst p2b = false ->
    ghoare p1 p2a ->
    ghoare p2b p3 ->
    gphiImplies (false, snd p2a) p2b ->
    sfrmgphi [] p2b ->
    ghoareSec ghoare p1 p3
.

Theorem GLIFT_hoareSec : forall (hoare : phi -> phi -> Prop) p1 p3,
  ghoareSec (GLIFT2 hoare) p1 p3 <-> GLIFT2 (hoareSec hoare) p1 p3.
Proof.
  intros.
  unfold GLIFT2, PLIFT2, gGamma.
  destruct p1 as [bp1 p1].
  destruct p3 as [bp3 p3].
  
  simpl in *. subst.
  split; intros.
  - inversionx H0.
    unf.
    destruct p2a, p2b.
    simpl in *. repeat subst.
    exists x2.
    exists x1.
    repeat split; auto.
    unfold gphiImplies in *.
    inversionx H5; try discriminate.
    simpl in *.
    eca.
    destruct b; unf; subst.
    * eapp phiImpliesTrans.
    * assumption.
  - unf.
    inversionx H3.
    apply (GHSec00 _ (bp1, p1) (false, p2a) (false, p2b) (bp3, p3));
    auto;
    simpl;
    try eex.
    unfold sfrmgphi.
    auto.
Qed.



Definition ghoareSec (ghoare : gphi -> gphi -> Prop) (gp1 gp3 : gphi) :=
  exists (gp2a gp2b : gphi),
    ghoare gp1 gp2a /\
    ghoare gp2b gp3 /\
    gphiImplies gp2a gp2b /\
    sfrmgphi [] gp2b.



Theorem hasWellFormedSubtype : forall p,
  phiSatisfiable p ->
  ∃ p' : phi, phiSatisfiable p' ∧ sfrmphi [] p' ∧ phiImplies p' p.
Proof.
  induction p0; intros; simpl.
  - exists [].
    split; auto.
    repeat eex.
  - admit.
Admitted.

(* Inductive ghasStaticType : gphi -> e -> T -> Prop :=
| GSTValNum : forall p n, 
  ghasStaticType p (ev (vn n)) TPrimitiveInt
| GSTValNull : forall p C, 
  ghasStaticType p (ev vnull) (TClass C)
| GSTVar : forall p T x,

  gphiImplies p (gThat [phiType x T]) -> 
  ghasStaticType p (ex x) T
| GSTField : forall p e f C T,
  
  ghasStaticType p e (TClass C) -> 
  gphiImplies p (gThat [phiNeq e (ev vnull)]) ->
  fieldType C f = Some T ->
  ghasStaticType p (edot e f) T
.

Theorem GLIFT_sfrmphi : forall p e T,
  gphiSatisfiable p ->
  ghasStaticType p e T <-> GLIFT1 (fun p => hasStaticType p e T) p.
Proof.
  unfold GLIFT1, PLIFT1, gGamma, gphiSatisfiable, sfrmgphi.
  intros.
  destruct p0. simpl in *.
  split; intros.
  - destruct b.
    * apply hasWellFormedSubtype in H0. unf.
      exists x0.
      split; auto.
      inversionx H1; eca.
      unfold gphiImplies in *; simpl in *; unf.
      repeat auto.
      inversionx H1.
      + exists [].
        repeat eca.
        .
      unfold gphiSatisfiable in H0. simpl in *.
      eappIn hasWellFormedSubtype H0.
      unf.
      eex.
      eapp sfrmIncl.
      apply inclEmpty.
    * inversionx H0; try discriminate.
      eex.
      intuition.
  - unf.
    destruct b; try tauto.
    subst.
    auto.
Qed. *)

Theorem GLIFT_phiImplies : forall p1 p2,
  gphiSatisfiable p1 ->
  sfrmgphi [] p1 ->
  gphiImplies p1 p2 <-> GLIFT2 phiImplies p1 p2.
Proof.
  unfold GLIFT2, PLIFT2, gGamma, gphiSatisfiable, sfrmgphi, gphiImplies.
  intros.
  destruct p1, p2. simpl in *.
  destruct b0.
  - split; intros; unf.
    * destruct b.
      + unf.
        exists x0.
        exists x0.
        auto.
      + exists p0.
        exists p0.
        inversionx H1; try discriminate.
        auto.
    * destruct b.
      + unf.
        eexists x0.
        repeat split; auto.
        eapp (phiImpliesTrans x0 x1 p1).
      + inversionx H1; try discriminate.
        eapp (phiImpliesTrans p0 x1 p1).
  - destruct b.
    * split; intros; unf.
      + exists x0.
        exists p1.
        auto.
      + subst.
        exists x0.
        auto.
    * split; intros.
      + eex.
      + unf.
        subst.
        assumption.
Qed.


Theorem GLIFT_sfrmphi : forall a p,
  gphiSatisfiable p ->
  sfrmgphi a p <-> GLIFT1 (sfrmphi a) p.
Proof.
  unfold GLIFT1, PLIFT1, gGamma, sfrmgphi.
  intros.
  destruct p0. simpl.
  split; intros.
  - destruct b.
    * unfold gphiSatisfiable in H0. simpl in *.
      eappIn hasWellFormedSubtype H0.
      unf.
      eex.
      eapp sfrmIncl.
      apply inclEmpty.
    * inversionx H0; try discriminate.
      eex.
      intuition.
  - unf.
    destruct b; try tauto.
    subst.
    auto.
Qed.

(* hasWellFormedSubtype *)
Fixpoint eComplexity (e : e) : nat :=
  match e with
  | edot e f => Datatypes.S (eComplexity e)
  | _ => 0
  end.

Fixpoint gee (e1 e2 : e) : bool :=
  let e1c := eComplexity e1 in
  let e2c := eComplexity e2 in
  if ge_dec e1c e2c then true else false.

Definition NORMphi' (p : phi') : phi' :=
  match p with
  | phiEq  e1 e2 => if gee e1 e2 then phiEq  e1 e2 else phiEq  e2 e1
  | phiNeq e1 e2 => if gee e1 e2 then phiNeq e1 e2 else phiNeq e2 e1
  | _ => p
  end.
Definition NORMphi (p : phi) : phi :=
  map NORMphi' p.

Lemma NORMphi'evalphi' : forall p H r A,
  evalphi' H r A p <-> evalphi' H r A (NORMphi' p).
Proof.
  intros.
  destruct p0; simpl;
  try destruct (gee e0 e1);
  try tauto;
  split; intros;
  inversionx H1;
  eca;
  unfold neq in *;
  auto.
Qed.

Lemma NORMphi'footprint' : forall p H r,
  footprint' H r p = footprint' H r (NORMphi' p).
Proof.
  intros.
  destruct p0; simpl;
  try destruct (gee e0 e1);
  tauto.
Qed.

Lemma NORMphievalphi : forall p H r A,
  evalphi H r A p <-> evalphi H r A (NORMphi p).
Proof.
  induction p0; intros; simpl in *; try tauto.
  split; intros; inversionx H1.
  - rewrite NORMphi'footprint', NORMphi'evalphi' in *.
    apply IHp0 in H12.
    eca.
  - rewriteRevIn NORMphi'footprint' H6.
    rewriteRevIn NORMphi'footprint' H11.
    rewriteRevIn NORMphi'footprint' H12.
    rewriteRevIn NORMphi'evalphi' H11.
    apply IHp0 in H12.
    eca.
Qed.

Fixpoint eSubste (e1 e2 : e) (e' : e) : e :=
  if e_dec e' e1
  then e2
  else match e' with
       | edot e f => edot (eSubste e1 e2 e) f
       | _ => e'
       end.

Definition phi'Subste (e1 e2 : e) (p : phi') : phi' :=
  match p with
  | phiTrue => phiTrue
  | phiEq e1' e2' => phiEq (eSubste e1 e2 e1') (eSubste e1 e2 e2')
  | phiNeq e1' e2' => phiNeq (eSubste e1 e2 e1') (eSubste e1 e2 e2')
  | phiAcc e f => phiAcc (eSubste e1 e2 e) f
  | phiType x T => phiType x T
  end.

Definition phiSubste (e1 e2 : e) (p : phi) : phi :=
  map (phi'Subste e1 e2) p.

Lemma eSubsteSAME : forall e1 e2 H r e,
  evale' H r e1 = evale' H r e2 ->
  evale' H r (eSubste e1 e2 e) = evale' H r e.
Proof.
  induction e0; intros.
  - destruct e1; try tauto.
    simpl.
    destruct (vex_dec v0 v1); try tauto.
    subst.
    simpl.
    rewriteRev H1.
    tauto.
  - destruct e1; try tauto.
    simpl.
    destruct (x_dec x0 x1); try tauto.
    subst.
    simpl.
    rewriteRev H1.
    tauto.
  - destruct e1; simpl; try rewrite IHe0; auto.
    destruct (e_dec e0 e1); simpl; try rewrite IHe0; auto.
    subst.
    destruct (string_dec f0 f1); simpl; try rewrite IHe0; auto.
    subst.
    rewriteRev H1.
    tauto.
Qed.

Lemma phi'SubsteSAME : forall e1 e2 H r A p,
  evale' H r e1 = evale' H r e2 ->
  evalphi' H r A (phi'Subste e1 e2 p) <-> evalphi' H r A p.
Proof.
  intros.
  destruct p0; simpl;
  try tauto;
  split; intros;
  inversionx H2;
  eca;
  unfold evale in *;
  rewrite eSubsteSAME in *;
  eauto.
Qed.

Lemma footprint'phi'SubsteSAME : forall e1 e2 H r p,
  evale' H r e1 = evale' H r e2 ->
  footprint' H r (phi'Subste e1 e2 p) = footprint' H r p.
Proof.
  intros.
  destruct p0; simpl;
  try tauto.
  rewrite eSubsteSAME; auto.
Qed.

Lemma phiSubsteSAME : forall e1 e2 H r p A,
  evale' H r e1 = evale' H r e2 ->
  evalphi H r A (phiSubste e1 e2 p) <-> evalphi H r A p.
Proof.
  induction p0; intros; simpl in *; try tauto.
  split; intros;
  inversionx H2; eca;
  try rewrite phi'SubsteSAME in *; auto;
  try rewrite footprint'phi'SubsteSAME in *; auto;
  eapp IHp0.
Qed.


















(* PLAYGROUND *)



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

Definition meetSingle (p1 p2 : phi) : phid :=
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  meetSplit (fst ps1) (fst ps2) (snd ps1 ++ snd ps2).

Definition meet (pd1 pd2 : phid) : phid :=
  flat_map (fun ps => meetSingle (fst ps) (snd ps)) (list_prod pd1 pd2).

(* 
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
 *)

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

Lemma evalphiIsCutAt : forall H r A A1 A2 e o f p,
  evale' H r e = Some (vo o) ->
  isCutAt (staticFootprint p) A1 (e, f) A2 ->
  incl [(o, f)] A ->
  evalphi H r A p <->
  evalphi H r (Aexcept A [(o, f)]) (mergePhi (A1 ++ A2) (snd (splitPhi p))).
Proof.
  unfold isCutAt, mergePhi.
  intros.
  rewrite evalphiSplitMerge.
  assert (fst (splitPhi p0) = A1 ++ (e0, f0) :: A2).
    rewrite splitPhiAlt. assumption.
  rewrite H4.
  repeat rewrite map_app.
  set (mm := map (λ p : e * f, phiAcc (fst p) (snd p))).
  assert (
    evalphi H0 r A ((mm A1 ++ mm ((e0, f0) :: A2)) ++ snd (splitPhi p0))
    <->
    evalphi H0 r A ((mm ((e0, f0) :: A2) ++ mm A1) ++ snd (splitPhi p0))
    ) as rw1.
    split; intros;
    apply evalphiApp in H5; unf;
    apply evalphiSymm in H6;
    rewrite footprintApp in H7;
    rewrite Aexcept2AppComm in H7;
    rewriteRevIn footprintApp H7;
    eapp evalphiAppRev.
  assert (
    evalphi H0 r (Aexcept A [(o0, f0)]) ((mm A1 ++ mm A2) ++ snd (splitPhi p0))
    <->
    evalphi H0 r (Aexcept A [(o0, f0)]) ((mm A2 ++ mm A1) ++ snd (splitPhi p0))
    ) as rw2.
    split; intros;
    apply evalphiApp in H5; unf;
    apply evalphiSymm in H6;
    rewrite footprintApp in H7;
    rewrite Aexcept2AppComm in H7;
    rewriteRevIn footprintApp H7;
    eapp evalphiAppRev.
  subst mm.
  rewrite rw1, rw2.
  repeat rewriteRev app_assoc.
  simpl.
  assert (forall p, evalphi H0 r A (phiAcc e0 f0 :: p) <->
                    evalphi H0 r (Aexcept A [(o0, f0)]) p)
  as rw.
    split; intros.
      inversionx H5. inversionx H15. simpl in *. rewrite H12 in *. inversionx H1. assumption.
      eca; simpl; rewrite H1; auto. eca. apply in_eq.
  rewrite rw.
  tauto.
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
          split; auto.
          eappIn evalphiIsCutAt H4.
          rewriteRev H4. assumption.
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
          rewrite splitPhiAlt in H5. simpl in *.
          inversionx H16. common. rewrite H10 in *. inversionx H12.
          eappIn evalphiIsCutAt H5.
          rewrite H5. assumption.
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
