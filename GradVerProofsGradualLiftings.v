Load GradVer22Galois.
Import Semantics.

(* determ split *)

Definition pimpl (pa pb : pphi) : Prop :=
  forall p, pa p -> exists p', pb p' /\ phiImplies p p'.

Definition mpt (a b : gphi) : Prop := pincl (gGamma' a) (gGamma' b).
Definition mpst (a b : gphi) : Prop := pimpl (gGamma' a) (gGamma' b).

Definition env := prod H (prod rho A_d).
Definition evalgphi (H : H) (rho : rho) (A : A_d) (gp : gphi) : Prop := exists p, gGamma' gp p /\ evalphi H rho A p.
Definition genvs (gp : gphi) : (env -> Prop) := fun e => (evalgphi (fst e) (fst (snd e)) (snd (snd e)) gp).
Definition envIncl (a b : env -> Prop) : Prop := forall e, a e -> b e.

(* connection mpt, envs, ... *)
Lemma mpt_gencs : forall g1 g2,
  mpt g1 g2 ->
  envIncl (genvs g1) (genvs g2).
Proof.
  repeat intro.
  unfold genvs, evalgphi in *.
  unf.
  apply H in H0.
  eex.
Qed.

Lemma gencs_mpt : forall p1 g2,
  good p1 ->
  envIncl (genvs (false, p1)) (genvs g2) ->
  (exists p2, g2 = (true, p2) /\ mpt (false, p1) g2) \/
  (exists p2, g2 = (false, p2) /\ phiImplies p1 p2).
Proof.
  repeat intro.
  unfold envIncl, genvs, evalgphi in *.
  destruct g2.
  destruct b.
  - apply or_introl.
    exists p0. splau.
    repeat intro.
    inv H1.
    simpl.
    eca.
    repeat intro.
    specialize (H0 (h, (r, a))).
    lapply H0; intros; cut.
    unf. simpl in *.
    inv H2.
    eapp H5.
  - apply or_intror.
    eex.
    repeat intro.
    specialize (H0 (h, (r, a))).
    lapply H0; intros; cut.
    unf. simpl in *.
    inv H2.
    eapp H4.
Qed.


(* Definition isPredMonotonousInformation (P : phi -> phi -> Prop) : Prop :=
  forall p1 p2 p1x, phiImplies p2 p1
    -> P p1 p1x
    -> exists p2x, P p2 p2x /\ phiImplies p2x p1x. *)

Inductive optPredLifting (P : phi -> phi -> Prop) : gphi -> gphi -> Prop :=
| OPLintro : forall p1 p2, 
    P p1 p2 -> 
    optPredLifting P (false, p1) (false, p2)
| OPLmon : forall g1 g2 g1x g2x, 
    mpt g1 g1x -> 
    mpt g2 g2x -> 
    optPredLifting P g1 g2 -> 
    optPredLifting P g1x g2x
.

Definition optPredLiftingAlt (P : phi -> phi -> Prop) : gphi -> gphi -> Prop :=
  fun gp1 gp2 => exists p1 p2, gGamma' gp1 p1 /\ gGamma' gp2 p2 /\ P p1 p2.

Lemma optPredLiftingAltEQ : forall P gp1 gp2,
  optPredLifting P gp1 gp2 <-> optPredLiftingAlt P gp1 gp2.
Proof.
  unfold optPredLiftingAlt.
  split; intros.
  - induction H.
    * exists p1.
      exists p2.
      cut.
    * unf.
      apply H in H2.
      apply H0 in H3.
      eex.
  - unf.
    apply (OPLmon _ (false, x) (false, x0)); cut;
    unfold mpt, pincl; intros; unfold gGamma' in H1; 
    simpl in *; subst; auto.
Qed.

Definition funcLifting (P : phi -> phi) (GP : gphi -> gphi) : Prop :=
  (forall p, gGamma' (GP (false, p)) (P p)) /\
  (forall gp1 gp2, mpt gp1 gp2 -> mpt (GP gp1) (GP gp2)).

Definition mptFunc (GP1 GP2 : gphi -> gphi) : Prop :=
  forall gp, mpt (GP1 gp) (GP2 gp).

Definition optFuncLifting (P : phi -> phi) (GP : gphi -> gphi) : Prop :=
    minWith (funcLifting P) mptFunc GP.

Definition optFuncLiftingAlt (P : phi -> phi) (GP : gphi -> gphi) : Prop :=
    forall gp, gAlpha (fun p => exists p', gGamma' gp p' /\ P p' = p) (GP gp).

Lemma optFuncLiftingAltEQ : forall P GP,
  optFuncLifting P GP <-> optFuncLiftingAlt P GP.
Proof.
  split; intros.
  - inv H.
    repeat intro.
    split.
    * admit.
    * admit.
    * repeat intro.
      unf.
      subst.
      inv H0.
      eapply H3. Focus 2. apply H2.
      repeat intro.
      inv H0.
      assumption.
    * intros.
      repeat intro.
      eapply H1 in H3.
      Focus 2.
        instantiate (1 := (fun x => gp')).
        split; intros; cut.
        apply H2. eex.
      admit.
      admit.
  - unfold optFuncLiftingAlt in H.
    split.
    * eca; intros.
      + specialize (H (false, p0)).
        inv H.
        apply H2.
        eex.
      + pose proof (H gp1).
        pose proof (H gp2).
        inv H1. inv H2.
        apply H6. admit.
        repeat intro. apply H8.
        unf. subst.
        apply H0 in H2.
        eex.
Qed.

Definition isOptPredLifting 
  (P : phi -> phi -> Prop)
  (GP : gphi -> gphi -> Prop) : Prop :=
    forall gp1 gp2, optPredLifting P gp1 gp2 <-> GP gp1 gp2.

Definition isPredLifting 
  (P : phi -> phi -> Prop)
  (GP : gphi -> gphi -> Prop) : Prop :=
    forall gp1 gp2, optPredLifting P gp1 gp2 -> GP gp1 gp2.


Definition isFunMonotonous (GF : gphi -> gphi) : Prop :=
  forall g gx, mpt g gx -> mpt (GF g) (GF gx).
Definition isFunInit
  (F : phi -> phi)
  (GF : gphi -> gphi) : Prop :=
    forall p, mpt (false, F p) (GF (false, p)).
Definition isFunLifting 
  (F : phi -> phi)
  (GF : gphi -> gphi) : Prop :=
    isFunInit F GF /\
    isFunMonotonous GF.
Definition isMptFunLifting (GF1 GF2 : gphi -> gphi) : Prop :=
  forall g, mpt (GF1 g) (GF2 g).
Definition isOptFunLifting 
  (F : phi -> phi)
  (GF : gphi -> gphi) : Prop :=
    isFunLifting F GF /\
    forall GFx, isFunLifting F GFx -> isMptFunLifting GF GFx.

Definition isPFunMonotonous (GF : gphi -> option gphi) : Prop :=
  forall g gx gr, mpt g gx 
    -> GF g = Some gr 
    -> exists gxr, GF gx = Some gxr /\ mpt gr gxr.
Definition isPFunInit
  (F : phi -> option phi)
  (GF : gphi -> option gphi) : Prop :=
    forall p pr,
      F p = Some pr ->
      exists pxr, GF (false, p) = Some pxr /\ mpt (false, pr) pxr.
Definition isPFunLifting 
  (F : phi -> option phi)
  (GF : gphi -> option gphi) : Prop :=
    isPFunInit F GF /\
    isPFunMonotonous GF.
Definition isMptPFunLifting (GF1 GF2 : gphi -> option gphi) : Prop :=
  forall g g1 g2, 
    GF1 g = Some g1 ->
    GF2 g = Some g2 ->
    mpt g1 g2.
Definition isOptPFunLifting 
  (F : phi -> option phi)
  (GF : gphi -> option gphi) : Prop :=
    isPFunLifting F GF /\
    forall GFx, isPFunLifting F GFx -> isMptPFunLifting GF GFx.

Definition phiImpliesStrict (p1 p2 : phi) := phiImplies p1 p2 /\ ~ phiImplies p2 p1.

Definition hasNoUniqueImplicator (P : phi -> Prop) (p : phi) :=
  forall pri, P pri -> phiImpliesStrict pri p -> exists prix, P prix /\ phiImpliesStrict prix pri.
Definition isHybridInit
  (P : phi -> phi -> Prop)
  (GF : gphi -> option gphi) : Prop :=
    forall p pr,
      P p pr ->
      (exists pxr, GF (false, p) = Some pxr) (* \/
      (exists pxr, GF (false, p) = Some pxr /\ mpt (false, pr) pxr) *).
Definition isHybridMesh
  (P : phi -> phi -> Prop)
  (GF : gphi -> option gphi) : Prop :=
    forall gp pxr,
      GF gp = Some pxr ->
      (forall pr p, gGamma' gp p -> P p pr -> exists pr', P p pr' /\ gGamma' pxr pr' /\ phiImplies pr' pr).
Definition isHybridLifting 
  (P : phi -> phi -> Prop)
  (GF : gphi -> option gphi) : Prop :=
    isHybridInit P GF /\
    isHybridMesh P GF /\
    isPFunMonotonous GF.
Definition isMptHybridLifting (GF1 GF2 : gphi -> option gphi) : Prop :=
  forall g, 
    (GF1 g <> None -> GF2 g <> None)
    /\
    (forall g1 g2,
     (GF1 g = Some g1 ->
      GF2 g = Some g2 ->
      mpt g1 g2)).
Definition isOptHybridLifting 
  (P : phi -> phi -> Prop)
  (GF : gphi -> option gphi) : Prop :=
    isHybridLifting P GF /\
    forall GFx, isHybridLifting P GFx -> isMptPFunLifting GF GFx.

Lemma mptImplies2 : forall p gp1 gp2,
  mpt gp1 gp2 ->
  good p -> 
  phiImplies p (snd gp1) ->
  phiImplies p (snd gp2).
Proof.
  unfold mpt.
  unfold gGamma'.
  unfold pincl.
  intros.
  destruct gp1, gp2.
  simpl in *.
  destruct b.
  - specialize (H p0).
    lapply H; cut.
    intros.
    destruct b0; cut.
  - specialize (H p1).
    lapply H; cut.
    intros.
    destruct b0; unf.
    * eapp phiImpliesTrans.
    * subst. assumption.
Qed.

Lemma mptImplies : forall g1 g1x g2 g2x,
  mpt g1 g1x ->
  mpt g2 g2x -> 
  gphiImplies g1 (snd g2) ->
  gphiImplies g1x (snd g2x).
Proof.
  intros.
  unfold gphiImplies in *. unf.
  exists x.
  splau.
  eapply mptImplies2; eauto.
  admit.
Admitted.

Theorem determSplitWorks : forall P GP,
  isHybridLifting P GP ->
  isPredLifting 
    P
    (fun gp1 gp2 => exists gp2x, GP gp1 = Some gp2x /\ gphiImplies gp2x (snd gp2)).
Proof.
  unfold isHybridLifting, isPredLifting.
  unfold isHybridInit, isPFunMonotonous.
  intros. unf.
  rename H1 into intr.
  rename H into mesh.
  rename H3 into monp.
  induction H0.
  - assert (H' := H).
    eapply intr in H; cut. unf.
    eex. simpl.
    apply mesh in H0.
    apply H0 in H'; cut.
    unf.
    eex.
  - unf.
    eapply monp in H3; eauto. unf. eex.
    eapp mptImplies.
Qed.


Lemma gphiImpliesMon : forall P DP p1 p2 gp1 gp2,
  isHybridLifting P DP ->
  P p1 p2 ->
  DP gp1 = Some gp2 ->
  gphiImplies gp1 p1 ->
  gphiImplies gp2 p2.
Proof.
  intros.
  inv H2. unf.
  assert (exists p2x, P x p2x /\ phiImplies p2x p2).
    admit.
  unf.
  assert (H3' := H3).
  apply H in H3'. unf.
  assert (mpt x1 gp2).
    eapply H in H5. Focus 2. instantiate (1 := gp1). repeat intro. inv H9. assumption.
    unf. rewrite H5 in H1. inv H1. assumption.
  apply H in H5.
  apply H5 in H3; cut.
  unf.
  eex.
  eapp phiImpliesTrans.
Admitted.

(* Lemma phiImpliesMon : forall P DP p1 p2 gp1 gp2,
  isHybridLifting P DP ->
  P p1 p2 ->
  DP gp1 = Some gp2 ->
  phiImplies p1 (snd gp1) ->
  phiImplies p2 (snd gp2).
Proof.
  intros.
  assert (H0' := H0).
  apply H in H0'. unf.
  
  destruct gp1. simpl in *.
  destruct b.
  - admit.
  - 
Admitted. *)

Lemma hybridLiftingComp : forall P1 P2 GP1 GP2,
  isHybridLifting P1 GP1 ->
  isHybridLifting P2 GP2 ->
  isHybridLifting 
    (fun a c => exists b, P1 a b /\ P2 b c)
    (fun s => option_bind GP2 (GP1 s)).
Proof.
  split; try split; repeat intro.
  - repeat intro. unf.
    assert (PP1 := H1).
    apply H in H1.
    unf.
    rewrite H2. simpl.
    apply H in H2.
    apply H2 in PP1; cut. unf.
    assert (exists xx, P2 x1 xx /\ phiImplies xx pr).
      admit.
    unf.
    assert (PP2 := H5).
    apply H0 in H5. unf.
    inv H0. inv H9.
    eapply H10 in H7. unf. eex.
    repeat intro. inv H9. assumption.
  - destruct GP1 eqn: GP1e; cut.
    simpl in *.
    unf.
    apply H in GP1e.
    apply H0 in H1.
    unf.
    apply GP1e in H3; auto. unf.
    assert (exists xx, P2 x0 xx /\ phiImplies xx pr).
      admit.
    clear H5.
    unf.
    apply H1 in H6; auto. unf.
    assert (phiImplies x2 pr).
      eapp phiImpliesTrans.
    eex.
  - repeat intro.
    destruct GP1 eqn: GP1e; cut.
    simpl in *.
    eapply H in GP1e; eauto. unf.
    eapply H0 in H2; eauto. unf.
    eex.
    rewrite H4. assumption.
Admitted.












(* move upwards *)
Definition swap {T U: Type} (p : prod T U) : prod U T := (snd p, fst p).
  
Lemma xSubstsSwap : forall m x,
  NoDup (map snd m) ->
  ~ In x (map snd m) ->
  xSubsts (map swap m) (xSubsts m x) = x.
Proof.
  induction m; intros; cut.
  rename H0 into ii.
  simpl in *.
  inv H.
  apply (IHm x) in H3. clear IHm. Focus 2. apply not_or_and in ii. unf. assumption.
  unfold xSubsts in *.
  destruct a.
  simpl in *.
  dec (x_dec x x0).
  - dec (x_dec x1 x1).
    auto.
  - rename de2 into de4.
    destruct (find (λ r0, if x_dec x (fst r0) then true else false) m) eqn: ee.
    * destruct p0.
      subst.
      dec (x_dec x3 x1); cut.
      contradict H2.
      apply find_some in ee. unf.
      apply in_map_iff. eex. auto.
    * dec (x_dec x x1); cut.
      contradict ii.
      auto.
Qed.
  
Lemma eSubstsSwap : forall m e,
  NoDup (map snd m) ->
  disjoint (map snd m) (FVe e) ->
  eSubsts (map swap m) (eSubsts m e) = e.
Proof.
  induction e; intros; simpl in *.
  - auto.
  - specialize (H0 x).
    inv H0.
    * rewrite xSubstsSwap; auto.
    * contradict H1.
      apply in_eq.
  - rewrite IHe; auto.
Qed.

Lemma phi'SubstsSwap : forall m p1 p2,
  NoDup (map snd m) ->
  disjoint (map snd m) (FV' p1) ->
  phi'Substs m p1 = p2 ->
  phi'Substs (map swap m) p2 = p1.
Proof.
  intros.
  destruct p1, p2; cut;
  simpl in *; inv H1.
  - apply disjointSplitB in H0. unf.
    rewrite eSubstsSwap; auto.
    rewrite eSubstsSwap; auto.
  - apply disjointSplitB in H0. unf.
    rewrite eSubstsSwap; auto.
    rewrite eSubstsSwap; auto.
  - rewrite eSubstsSwap; auto.
Qed.

Lemma phiSubstsSwap : forall m p1 p2,
  NoDup (map snd m) ->
  disjoint (map snd m) (FV p1) ->
  phiSubsts m p1 = p2 ->
  phiSubsts (map swap m) p2 = p1.
Proof.
  induction p1; destruct p2; intros; cut.
  inv H1.
  simpl in *.
  apply disjointSplitB in H0. unf.
  rewrite IHp1; auto.
  erewrite phi'SubstsSwap; auto.
Qed.







Lemma gGoodFalseGood : forall p,
  gGood (false, p) <-> good p.
Proof.
  split; intros.
  - inv H.
    inv H1; cut.
  - split; try apply H.
    unfold sfrmgphi.
    apply or_intror.
    apply H.
Qed.

Lemma gGammaGood : forall gp p,
  gGood gp ->
  gGamma' gp p ->
  good p.
Proof.
  intros.
  unfold gGamma' in H0.
  destruct gp. simpl in *.
  destruct b; cut.
  subst.
  rewriteRev gGoodFalseGood.
  assumption.
Qed.




Lemma GLIFT_liftablex : forall P,
  liftable P ->
  GLIFTpp1x P (simpleLift P).
Proof.
  intros.
  apply (GLIFT_liftable P); apply H.
Qed.

Lemma simpleLift2lift : forall P,
  liftable P ->
  forall p1 p2,
    simpleLift P p1 p2 -> 
    gAlpha (PLIFTp1 P (gGamma' p1)) p2.
Proof.
  intros.
  assert (H' := H).
  apply GLIFT_liftablex in H.
  eapply H; eauto.
  eca.
  apply H0.
Qed.

(* HNewObj *)
Inductive HNewObjX : x -> C -> 
              Gamma -> phi -> phi -> Prop :=
| HNewObj : forall G(*\Gamma*) phi(*\*) phi'(*\*) phi'' x (C : C) f_bar(*\overline{f}*),
    liftableWOvar x phi phi' ->
    hasStaticType G (ex x) (TClass C) ->
    fieldsNames C = Some f_bar ->
    liftableAppend (phiNeq (ex x) (ev vnull) :: accListApp x f_bar)
      phi' phi'' ->
    HNewObjX x C
      G
      phi
      phi''
.

Inductive GHNewObjX : x -> C -> 
              Gamma -> gphi -> gphi -> Prop :=
| GHNewObj : forall G(*\Gamma*) phi(*\*) phi'(*\*) phi'' x (C : C) f_bar(*\overline{f}*),
    simpleLift (liftableWOvar x) phi phi' ->
    hasStaticType G (ex x) (TClass C) ->
    fieldsNames C = Some f_bar ->
    simpleLift (liftableAppend (phiNeq (ex x) (ev vnull) :: accListApp x f_bar))
      phi' phi'' ->
    GHNewObjX x C
      G
      phi
      phi''
.

Theorem GLIFT_GHNewObjX : forall x C  G,
  GLIFTpp1 (HNewObjX x C G) (GHNewObjX x C G).
Proof.
  unfold GLIFTpp1.
  intros.
  
  inv H.
  inv H1.
  
  set (app := (phiNeq (ex x) (ev vnull) :: accListApp x f_bar)) in *.
  
  assert (gGood gp2') as g1.
    apply H5.
  assert (gGood phi') as g2.
    apply H.
  assert (gGood gp2) as g3.
    inv H0.
    assumption.
  
  eexists. eexists.
  split. eca.
  split. eca.
  
  assert (lt := liftableTrans
    (liftableWOvar x)
    (liftableAppend app)
    (liftableWOvar_ x)
    (liftableAppend_ app)).
  assert (simpleLift (λ x1 x3, ∃ x2,
        liftableWOvar x x1 x2 ∧ liftableAppend app x2 x3) gp1 gp2')
  as sl.
    unfold simpleLift in *. unf.
    splau.
    splau.
  
  apply simpleLift2lift in sl; auto.
  
  split.
  - inv sl.
    apply H8. auto.
    inv H0.
    repeat intro.
    apply H11.
    unfold PLIFTp1 in *.
    unf.
    eex.
    eca.
  - inv H0.
    apply H8. auto.
    inv sl.
    repeat intro.
    apply H10.
    unfold PLIFTp1 in *.
    unf.
    eex.
    inv H14.
    exists phi'0.
    
    rewrite H16 in H4. inv H4.
    auto.
Qed.


(* HFieldAssign *)
Inductive HFieldAssignX : x -> f -> x -> 
              Gamma -> phi -> phi -> Prop :=
| HFieldAssign : forall G(*\Gamma*) phi(*\*) phi'(*\*) phi'' (x y : x) (f : f) C T,
    liftableWOacc (ex x, f) phi phi' ->
    phiImplies phi [phiAcc (ex x) f] ->
    hasStaticType G (ex x) (TClass C) ->
    hasStaticType G (ex y) T ->
    fieldHasType C f T ->
    liftableAppend (phiAcc (ex x) f ::
       phiNeq (ex x) (ev vnull) ::
       phiEq (edot (ex x) f) (ex y) :: [])
      phi' phi'' ->
    HFieldAssignX x f y
      G
      phi
      phi''
.

Inductive GHFieldAssignX : x -> f -> x -> 
              Gamma -> gphi -> gphi -> Prop :=
| GHFieldAssign : forall G(*\Gamma*) phi(*\*) phi'(*\*) phi'' (x y : x) (f : f) C T,
    simpleLift (liftableWOacc (ex x, f)) phi phi' ->
    gphiImplies phi [phiAcc (ex x) f] ->
    hasStaticType G (ex x) (TClass C) ->
    hasStaticType G (ex y) T ->
    fieldHasType C f T ->
    simpleLift (liftableAppend (phiAcc (ex x) f ::
       phiNeq (ex x) (ev vnull) ::
       phiEq (edot (ex x) f) (ex y) :: []))
      phi' phi'' ->
    GHFieldAssignX x f y
      G
      phi
      phi''
.

Theorem GLIFT_GHFieldAssignX : forall x f y  G,
  GLIFTpp1 (HFieldAssignX x f y G) (GHFieldAssignX x f y G).
Proof.
  unfold GLIFTpp1.
  intros.
  
  inv H.
  inv H1.
  
  set (app := [phiAcc (ex x) f; phiNeq (ex x) (ev vnull);
          phiEq (edot (ex x) f) (ex y)]) in *.
  
  assert (gGood gp2') as g1.
    apply H7.
  assert (gGood phi') as g2.
    apply H.
  assert (gGood gp2) as g3.
    inv H0.
    assumption.
  
  eexists. eexists.
  split. eca.
  split. eca.
  
  assert (lt := liftableTrans
    (liftableWOacc (ex x, f))
    (liftableAppend app)
    (liftableWOacc_ _)
    (liftableAppend_ _)).
  assert (simpleLift (λ x1 x3, ∃ x2,
        liftableWOacc (ex x, f) x1 x2 ∧ liftableAppend app x2 x3) gp1 gp2')
  as sl.
    unfold simpleLift in *. unf.
    splau.
    splau.
  
  apply simpleLift2lift in sl; auto.
  
  split.
  - inv sl.
    apply H10. auto.
    inv H0.
    repeat intro.
    apply H13.
    unfold PLIFTp1 in *.
    unf.
    eex.
    eca.
    apply H16.
  - inv H0.
    apply H10. auto.
    inv sl.
    repeat intro.
    apply H12.
    unfold PLIFTp1 in *.
    unf.
    eex.
    inv H16.
    exists phi'0.
    auto.
Qed.


(* HVarAssign *)
Inductive HVarAssignX : x -> e -> 
              Gamma -> phi -> phi -> Prop :=
| HVarAssign : forall G(*\Gamma*) T phi(*\*) phi'(*\*) phi'' phi''' (x : x) (e : e),
    liftableWOvar x phi phi' ->
    NotIn x (FVe e) ->
    hasStaticType G (ex x) T ->
    hasStaticType G e T ->
    liftableImplies (unfoldAcc e)
      phi' phi'' ->
    liftableAppend [phiEq (ex x) e] 
      phi'' phi''' ->
    HVarAssignX x e
      G
      phi
      phi'''
.

Inductive GHVarAssignX : x -> e -> 
              Gamma -> gphi -> gphi -> Prop :=
| GHVarAssign : forall G(*\Gamma*) T phi(*\*) phi'(*\*) phi'' phi''' (x : x) (e : e),
    simpleLift (liftableWOvar x) phi phi' ->
    NotIn x (FVe e) ->
    hasStaticType G (ex x) T ->
    hasStaticType G e T ->
    gphiImplies phi' (unfoldAcc e) ->
    simpleLift (liftableImplies (unfoldAcc e))
      phi' phi'' ->
    simpleLift (liftableAppend [phiEq (ex x) e])
      phi'' phi''' ->
    GHVarAssignX x e
      G
      phi
      phi'''
.

Theorem GLIFT_GHVarAssignX : forall x e  G,
  GLIFTpp1 (HVarAssignX x e G) (GHVarAssignX x e G).
Proof.
  unfold GLIFTpp1.
  intros.
  
  inv H.
  inv H1.
  
  set (app := [phiEq (ex x) e]) in *.
  
  assert (gGood gp2') as g1.
    apply H8.
  assert (gGood phi') as g2.
    apply H.
  assert (gGood phi'') as g3.
    apply H7.
  assert (gGood gp2) as g4.
    inv H0.
    assumption.
  
  eexists. eexists.
  split. eca.
  split. eca.
  
  set (op1 := liftableWOvar x) in *.
  set (op2 := liftableImplies (unfoldAcc e)) in *.
  set (op3 := liftableAppend app) in *.
  
  assert (lt12 := liftableTrans
    op1
    op2
    (liftableWOvar_ _)
    (liftableImplies_ _)).
  set (op12 := (λ x1 x3 : phi, ∃ x2 : phi, op1 x1 x2 ∧ op2 x2 x3)) in *.
  assert (lt123 := liftableTrans
    op12
    op3
    lt12
    (liftableAppend_ _)).
  set (op123 := (λ x1 x3 : phi, ∃ x2 : phi, op12 x1 x2 ∧ op3 x2 x3)) in *.
  
  assert (simpleLift op123 gp1 gp2')
  as sl.
    unfold simpleLift in *. unf.
    splau.
    splau.
    splau.
    unfold op123.
    exists (snd phi''). splau.
    exists (snd phi'). splau.
  
  apply simpleLift2lift in sl; auto.
  
  split.
  - inv sl.
    apply H11. auto.
    inv H0.
    repeat intro.
    apply H14.
    unfold PLIFTp1 in *.
    unf.
    eex. inv H17. unf. inv H17. unf.
    eca.
  - inv H0.
    apply H11. auto.
    inv sl.
    repeat intro.
    apply H13.
    unfold PLIFTp1 in *.
    unf.
    eex.
    inv H17.
    exists phi''0. splau.
    exists phi'0. splau.
Qed.


(* HReturn *)
Inductive HReturnX : x ->
              Gamma -> phi -> phi -> Prop :=
| HReturn : forall G(*\Gamma*) phi(*\*) phi'(*\*) phi'' (x : x) T,
    liftableWOvar xresult phi phi' ->
    hasStaticType G (ex x) T ->
    hasStaticType G (ex xresult) T ->
    liftableAppend [phiEq (ex xresult) (ex x)] 
      phi' phi'' ->
    HReturnX x
      G
      phi 
      phi''
.

Inductive GHReturnX : x ->
              Gamma -> gphi -> gphi -> Prop :=
| GHReturn : forall G(*\Gamma*) phi(*\*) phi'(*\*) phi'' (x : x) T,
    simpleLift (liftableWOvar xresult) phi phi' ->
    hasStaticType G (ex x) T ->
    hasStaticType G (ex xresult) T ->
    simpleLift (liftableAppend [phiEq (ex xresult) (ex x)])
      phi' phi'' ->
    GHReturnX x
      G
      phi 
      phi''
.

Theorem GLIFT_GHReturnX : forall x  G,
  GLIFTpp1 (HReturnX x G) (GHReturnX x G).
Proof.
  unfold GLIFTpp1.
  intros.
  
  inv H.
  inv H1.
  
  set (app := [phiEq (ex xresult) (ex x)]) in *.
  
  assert (gGood gp2') as g1.
    apply H5.
  assert (gGood phi') as g2.
    apply H.
  assert (gGood gp2) as g3.
    inv H0.
    assumption.
  
  eexists. eexists.
  split. eca.
  split. eca.
  
  assert (lt := liftableTrans
    (liftableWOvar xresult)
    (liftableAppend app)
    (liftableWOvar_ _)
    (liftableAppend_ _)).
  assert (simpleLift (λ x1 x3, ∃ x2,
        liftableWOvar xresult x1 x2 ∧ liftableAppend app x2 x3) gp1 gp2')
  as sl.
    unfold simpleLift in *. unf.
    splau.
    splau.
  
  apply simpleLift2lift in sl; auto.
  
  split.
  - inv sl.
    apply H8. auto.
    inv H0.
    repeat intro.
    apply H11.
    unfold PLIFTp1 in *.
    unf.
    eex.
    eca.
  - inv H0.
    apply H8. auto.
    inv sl.
    repeat intro.
    apply H10.
    unfold PLIFTp1 in *.
    unf.
    eex.
    inv H14.
    exists phi'0.
    auto.
Qed.


(* HApp *)
(* Inductive HAppX : T -> m -> T -> x' -> gphi -> gphi ->
              Gamma -> phi -> phi -> Prop :=
| HApp : forall G(*\Gamma*) phiTMP phi(*\phi*) phi_p(*\*) phi'(*\*) phi'' phi_q(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
    hasStaticType G (ex y) (TClass C) ->
    hasStaticType G (ex x) T_r ->
    hasStaticType G (ex z') T_p ->
    phiImplies phi (phiNeq (ex y) (ev vnull) :: phi_p) ->
    liftableWOvar xresult phi phiTMP ->
    liftableWOaccs (staticFootprint phi_p) phiTMP phi' ->
    listDistinct [x ; y ; z'] ->
    liftablePS2 xthis y (xUserDef z) z' 
      phi_pre phi_p ->
    liftablePS3 xthis y (xUserDef z) z' xresult x 
      phi_post phi_q ->
    liftableAppend phi_q
      phi' phi'' ->
    HAppX T_r m T_p z (false, phi_pre) (false, phi_post)
      G
      phi
      phi''
.

Inductive GHAppX : T -> m -> T -> x' -> gphi -> gphi ->
              Gamma -> gphi -> gphi -> Prop :=
| GHApp : forall G(*\Gamma*) phi''' phiTMP phi(*\phi*) phi_p(*\*) phi'(*\*) phi'' phi_q(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
    hasStaticType G (ex y) (TClass C) ->
    hasStaticType G (ex x) T_r ->
    hasStaticType G (ex z') T_p ->
    gphiImplies phi (phiNeq (ex y) (ev vnull) :: (snd phi_p)) ->
    simpleLift (liftableWOvar xresult) phi phiTMP ->
    simpleLift (liftableWOaccs (staticFootprint phi_p)) phiTMP phi' ->
    listDistinct [x ; y ; z'] ->
    simpleLift (liftablePS2 xthis y (xUserDef z) z')
      phi_pre phi_p ->
    simpleLift (liftablePS3 xthis y (xUserDef z) z' xresult x)
      phi_post phi_q ->
    simpleLift (liftableAppend (snd phi_p))
      phi' phi'' ->
    phi''' = (fst phi'' || fst phi_p, snd phi'') ->
    GHAppX T_r m T_p z (false, phi_pre) (false, phi_post)
      G
      phi
      phi'''
. *)


Inductive XHAppX : T -> m -> T -> x' -> x -> x -> x ->
              Gamma -> phi -> phi -> phi -> phi -> Prop :=
| XHApp : forall G(*\Gamma*) phi(*\phi*) phi' phi'' phi_p(*\*) phi_q(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
    (*method information*)
    good phi_pre ->
    good phi_post ->
    
    hasStaticType G (ex y) (TClass C) ->
    hasStaticType G (ex x) T_r ->
    hasStaticType G (ex z') T_p ->
    liftableImplies (phiNeq (ex y) (ev vnull) :: phi_p)
      phi phi' ->
    listDistinct [x ; y ; z'] ->
    liftablePS2 xthis y (xUserDef z) z'
      phi_pre phi_p ->
    liftablePS3 xthis y (xUserDef z) z' xresult x 
      phi_post phi_q ->
    liftableAppend phi_q
      phi' phi'' ->
    XHAppX T_r m T_p z x y z'
      G
      phi
      phi_pre 
      phi_post 
      phi''
.

Inductive GXHAppX : T -> m -> T -> x' -> x -> x -> x ->
              Gamma -> gphi -> gphi -> gphi -> gphi -> Prop :=
| GXHApp : forall G(*\Gamma*) phi(*\phi*) phi' phi'' phi_p(*\*) phi_q(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
    (*method information*)
    gGood phi_pre ->
    gGood phi_post ->
    
    hasStaticType G (ex y) (TClass C) ->
    hasStaticType G (ex x) T_r ->
    hasStaticType G (ex z') T_p ->
    simpleLift (liftableImplies (phiNeq (ex y) (ev vnull) :: snd phi_p))
      phi phi' ->
    listDistinct [x ; y ; z'] ->
    simpleLift (liftablePS2 xthis y (xUserDef z) z')
      phi_pre phi_p ->
    simpleLift (liftablePS3 xthis y (xUserDef z) z' xresult x)
      phi_post phi_q ->
    simpleLift (liftableAppend (snd phi_q))
      phi' phi'' ->
    GXHAppX T_r m T_p z x y z'
      G
      phi
      phi_pre 
      phi_post 
      (fst phi'' || fst phi_p || fst phi_q, snd phi'')
.

Theorem GLIFT_GXHAppX : forall T_r m T_p z x y z'  G,
  GLIFTpp3 (XHAppX  T_r m T_p z x y z' G) 
           (GXHAppX T_r m T_p z x y z' G).
Proof.
  unfold GLIFTpp3.
  intros.
  
  inv H.
  inv H0.
  inv H1.
  inv H3.
  
  assert (gGood phi_p) as g0.
    apply H11.
  assert (gGood phi_q) as g1.
    apply H12.
  assert (gGood phi') as g2.
    apply H9.
  assert (gGood phi'') as g3.
    apply H13.
  assert (gGood gpx) as g4.
    inv H2.
    assumption.
  
  eexists. eexists.
  split. eca.
    inv g3.
    eca.
    inv H14.
      rewrite H15. eca.
    apply or_intror.
    assumption.
  split. eca.
  
  set (op1 := liftableImplies (phiNeq (ex y) (ev vnull) :: snd phi_p)) in *.
  set (op2 := liftableAppend (snd phi_q)) in *.
  
  assert (lt12 := liftableTrans
    op1
    op2
    (liftableImplies_ _)
    (liftableAppend_ _)).
(*   assert (lt123 := liftableTrans
    (λ x1 x3, ∃ x2, op1 x1 x2 ∧ op2 x2 x3)
    op3
    lt12
    (liftablePS3_ _ _ _ _ _ _)). *)
(*   simpl in *. *)
    
 (* assert (simpleLift (λ x1 x3 : phi,
           ∃ x2 : phi,
         (∃ x4 : phi, op1 x1 x4 ∧ op2 x4 x2) ∧ op3 x2 x3) phi_p gp2')
  as sl.
    unfold simpleLift in *. unf.
    splau.
    splau.
    splau. *)
  assert (simpleLift (λ x1 x3 : phi,
         (∃ x2 : phi, op1 x1 x2 ∧ op2 x2 x3)) gp1 phi'')
  as sl.
    unfold simpleLift in *. unf.
    splau.
    splau.
  
  apply simpleLift2lift in sl; auto.
  
(*   apply simpleLift2lift in sl1; auto.
  apply simpleLift2lift in sl1; auto. *)
  
  split.
  - inv sl.
    destruct phi''. simpl in *.
    destruct b; simpl.
    * apply H16. auto.
      repeat intro.
      inv H2.
      apply H20.
      unfold PLIFTp1 in *.
      unfold PLIFTp3 in *.
      unf.
      exists x0.
      exists (snd gp2).
      exists (snd gp3).
      splau.
      split. admit.
      split. admit.
      eca.
      + 
      eex.
      eca.
  - inv H0.
    apply H14. auto.
    repeat intro.
    inv sl.
    apply H17.
    unfold PLIFTp1 in *.
    unf.
    inv H20.
    assert (phi_q0 = phi_q).
      assert (li := liftablePS3_ xthis y (xUserDef z) z' xresult x).
      inv li. unf.
      inv H20.
      eapply H33; eauto.
    subst.
    assert (phi_p0 = phi_p).
      assert (li := liftablePS2_ xthis y (xUserDef z) z').
      inv li. unf.
      inv H20.
      eapply H33; eauto.
    subst.
    eex.
Qed.

Inductive HAppX : T -> m -> T -> x' -> phi -> phi -> x -> x -> x ->
              Gamma -> phi -> phi -> Prop :=
| HApp : forall G(*\Gamma*) phi(*\phi*) phi' phi'' phi_p(*\*) phi_q(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
    (*method information*)
    good phi_pre ->
    good phi_post ->
    
    hasStaticType G (ex y) (TClass C) ->
    hasStaticType G (ex x) T_r ->
    hasStaticType G (ex z') T_p ->
    liftableImplies (phiNeq (ex y) (ev vnull) :: phi_p)
      phi phi' ->
    listDistinct [x ; y ; z'] ->
    liftablePS2 xthis y (xUserDef z) z'
      phi_pre phi_p ->
    liftablePS3 xthis y (xUserDef z) z' xresult x 
      phi_post phi_q ->
    liftableAppend phi_q
      phi' phi'' ->
    HAppX T_r m T_p z phi_pre phi_post x y z'
      G
      phi
      phi''
.

Inductive GHAppX : T -> m -> T -> x' -> phi -> phi -> x -> x -> x ->
              Gamma -> gphi -> gphi -> Prop :=
| GHApp : forall G(*\Gamma*) phi(*\phi*) phi' phi'' phi_p(*\*) phi_q(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
    (*method information*)
    good phi_pre ->
    good phi_post ->
    
    hasStaticType G (ex y) (TClass C) ->
    hasStaticType G (ex x) T_r ->
    hasStaticType G (ex z') T_p ->
    simpleLift (liftableImplies (phiNeq (ex y) (ev vnull) :: phi_p))
      phi phi' ->
    listDistinct [x ; y ; z'] ->
    liftablePS2 xthis y (xUserDef z) z'
      phi_pre phi_p ->
    liftablePS3 xthis y (xUserDef z) z' xresult x
      phi_post phi_q ->
    simpleLift (liftableAppend phi_q)
      phi' phi'' ->
    GHAppX T_r m T_p z phi_pre phi_post x y z'
      G
      phi
      phi''
.

Theorem GLIFT_GHAppX : forall T_r m T_p z p_pre p_post x y z'  G,
  GLIFTpp1 (HAppX  T_r m T_p z p_pre p_post x y z' G) 
           (GHAppX T_r m T_p z p_pre p_post x y z' G).
Proof.
  unfold GLIFTpp1.
  intros.
  
  inv H.
  inv H1.
  
  assert (gGood (false, phi_q)) as g1.
    apply gGoodFalseGood.
    assert (li := liftablePS3_ xthis y (xUserDef z) z' xresult x).
    inv li. unf. inv H1. apply H12 in H10; auto.
  assert (gGood (false, p_post)) as g2.
    apply gGoodFalseGood. assumption.
  assert (gGood gp2') as g3.
    apply H11.
  assert (gGood (false, p_pre)) as g4.
    apply gGoodFalseGood. assumption.
  assert (gGood gp2) as g6.
    inv H0.
    assumption.
  
  eexists. eexists.
  split. eca.
  split. eca.
  
  set (op1 := liftableImplies (phiNeq (ex y) (ev vnull) :: phi_p)) in *.
  set (op2 := liftableAppend phi_q) in *.
  
  assert (lt12 := liftableTrans
    op1
    op2
    (liftableImplies_ _)
    (liftableAppend_ _)).
(*   assert (lt123 := liftableTrans
    (λ x1 x3, ∃ x2, op1 x1 x2 ∧ op2 x2 x3)
    op3
    lt12
    (liftablePS3_ _ _ _ _ _ _)). *)
(*   simpl in *. *)
    
 (* assert (simpleLift (λ x1 x3 : phi,
           ∃ x2 : phi,
         (∃ x4 : phi, op1 x1 x4 ∧ op2 x4 x2) ∧ op3 x2 x3) phi_p gp2')
  as sl.
    unfold simpleLift in *. unf.
    splau.
    splau.
    splau. *)
  assert (simpleLift (λ x1 x3 : phi,
         (∃ x2 : phi, op1 x1 x2 ∧ op2 x2 x3)) gp1 gp2')
  as sl.
    unfold simpleLift in *. unf.
    splau.
    splau.
  
  apply simpleLift2lift in sl; auto.
  
(*   apply simpleLift2lift in sl1; auto.
  apply simpleLift2lift in sl1; auto. *)
  
  split.
  - inv sl.
    apply H14. auto.
    repeat intro.
    inv H0.
    apply H18.
    unfold PLIFTp1 in *.
    unf.
    eex.
    eca.
  - inv H0.
    apply H14. auto.
    repeat intro.
    inv sl.
    apply H17.
    unfold PLIFTp1 in *.
    unf.
    inv H20.
    assert (phi_q0 = phi_q).
      assert (li := liftablePS3_ xthis y (xUserDef z) z' xresult x).
      inv li. unf.
      inv H20.
      eapply H33; eauto.
    subst.
    assert (phi_p0 = phi_p).
      assert (li := liftablePS2_ xthis y (xUserDef z) z').
      inv li. unf.
      inv H20.
      eapply H33; eauto.
    subst.
    eex.
Qed.



(* HAssert - old, non ideal way *)
(* Inductive HAssertX : phi ->
              Gamma -> phi -> phi -> Prop :=
| HAssert : forall G(*\Gamma*) phi(*\*) phi_a(*\*) phi' phi'',
    phiImplies phi phi_a -> (* implied by liftableWOaccsX *)
    liftableWOaccsX phi_a
      phi phi' ->
    liftableAppend phi_a
      phi' phi'' ->
    HAssertX phi_a
      G
      phi
      phi''
.

Inductive GHAssertX : phi ->
              Gamma -> gphi -> gphi -> Prop :=
| GHAssert : forall G(*\Gamma*) phi(*\*) phi_a(*\*) phi' phi'',
    gphiImplies phi phi_a -> (* implied by liftableWOaccsX *)
    simpleLift (liftableWOaccsX phi_a)
      phi phi' ->
    simpleLift (liftableAppend phi_a)
      phi' phi'' ->
    GHAssertX phi_a
      G
      phi 
      phi''
.

Theorem GLIFT_GHAssertX : forall p  G,
  GLIFTpp1 (HAssertX p G) (GHAssertX p G).
Proof.
  unfold GLIFTpp1.
  intros.
  
  inv H.
  inv H1.
  
  assert (gGood gp2') as g1.
    apply H4.
  assert (gGood phi') as g2.
    apply H3.
  assert (gGood gp2) as g3.
    inv H0.
    assumption.
  
  eexists. eexists.
  split. eca.
  split. eca.
  
  assert (lt := liftableTrans
    (liftableWOaccsX p0)
    (liftableAppend p0)
    (liftableWOaccsX_ _)
    (liftableAppend_ _)).
  assert (simpleLift (λ x1 x3, ∃ x2,
        liftableWOaccsX p0 x1 x2 ∧ liftableAppend p0 x2 x3) gp1 gp2')
  as sl.
    unfold simpleLift in *. unf.
    splau.
    splau.
  
  apply simpleLift2lift in sl; auto.
  
  split.
  - inv sl.
    apply H7. auto.
    inv H0.
    repeat intro.
    apply H10.
    unfold PLIFTp1 in *.
    unf.
    eex.
    eca.
    apply H13.
  - inv H0.
    apply H7. auto.
    inv sl.
    repeat intro.
    apply H9.
    unfold PLIFTp1 in *.
    unf.
    eex.
    inv H13.
    exists phi'0.
    auto.
Qed. *)

(* HAssert *)
Inductive HAssertX : phi ->
              Gamma -> phi -> phi -> Prop :=
| HAssert : forall G(*\Gamma*) phi(*\*) phi_a(*\*) phi',
    liftableImplies phi_a
      phi phi' ->
    HAssertX phi_a
      G
      phi
      phi'
.

Inductive GHAssertX : phi ->
              Gamma -> gphi -> gphi -> Prop :=
| GHAssert : forall G(*\Gamma*) phi(*\*) phi_a(*\*) phi',
    simpleLift (liftableImplies phi_a)
      phi phi' ->
    GHAssertX phi_a
      G
      phi 
      phi'
.

Theorem GLIFT_GHAssertX : forall p  G,
  GLIFTpp1 (HAssertX p G) (GHAssertX p G).
Proof.
  unfold GLIFTpp1.
  intros.
  
  inv H.
  inv H1.
  
  assert (gGood gp2') as g1.
    apply H.
  assert (gGood gp2) as g3.
    inv H0.
    assumption.
  
  eexists. eexists.
  split. eca.
  split. eca.
  
  rename H into sl.
  apply simpleLift2lift in sl; auto.
  Focus 2. apply liftableImplies_.
  
  split.
  - inv sl.
    apply H4. auto.
    inv H0.
    repeat intro.
    apply H7.
    unfold PLIFTp1 in *.
    unf.
    inv H10.
    eex.
  - inv H0.
    apply H4. auto.
    inv sl.
    repeat intro.
    apply H6.
    unfold PLIFTp1 in *.
    unf.
    inv H10. inv H9.
    eex.
Qed.


(* HRelease *)
Inductive HReleaseX : phi ->
              Gamma -> phi -> phi -> Prop :=
| HRelease : forall G(*\Gamma*) phi(*\*) phi_a(*\*) phi',
    phiImplies phi phi_a -> (* implied by liftableWOaccsX *)
    liftableWOaccsX phi_a
      phi phi' ->
    HReleaseX phi_a
      G
      phi
      phi'
.

Inductive GHReleaseX : phi ->
              Gamma -> gphi -> gphi -> Prop :=
| GHRelease : forall G(*\Gamma*) phi(*\*) phi_a(*\*) phi',
    gphiImplies phi phi_a -> (* implied by liftableWOaccsX *)
    simpleLift (liftableWOaccsX phi_a)
      phi phi' ->
    GHReleaseX phi_a
      G
      phi 
      phi'
.

Theorem GLIFT_GHReleaseX : forall p  G,
  GLIFTpp1 (HReleaseX p G) (GHReleaseX p G).
Proof.
  unfold GLIFTpp1.
  intros.
  
  inv H.
  inv H1.
  
  assert (gGood gp2') as g1.
    apply H3.
  assert (gGood gp2) as g3.
    inv H0.
    assumption.
  
  eexists. eexists.
  split. eca.
  split. eca.
  
  rename H3 into sl.
  apply simpleLift2lift in sl; auto.
  Focus 2. apply liftableWOaccsX_.
  
  split.
  - inv sl.
    apply H5. auto.
    inv H0.
    repeat intro.
    apply H8.
    unfold PLIFTp1 in *.
    unf.
    eex; apply H11.
  - inv H0.
    apply H5. auto.
    inv sl.
    repeat intro.
    apply H7.
    unfold PLIFTp1 in *.
    unf.
    inv H11.
    eex.
    apply H12.
Qed.


(* HDeclare *)
Inductive HDeclareX : (Gamma -> list s -> phi -> phi -> Prop) -> T -> x -> list s ->
              Gamma -> phi -> phi -> Prop :=
| HDeclare : forall (ff : Gamma -> list s -> phi -> phi -> Prop) phi'' ss(*\overline{s}*) G(*\Gamma*) phi(*\*) phi'(*\*) x T,
    GammaNotSetAt G x ->
    liftableAppend [phiEq (ex x) (ev (defaultValue' T))]
      phi phi'' ->
    ff (GammaSet x T G) ss
      phi''
      phi' ->
    HDeclareX ff T x ss
      G
      phi
      phi'
.

Inductive GHDeclareX : (Gamma -> list s -> phi -> phi -> Prop) -> T -> x -> list s ->
              Gamma -> gphi -> gphi -> Prop :=
| GHDeclare : forall (ff : Gamma -> list s -> phi -> phi -> Prop) phi'' ss(*\overline{s}*) G(*\Gamma*) phi(*\*) phi'(*\*) x T,
    GammaNotSetAt G x ->
    simpleLift (liftableAppend [phiEq (ex x) (ev (defaultValue' T))])
      phi phi'' ->
    simpleLift (ff (GammaSet x T G) ss)
      phi''
      phi' ->
    GHDeclareX ff T x ss
      G
      phi
      phi'
.

Theorem GLIFT_GHDeclareX : forall ff T x ss  G,
  liftable (ff (GammaSet x T G) ss) ->
  GLIFTpp1 (HDeclareX ff T x ss G) (GHDeclareX ff T x ss G).
Proof.
  unfold GLIFTpp1.
  intros.
  
  inv H0.
  inv H2.
  
  set (app := [phiEq (ex x) (ev (defaultValue' T))]) in *.
  
  assert (gGood gp2') as g1.
    apply H5.
  assert (gGood phi'') as g2.
    apply H4.
  assert (gGood gp2) as g3.
    inv H1.
    assumption.
  
  eexists. eexists.
  split. eca.
  split. eca.
  
  assert (lt := liftableTrans
    (liftableAppend app)
    (ff (GammaSet x T G) ss)
    (liftableAppend_ _)
    H).
  assert (simpleLift (λ x1 x3, ∃ x2,
        liftableAppend app x1 x2 ∧ ff (GammaSet x T G) ss x2 x3) gp1 gp2')
  as sl.
    unfold simpleLift in *. unf.
    splau.
    splau.
  
  apply simpleLift2lift in sl; auto.

  split.
  - inv sl.
    apply H8. auto.
    inv H1.
    repeat intro.
    apply H11.
    unfold PLIFTp1 in *.
    unf.
    eex.
    eca.
  - inv H1.
    apply H8. auto.
    inv sl.
    repeat intro.
    apply H10.
    unfold PLIFTp1 in *.
    unf.
    inv H14.
    eex.
Qed.


(* HSec *)
Inductive HSecX : (Gamma -> list s -> phi -> phi -> Prop) -> list s ->
              Gamma -> phi -> phi -> Prop :=
| HSec : forall (ff : Gamma -> list s -> phi -> phi -> Prop) s1 s2 G(*\Gamma*) p q r,
    ff G [s1]
      p
      q ->
    ff G s2
      q
      r ->
    HSecX ff ([s1] ++ s2)
      G
      p
      r
.

Inductive GHSecX : (Gamma -> list s -> phi -> phi -> Prop) -> list s ->
              Gamma -> gphi -> gphi -> Prop :=
| GHSec : forall (ff : Gamma -> list s -> phi -> phi -> Prop) s1 s2 G(*\Gamma*) p q r,
    simpleLift (ff G [s1])
      p
      q ->
    simpleLift (ff G s2)
      q
      r ->
    GHSecX ff ([s1] ++ s2)
      G
      p
      r
.

Theorem GLIFT_GHSecX : forall ff s  G,
  (forall s, liftable (ff G s)) ->
  GLIFTpp1 (HSecX ff s G) (GHSecX ff s G).
Proof.
  unfold GLIFTpp1.
  intros.
  
  inv H0.
  inv H2.
  
  assert (gGood q) as g1.
    apply H0.
  assert (gGood gp2') as g2.
    apply H4.
  assert (gGood gp2) as g3.
    inv H1.
    assumption.
  
  eexists. eexists.
  split. eca.
  split. eca.
  
  assert (lt := liftableTrans
    (ff G [s1])
    (ff G s2)
    (H _)
    (H _)).
  assert (simpleLift (λ x1 x3, ∃ x2,
        ff G [s1] x1 x2 ∧ ff G s2 x2 x3) gp1 gp2')
  as sl.
    unfold simpleLift in *. unf.
    splau.
    splau.
  
  apply simpleLift2lift in sl; auto.

  split.
  - inv sl.
    apply H7. auto.
    inv H1.
    repeat intro.
    apply H10.
    unfold PLIFTp1 in *.
    unf.
    eex.
    eca.
  - inv H1.
    apply H7. auto.
    inv sl.
    repeat intro.
    apply H9.
    unfold PLIFTp1 in *.
    unf.
    inv H13.
    eex.
Qed.


(* APP *)
Inductive hoareAppX : Gamma -> T -> T -> x -> phi -> phi -> phi -> phi -> Prop :=
| HX'App : forall G(*\Gamma*) phi(*\phi*) phi_p(*\*) phi_q(*\*) T_r T_p z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
        incl (FV phi_pre) [xUserDef z ; xthis] ->
        incl (FV phi_post) [xUserDef z ; xthis ; xresult] ->
        sfrmphi [] phi_pre ->
        sfrmphi [] phi_post ->
    hasStaticType G (ex x) T_r ->
    hasStaticType G (ex z') T_p ->
    phiImplies phi (phiNeq (ex y) (ev vnull) :: phi_p) ->
    listDistinct [x ; y ; z'] ->
    phi_p = phiSubsts2 xthis y (xUserDef z) z' phi_pre ->
    phi_q = phiSubsts3 xthis y (xUserDef z) z' xresult x phi_post ->
    hoareAppX G T_r T_p z' phi_pre phi_post phi phi_q
.

Inductive hoareGAppX : Gamma -> T -> T -> x -> gphi -> gphi -> gphi -> gphi -> Prop :=
| HX'GApp : forall G(*\Gamma*) phi(*\phi*) phi_p(*\*) phi_q(*\*) T_r T_p z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
        incl (FV (snd phi_pre)) [xUserDef z ; xthis] ->
        incl (FV (snd phi_post)) [xUserDef z ; xthis ; xresult] ->
        sfrmgphi [] phi_pre ->
        sfrmgphi [] phi_post ->
    hasStaticType G (ex x) T_r ->
    hasStaticType G (ex z') T_p ->
    gphiImplies phi (fst phi_p, phiNeq (ex y) (ev vnull) :: snd phi_p) ->
    listDistinct [x ; y ; z'] ->
    phi_p = (fst phi_pre, phiSubsts2 xthis y (xUserDef z) z' (snd phi_pre)) ->
    phi_q = (fst phi_post, phiSubsts3 xthis y (xUserDef z) z' xresult x (snd phi_post)) ->
    hoareGAppX G T_r T_p z' phi_pre phi_post phi phi_q
.

Theorem GLIFT_eq : forall G Tr Tp p p1 p2 p3 p4,
  gGood p1 ->
  gGood p2 ->
  gGood p3 ->
  gGood p4 ->
  hoareGAppX        G Tr Tp p  p1 p2 p3 p4 <-> 
  GLIFT4 (hoareAppX G Tr Tp p) p1 p2 p3 p4.
Proof.
  unfold
    GLIFT4, PLIFT4, gGamma', sfrmgphi,
    gphiSatisfiable, NotIn,
    phiIsIndependentVar.
  split;
  rename H into gps1;
  rename H0 into gps2;
  rename H1 into gps3;
  rename H2 into gps4;
  intros.
  - inversionx H.
    do 4 eexists. simpl in *.
    split. eca.
    split. eca.
    split. eca.
    split. eca.
    inversionx gps1.
    apply hasWellFormedSubtype in H.
    inversionx gps2.
    apply hasWellFormedSubtype in H9.
    inversionx gps3.
    apply hasWellFormedSubtype in H11.
    inversionx gps4.
    apply hasWellFormedSubtype in H13.
    unf.
    simpl in *.
    exists (if fst p1 then x3 else snd p1).
    exists (if fst p2 then x2 else snd p2).
    exists (if fst p3 then x1 else snd p3).
    exists (if fst p2 then x0 else snd p4).
    unfold gGamma'.
    destruct p1, p2, p3, p4. simpl in *.
    split. destruct b; auto. split; auto. eca.
    split. destruct b0; auto. split; auto. eca.
    split. destruct b1; auto. split.
      eca. admit. repeat eca.
      eappIn phiImpliesTrans H27.
      rewrite cons2app. eapp phiImpliesSuffix.
    split. destruct b2; auto. split; auto. eca.
    eca.
    * destruct b;
      try rewriteRev H19;
      eauto.
    * destruct b0;
      try rewriteRev H22;
      eauto.
    * destruct b;
      eauto.
      inversionx H2; try tauto; try discriminate.
    * destruct b0;
      eauto.
      inversionx H3; try tauto; try discriminate.
    * destruct b1; auto.
      rewrite cons2app. eapp phiImpliesPrefix.
      admit.
    * repeat eca.
    * admit.
    * admit.
  - unf.
    inversionx H8.
    inversionx H0.
    inversionx H.
    inversionx H1.
    inversionx H2.
    eca.
    * admit.
    * admit.
    * apply H8.
    * apply H0.
    * destruct p3.
      destruct b; unfold gphiImplies; simpl.
      + exists x5.
        inversionx H5.
        auto.
      + inversionx H5.
        auto.
    * destruct p3.
      destruct b; unfold gphiImplies; simpl.
      + exists x5.
        inversionx H5.
        split; auto.
        split; auto.
        eauto.
        destruct p1.
        simpl in *.
        destruct b; inversionx H3;
        unfold dividex, divideTrue in *; simpl in *; eauto.
        admit.
      + inversionx H5.
        destruct p1.
        simpl in *.
        destruct b; inversionx H3;
        unfold dividex, divideTrue in *; simpl in *; eauto.
        admit.
    * unfold gdividex.
      simpl.
      unfold sfrmgphi.
      destruct (fst p3 || fst p1); auto.
    * simpl in *.
      unfold dividex, divideTrue in *.
      rewrite app_nil_r in *.
      destruct p2, p3, p1, p4.
      simpl in *.
      unfold gphiImplies.
      destruct (b || (b0 || b1)) eqn: ee; simpl.
      + exists x6.
        destruct b2;
        inversionx H6; simpl in *.
          split; auto.
Admitted.



(* INTERIORS *)
Definition interior : Type := phi -> phi -> Prop.
Definition interiorCreate (pp1 pp2 : pphi) : interior :=
  fun p1 p2 => pp1 p1 /\ pp2 p2.
Definition interiorGCreate (gp1 gp2 : gphi) : interior :=
  interiorCreate (gGamma gp1) (gGamma gp2).
Definition interiorProp (prop : phi -> phi -> Prop) : interior :=
  prop.
Definition interiorIntersect (i1 i2 : interior) : interior :=
  fun a b => i1 a b /\ i2 a b.

Definition interiorInner (prop : phi -> phi -> Prop) (gp1 gp2 : gphi) : interior :=
  interiorIntersect
    (interiorProp prop)
    (interiorGCreate gp1 gp2).

(* Definition interiorEq : interior := fun p1 p2 => p1 = p2.
Definition interiorJoin (i1 i2 : interior) : interior :=
  fun a b => exists c, i1 a c /\ i2 c b.
  
Definition interiorHoareSingle (s : s) := fun p1 p2 => hoareSingle p1 s p2.
Definition interiorHoare (s : list s) :=
  fold_right interiorJoin interiorEq (map interiorHoareSingle s).
 *)

(* phi equality *)
Inductive geq : gphi -> gphi -> Prop :=
| geqStatic : forall p1 p2,
  p1 = p2 ->
  geq (false, p1) (false, p2)
| geqGradual : forall gp1 gp2,
  fst gp1 || fst gp2 = true ->
  gphiImplies gp1 gp2 ->
  gphiImplies gp2 gp1 ->
  geq gp1 gp2
.

Theorem GLIFT_eq : forall p1 p2,
  gphiSatisfiable p1 ->
  gphiSatisfiable p2 ->
  sfrmgphi [] p1 ->
  sfrmgphi [] p2 ->
  geq p1 p2 <-> GLIFT2 eq p1 p2.
Proof.
  unfold
    GLIFT2, PLIFT2, gGamma, sfrmgphi,
    gphiSatisfiable, NotIn,
    phiIsIndependentVar.
  intros.
  split; intros.
  - inversionx H3; simpl.
    * eex.
    * destruct p1, p2.
      unfold gphiImplies in *.
      simpl in *.
      destruct b, b0; try discriminate; unf.
      + repeat eex.
      + exists p1. eex.
        intuition.
      + exists p0. eex.
        intuition.
  - unf.
    subst.
    destruct p1, p2. simpl in *.
    destruct b, b0; unf.
    * repeat eca.
    * subst.
      repeat eca.
    * subst.
      repeat eca.
    * repeat subst.
      eca.
Qed.

(* HFieldAssign *)
Inductive IHFieldAssign : phi -> s -> phi -> Prop :=
| IIHFieldAssign : forall p1' p1 p2 phi(*\*) (x y : x) (f : f) C T,
    fieldHasType C f T ->
    sfrmphi [] p1 ->
    p1 = (phiType x (TClass C) :: 
          phiType y T ::
          phi ++ [phiAcc (ex x) f]) ->
    p2 = (phiType x (TClass C) ::
          phiAcc (ex x) f ::
          phiEq (edot (ex x) f) (ex y) :: phi) ->
    phiImplies p1' p1 ->
    IHFieldAssign 
      p1'
      (sMemberSet x f y) 
      p2
.

Print gphiImplies.

Inductive gIHFieldAssign : gphi -> s -> gphi -> Prop :=
| gIIHFieldAssign : forall (gp1 gp2 : gphi) p1 p2 phi (x y : x) (f : f) C T,
    fieldHasType C f T ->
    sfrmphi [] p1 ->
    p1 = (phiType x (TClass C) :: 
          phiType y T ::
          phi ++ [phiAcc (ex x) f]) ->
    p2 = (phiType x (TClass C) ::
          phiAcc (ex x) f ::
          phiEq (edot (ex x) f) (ex y) :: phi) ->
    gphiImplies gp1 (false, p1) ->
(*     geq gp2 (false, p2) -> *)
(*     (if fst gp2 
      then phiImplies p2 (snd gp2) /\
           phiSatisfiable p2
      else p2 = snd gp2) -> *)
    gGamma gp2 p2 ->
    gIHFieldAssign 
      gp1
      (sMemberSet x f y) 
      gp2
.

Theorem GLIFT_HFieldAssign : forall s p1 p2,
(*   gphiSatisfiable p1 ->
  gphiSatisfiable p2 ->
  sfrmgphi [] p1 ->
  sfrmgphi [] p2 -> *)
  gIHFieldAssign p1 s p2 <-> GLIFT2 (fun p1 p2 => IHFieldAssign p1 s p2) p1 p2.
Proof.
  unfold
    GLIFT2, PLIFT2, gGamma, sfrmgphi,
    gphiSatisfiable, NotIn,
    phiIsIndependentVar.
  intros.
(*   rename H into ps1.
  rename H0 into ps2.
  rename H1 into sf1.
  rename H2 into sf2. *)
  destruct p1, p2. simpl in *.
  split; intros.
  - inversionx H.
    unfold gGamma in *.
    destruct b, b0;
    simpl in *;
    try discriminate;
    unfold gphiImplies, phiSatisfiable in *;
    simpl in *; unf.
    * eexists. eexists.
      split. Focus 2.
      split. Focus 2.
      econstructor.
        eauto.
        Focus 2. eauto.
        Focus 2. eauto.
        repeat eca.
        eauto.
      split. eex.
      split. repeat eca.
      assumption.
      split. eex.
      split. assumption.
      assumption.
    * repeat eexists; eauto;
      repeat eca.
    * repeat eexists; eauto;
      repeat eca.
    * repeat eexists; eauto;
      repeat eca.
  - unf.
    inversionx H2.
    destruct b, b0;
    unf.
    * econstructor.
        eauto.
        apply H3.
        eauto.
        eauto.
        repeat eca.
        repeat eca.
    * econstructor.
        eauto.
        Focus 2. eauto.
        Focus 2. eauto.
        eauto.
        eex.
        assumption.
    * econstructor.
        eauto.
        Focus 2. eauto.
        Focus 2. eauto.
        eauto.
        subst. assumption.
        eca.
    * econstructor.
        eauto.
        Focus 2. eauto.
        Focus 2. eauto.
        eauto.
        subst. assumption.
        assumption.
Qed.

Definition phiRemoveX (x : x) (p : phi) : phi :=
  filter (fun p' => negb (existsb (x_decb x) (FV' p'))) p.

Definition phiIndependentOfX (x : x) (p : phi) := forall H r A,
  evalphi H r A p -> evalphi H r A (phiRemoveX x p).

(* NotInFV *)
Definition GNotInFV (x : x) (gp : gphi) : Prop :=
  In x (FV (snd gp)) -> 
  fst gp = true /\ phiIsIndependentVar x (snd gp).

Lemma phiIsIndependentVarBidirectional : forall x p,
  phiIsIndependentVar x p ->
  forall H r A v, evalphi H r A p <-> evalphi H (rhoSubst x v r) A p.
Proof.
  unfold phiIsIndependentVar.
  intros.
  split; try apply H0.
  intros.
Admitted.

Lemma phiImpliesIsIndependentVar : forall p1 p2 x,
  phiImplies p1 p2 ->
  phiIsIndependentVar x p1 ->
  phiIsIndependentVar x p2.
Proof.
  unfold phiIsIndependentVar.
  intros.
Admitted.

Theorem GLIFT_GNotInFV : forall x p,
  gphiSatisfiable p ->
  sfrmgphi [] p ->
  GNotInFV x p <-> GLIFT1 (NotInFV x) p.
Proof.
  unfold
    GLIFT1, PLIFT1, gGamma, sfrmgphi, GNotInFV, 
    gphiSatisfiable, NotInFV, NotIn,
    phiIsIndependentVar.
  intros.
  destruct p0. simpl.
  split; intros.
  - destruct b; simpl in *.
    * admit.
    * inversionx H0; try discriminate.
      eex.
      autounfold.
      intro inf. apply H1 in inf. unf.
      discriminate.
  - unf.
    destruct b; unf.
    * split; auto.
      intros.
      admit.
    * subst.
      tauto.
Admitted.


(* HSec *)
Inductive hoareSec (hoare : phi -> phi -> Prop) : phi -> phi -> Prop :=
| HSec : forall (p1 p2 p3 : phi),
    hoare p1 p2 ->
    hoare p2 p3 ->
    hoareSec hoare p1 p3
.

Inductive ghoareSec (ghoare : gphi -> gphi -> Prop) : gphi -> gphi -> Prop :=
| GHSecGuarantee : forall (p1 p2 p3 : gphi), (* later: probably just special case of generic one with 0 evidence requirement! *)
    fst p2 = false ->
    ghoare p1 p2 ->
    ghoare p2 p3 ->
    ghoareSec ghoare p1 p3
| GHSecGeneric : forall (p1 p2 p3 : gphi),
    ghoare p1 p2 ->
    ghoare p2 p3 ->
    ghoareSec ghoare p1 p3
.

Theorem GLIFT_hoareSec : forall (hoare : phi -> phi -> Prop) p1 p3,
  ghoareSec (GLIFT2 hoare) p1 p3 <-> GLIFT2 (hoareSec hoare) p1 p3.
Proof.
  intros.
  unfold GLIFT2, PLIFT2, gGamma.
  destruct p1 as [bp1 p1].
  destruct p3 as [bp3 p3].
  
  simpl in *.
  split; intros.
  - inversionx H.
    + unf.
      destruct p2.
      simpl in *. repeat subst.
      exists x1.
      exists x0.
      repeat split; auto.
      eca.
    + unf.
      destruct p2.
      assert (b = true). admit.
      simpl in *. repeat subst.
       
      exists x1.
      exists x0.
      repeat split; auto.
      eca.
      admit. (* only guaranteeable using runtime info *)
  - unf.
    inversionx H2.
    apply (GHSecGuarantee _ (bp1, p1) (false, p2) (bp3, p3));
    auto;
    simpl;
    try eex.
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
