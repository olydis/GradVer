Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Decidable.
Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Logic.Eqdep_dec.
Require Import Classical_Prop.

Load GradVer.
Load GradVerPreludeLtac.
Import Semantics.

Lemma evalphiTrue : forall H r A, True -> evalphi H r A [].
Proof.
  intros.
  constructor.
Qed.

Lemma evalphiApp : forall p1 p2 H r A, evalphi H r A (p1 ++ p2) -> evalphi H r A p1.
Proof.
  induction p1; intros; try constructor.
  assert (Hx := app_comm_cons).
  specialize (Hx phi' p1 p2 a).
  symmetry in Hx.
  rewrite Hx in H1.
  clear Hx.
  inversionx H1.
  apply IHp1 in H12.
  econstructor; eauto.
Qed.

Lemma inclAexcept : forall A1 A2 A3,
  incl A1 (Aexcept A2 A3) -> incl A1 A2.
Proof.
  unfold incl.
  intros.
  apply H0 in H1.
  unfold Aexcept in H1.
  unfold except in H1.
  apply filter_In in H1.
  intuition.
Qed.

Lemma AexceptComm : forall A1 A2 A3,
  Aexcept (Aexcept A1 A2) A3 = Aexcept (Aexcept A1 A3) A2.
Proof.
Admitted.

Lemma evalphiFootprint : forall p p' H r A,
    evalphi H r A p ->
    In p' p ->
    incl (footprint' H r p') A.
Proof.
  induction p0; intros; inversionx H1;
  try (inversion H2; fail).
  inversionx H2; try assumption.
  eapply IHp0 in H13; eauto.
  apply inclAexcept in H13.
  assumption.
Qed.

Lemma evalphiSymm : forall p1 p2 H r A, evalphi H r A (p1 ++ p2) -> evalphi H r A (p2 ++ p1).
Proof.
  induction p1.
  - intros.
    rewrite app_nil_r.
    rewrite app_nil_l in H1.
    assumption.
  - intros.
    assert (Hx := app_comm_cons).
    specialize (Hx phi' p1 p2 a).
    symmetry in Hx.
    rewrite Hx in H1.
    clear Hx.
    inversionx H1.
    apply IHp1 in H12.
    clear IHp1.
    generalize p2 H0 r A H11 H12 H6.
    clear.
    induction p2; intros.
    * rewrite app_nil_l.
      rewrite app_nil_l in H12.
      econstructor; eauto.
    * assert (Hx := app_comm_cons).
      specialize (Hx phi' p2 (a :: p1) a0).
      symmetry in Hx.
      rewrite Hx.
      clear Hx.
      econstructor; eauto.
      + eapply evalphiFootprint in H12.
        eapply inclAexcept in H12.
        eauto.
        assert (Hx := app_comm_cons).
        specialize (Hx phi' p2 p1 a0).
        symmetry in Hx.
        rewrite Hx.
        clear Hx.
        constructor.
        tauto.
      + assert (Hx := app_comm_cons).
        specialize (Hx phi' p2 p1 a0).
        symmetry in Hx.
        rewrite Hx in H12.
        clear Hx.
        inversionx H12.
        assumption.
      + apply IHp2; auto.
          assert (Hx := app_comm_cons).
          specialize (Hx phi' p2 p1 a0).
          symmetry in Hx.
          rewrite Hx in H12.
          clear Hx.
          inversionx H12.
          rewrite AexceptComm.
          assumption.

Admitted.

Lemma evalphi'Aexcept : forall p h r a a2,
  evalphi' h r (Aexcept a a2) p -> evalphi' h r a p.
Proof.
  intros.
  inversionx H0;
  econstructor; eauto.
  unfold Aexcept, except in H3.
  apply filter_In in H3.
  intuition.
Qed.

Lemma evalphiAexcept : forall p h r a a2,
  evalphi h r (Aexcept a a2) p -> evalphi h r a p.
Proof.
  induction p0;
  intros; try constructor.
  inversionx H0.
  econstructor; eauto.
  - apply inclAexcept in H5.
    assumption.
  - eapply IHp0.
    erewrite AexceptComm.
    eauto.
Qed.

Lemma AexceptEmpty : forall A, Aexcept A [] = A.
Proof.
  induction A.
  - compute.
    tauto.
  - unfold Aexcept, except in *.
    simpl in *.
    rewrite IHA.
    tauto.
Qed.

Lemma evalphiFalse : forall a H r A x f, In (phiAcc x f) a -> ~ evalphi H r A (phiAcc x f :: a).
Proof.
  induction a; intros; inversionx H1; intuition.
  - inversionx H1.
    inversionx H12.
    inversionx H11.
    unfold footprint' in *.
    rewrite H9 in *; clear H9.
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

Lemma HnotTotal : forall (H' : H), exists x, H' x = None.
Admitted.

Lemma evalPhiPrefix : forall p1 h r a p2,
   evalphi h r a (p1 ++ p2) -> evalphi h r a p1.
Proof.
  induction p1;
  intros.
  * constructor.
  * app_cons H0.
    inversionx H0.
    apply IHp1 in H11.
    econstructor; eauto.
Qed.

Lemma HSubstsLeavesUntouched : forall mm o0 o1 C m H,
  o0 <> o1 ->
  H o0 = Some (C, m) ->
  HSubsts o1 mm H o0 = Some (C, m).
Proof.
  unfold HSubsts; 
  induction mm; intros;
  simpl; auto.
  apply IHmm; auto.
  unfold HSubst.
  destruct (o_decb o0 o1) eqn: rec; auto.
  contradict H1.
  unfold o_decb in rec.
  unfold dec2decb in rec.
  destruct (o_dec o0 o1); auto.
  inversion rec.
Qed.

Lemma PropLift : forall (P : execState -> Prop),
  (forall a b, dynSem a b -> P a -> P b) ->
  (forall a b, dynSemStar a b -> P a -> P b).
Proof.
  intros.
  induction H1; try assumption.
  apply IHdynSemStar.
  eapply H0; eauto.
Qed.

Lemma lengthId : forall {A : Type} (a b : list A), a = b -> Datatypes.length a = Datatypes.length b.
Proof.
  intros.
  rewrite H0.
  tauto.
Qed.

Lemma HeapGetsMoreSpecific' : forall s1 s2 (H1 H2 : H) (C : C) m1 (o : o),
  dynSem (H1, s1) (H2, s2) ->
             H1 o = Some (C, m1) ->
  exists m2, H2 o = Some (C, m2).
Proof.
  intros.
  inversion H0; subst;
  try (eexists; eauto; fail).
  - unfold HSubst.
    destruct (o_decb o0 o1) eqn: oe;
    eexists;
    eauto.
    rewrite H3.
    eauto.
  - exists m1.
    unfold Halloc.
    apply HSubstsLeavesUntouched; auto.
    destruct (o_dec o0 o1); auto.
    subst. rewrite H9 in H3.
    inversion H3.
Qed.

Lemma HeapGetsMoreSpecific : forall (C : C) (o : o) m1 s1 s2 (H1 H2 : H),
  dynSemStar (H1, s1) (H2, s2) ->
             H1 o = Some (C, m1) ->
  exists m2, H2 o = Some (C, m2).
Proof.
  specialize (HeapGetsMoreSpecific').
  intro.
  intro.
  intro.
  specialize (PropLift (fun x => exists m1, fst x o0 = Some (C0, m1))).
  intro.
  assert (∀ a b : execState,
      dynSem a b
      → (∃ m1 : f → option v, fst a o0 = Some (C0, m1))
        → ∃ m1 : f → option v, fst b o0 = Some (C0, m1)).
    clear H1.
    intros.
    destruct a, b.
    inversionx H2.
    eapply H0 in H1.
      inversionx H1.
      eexists; eassumption.

      eassumption.
  intuition.
  clear H0 H2.
  specialize (H3 (H1, s1) (H4, s2)).
  intuition.
  apply H0.
  eexists. eassumption.
Qed.

Lemma RhoGetsMoreSpecific' : forall r1 r2 a1 a2 s1 s2 S (H1 H2 : H) v1 (x : x),
  dynSem (H1, (r1, a1, s1) :: S) (H2, (r2, a2, s2) :: S) ->
             r1 x = Some v1 ->
  exists v2, r2 x = Some v2.
Proof.
  intros.
  inversion H0; clear H0; try subst;
  try (eexists; eauto; fail);
  try (unfold rhoSubst, x_decb, dec2decb;
    destruct (x_dec x0 x1); subst; eexists; eauto; fail).
  - unfold rhoSubst, x_decb, dec2decb.
    destruct (x_dec x0 xresult); subst; eexists; eauto.
  - apply lengthId in H15.
    simpl in H15.
    contradict H15.
    auto with arith.
  - apply lengthId in H15.
    simpl in H15.
    contradict H15.
    auto with arith.
Qed.

Lemma RhoGetsMoreSpecific : forall r1 r2 a1 a2 s1 s2 S (H1 H2 : H) v1 (x : x),
  dynSemStar (H1, (r1, a1, s1) :: S) (H2, (r2, a2, s2) :: S) ->
             r1 x = Some v1 ->
  exists v2, r2 x = Some v2.
Proof.
Admitted.

Lemma phiImpliesRefl : forall x, phiImplies x x.
Proof.
  unfold phiImplies.
  auto.
Qed.
Hint Resolve phiImpliesRefl.

Lemma AexceptReverse : forall a1 a2, Aexcept (a1 ++ a2) a2 = a1.
Admitted.

Lemma evalPhiImplies : forall H' r A' q1 q2,
  phiImplies q1 q2 -> evalphi H' r A' q1 -> evalphi H' r A' q2.
Proof.
  intros.
  unfold phiImplies in H0.
  specialize (H0 H' r A').
  intuition.
Qed.

Lemma InAexcept : forall x a a', In x (Aexcept a a') -> In x a.
Proof.
  unfold Aexcept.
  unfold except.
  induction a; intros.
  - compute in H0.
    inversion H0.
  - simpl.
    simpl filter in H0.
    destruct (existsb (A_d'_decb a) a'); simpl in H0.
    * apply IHa in H0.
      auto.
    * inversion H0; auto.
      apply IHa in H1.
      auto.
Qed.

Lemma mapSplitFst : forall {A B : Type} (x : list (A * B)), map fst x = fst (split x).
Admitted.
Lemma mapSplitSnd : forall {A B : Type} (x : list (A * B)), map snd x = snd (split x).
Admitted.

Lemma exists_forall : forall {A : Type} (b : A -> Prop) (c : Prop), ((exists a, b a) -> c) -> (forall a, b a -> c).
Proof.
  intros.
  apply H0.
  eauto.
Qed.
