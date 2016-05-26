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
Import Semantics.

(* playground *)
Definition phiEquiv (p1 p2 : phi) := phiImplies p1 p2 /\ phiImplies p2 p1.
Definition gradPhiA (p1 : phi) (p2 : phi) := exists p1x, phiEquiv (p1 ++ p1x) p2.
Definition gradPhiB (p1 : phi) (p2 : phi) := phiImplies p2 p1.

Ltac inversionE H :=
  inversion H; clear H.
Ltac inversionx H :=
  inversion H; clear H; subst.

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

Definition phiMinusAccess (p1 p2 : phi) :=
  let fp := staticFootprint p2 in
  filter (fun p => match p with
                   | phiAcc x f => match find (fun fp => x_decb x (fst fp) && f_decb f (snd fp)) fp with
                                   | Some _ => true
                                   | None => false
                                   end
                   | _ => true
                   end) p1.

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

Theorem gradPhiEquiv : forall (p1 p2 : phi),
  gradPhiA p1 p2 <-> gradPhiB p1 p2.
Proof.
  split;
  generalize p1, p2; clear p1 p2.
  * unfold gradPhiA, gradPhiB, phiEquiv, phiImplies in *.
    intros.
    inversionE H0.
    inversionx H2.
    apply H3 in H1.
    clear H0 H3.
    apply evalphiApp in H1.
    assumption.
  * unfold gradPhiA, gradPhiB, phiEquiv, phiImplies in *;
    intros.
    exists (phiMinusAccess p2 p1).
    split; intros.
    - generalize p2 a r h H1.
      clear.
      induction p2; intros; try constructor.
      econstructor; eauto.
      + destruct a; simpl; try (unfold incl; intros; inversion H0).
        destruct (r x0) eqn: rx; try (unfold incl; intros; inversion H0).
        destruct v0.
        destruct x1; try (unfold incl; intros; inversion H0).
        destruct v0; unfold incl; intros; inversion H0; inversionx H2.
        clear H0.
        admit.
      + admit.
      + admit.
    - assert (H11 := H1).
      apply H0 in H11.
      admit.
Admitted.

(* meet operation *)
Definition phiEnsureAccess (x : x) (f : f) (p : phi) : list phi :=
  let xs := map fst (filter (fun xf => f_decb f (snd xf)) (staticFootprint p)) in
  (phiAcc x f :: (*(map (fun x' => phiNeq (ex x) (ex x')) xs) ++*) p) :: (map (fun x' => phiEq (ex x) (ex x') :: p) xs).

Fixpoint phiMeet (a b : phi) : list phi := 
  match a with
  | [] => [b]
  | a' :: a => let ax := phiMeet a b in
      match a' with
      | phiAcc x f => flat_map (phiEnsureAccess x f) ax
      | _ => map (fun ax' => a' :: ax') ax
      end
  end.

Open Scope string.
Eval compute in phiMeet [phiAcc (xUserDef "a") "f"; phiAcc (xUserDef "b") "f"] [].
Close Scope string.

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

Lemma phiEnsureAccessEval : forall x0 x1 x2 x3 H1 r A,
  In x2 (phiEnsureAccess x0 x1 x3) -> evalphi H1 r A x2 -> evalphi H1 r A x3.
Proof.
  intros.
  unfold phiEnsureAccess in H0.
  inversionx H0.
  - inversionx H2.
    apply evalphiAexcept in H12.
    assumption.
  - apply in_map_iff in H3.
    inversionE H3.
    inversionx H0.
    inversionx H2.
    apply evalphiAexcept in H13.
    assumption.
Qed.

Lemma phiMeetWorksPhiAcc : forall a0,
    (∀ (b : phi) (H : H) (r : rho) (A : A_d), evalphi H r A a0 ∧ evalphi H r A b ↔ (∃ c : phi, In c (phiMeet a0 b) ∧ evalphi H r A c)) ->
    (∀ x0 x1 (b : phi) (H0 : H) (r : rho) (A : A_d), evalphi H0 r A (phiAcc x0 x1 :: a0) ∧ evalphi H0 r A b ↔ (∃ c : phi, In c (phiMeet (phiAcc x0 x1 :: a0) b) ∧ evalphi H0 r A c)).
  induction b.
  - split; intuition.
    * eexists. split.
      + eapply phiMeetEmpty.
      + assumption.
    * inversionE H2.
      inversionx H3.
      simpl in H2.
      apply in_flat_map in H2.
      inversionE H2.
      inversionx H3.
      specialize (H0 [phiAcc x0 x1] H1 r A).
      assert (∃ c : phi, In c (phiMeet a0 [phiAcc x0 x1]) ∧ evalphi H1 r A c).
        exists x3. split; try assumption.
        eapply phiEnsureAccessEval; eauto.
      apply H0 in H3.
        
      assert (evalphi H1 r A x2 ∧ evalphi H1 r A []).
        intuition. constructor.
      intuition.
      econstructor; eauto.

 exists (phiAcc x0 x1 :: a0); simpl.
  intros.
Admitted.

Theorem phiMeetWorks : forall a b H r A,
  evalphi H r A a /\ evalphi H r A b <-> (exists c, In c (phiMeet a b) /\ evalphi H r A c).
Proof.
  induction a.
  - intros.
    split; intuition; simpl in *.
    * exists b.
      intuition.
    * constructor.
    * inversionE H1.
      inversionx H2.
      inversionx H1; try inversion H2.
      assumption.
  - assert (CL := classic (exists x f, a = phiAcc x f)).
    inversionE CL.
    * inversionx H0.
      inversionx H1.
      apply phiMeetWorksPhiAcc.
      assumption.
    * split; intros.
      + inversionx H2.
        inversionx H3.
        apply evalphiAexcept in H14.
        assert (∃ c : phi, In c (phiMeet a0 b) ∧ evalphi H1 r A c).
          apply IHa. intuition.
        inversionE H2.
        inversionx H3.
        exists (a :: x0).
        destruct a;
        split; simpl;
        try (apply in_map; try assumption);
        try (econstructor; eauto; simpl; rewrite AexceptEmpty; assumption).
        (*contradict phiAcc*)
        contradict H0; eexists; eauto.
        contradict H0; eexists; eauto.
Qed.

Theorem phiMeetWorks : forall a b, exists cs, forall H r A,
  evalphi H r A a /\ evalphi H r A b <-> (exists c, In c cs /\ evalphi H r A c).
Proof.
  induction a.
    intros.
    exists [b].
    intros.
    split; intuition.
      exists b. split; try assumption; try constructor. tauto.
      constructor.
      inversionE H1.
      inversionx H2.
      inversionx H1; try assumption.
      inversion H2.
  intros.
  pose proof (IHa b) as IHax.
  specialize (IHa (a :: b)).
  destruct a.
  - inversionE IHa.
    exists x0.
    intros.
    specialize (H0 H1 r A).
    intuition.
    * inversionx H4.
      apply evalphiAexcept in H15.
      apply H0; try assumption.
      econstructor; eauto.
      simpl.
      rewrite AexceptEmpty. assumption.
    * econstructor; eauto; simpl.
      + compute. intuition.
      + inversionx H5. simpl in H14. assumption.
      + rewrite AexceptEmpty. assumption.
    * inversionx H5.
      apply evalphiAexcept in H15.
      assumption.
  - inversionE IHa.
    exists x0.
    intros.
    specialize (H0 H1 r A).
    intuition.
    * inversionx H4.
      apply evalphiAexcept in H15.
      apply H0; try assumption.
      econstructor; eauto.
      simpl.
      rewrite AexceptEmpty. assumption.
    * econstructor; eauto; simpl.
      + compute. intuition.
      + inversionx H5. simpl in H14. assumption.
      + rewrite AexceptEmpty. assumption.
    * inversionx H5.
      apply evalphiAexcept in H15.
      assumption.
  - inversionE IHa.
    exists x0.
    intros.
    specialize (H0 H1 r A).
    intuition.
    * inversionx H4.
      apply evalphiAexcept in H15.
      apply H0; try assumption.
      econstructor; eauto.
      simpl.
      rewrite AexceptEmpty. assumption.
    * econstructor; eauto; simpl.
      + compute. intuition.
      + inversionx H5. simpl in H14. assumption.
      + rewrite AexceptEmpty. assumption.
    * inversionx H5.
      apply evalphiAexcept in H15.
      assumption.
  - assert (CA := classic (In (phiAcc x0 f0) a0)).
    inversionx CA.
      exists [[phiAcc x0 f0 ; phiAcc x0 f0]].
      split; intros.
        (*->*)
        inversionx H2.
        apply evalphiFalse in H3; try assumption.
        inversion H3.
        (*<-*)
        inversionE H2. inversionx H3. inversionx H2; try inversion H3.
        apply evalphiFalse in H4; try assumption; try constructor; inversion H4.
        tauto.
    assert (CB := classic (In (phiAcc x0 f0) b)).
    inversionx CB.
   ++ inversionE IHax.
      exists x1.
      intros.
      specialize (H2 H3 r A).
      intuition.
      * inversionx H6.
        apply evalphiAexcept in H17.
        apply H2; try assumption.
      * eapply (evalphiIn b) in H1; eauto.
        inversionx H1. inversionx H13.
        econstructor; eauto.
        + simpl. rewrite H1. unfold incl. intros. inversionx H6; try assumption. inversion H8.
        + econstructor.
            unfold optionVisO. eexists. eassumption.
            unfold footprint'. rewrite H1. constructor. tauto.
        + unfold footprint'. 
          rewrite H1.
          generalize a0 H3 r A H0 H5 H1.
          clear.
          induction a0; intros; try constructor.
          inversionx H5.
          apply not_in_cons in H0.
          inversionx H0.
          apply IHa0 in H14; try assumption.
          rewrite AexceptComm in H14.
          econstructor; eauto.
          destruct a; simpl in *; try (unfold incl; intuition; fail).
          destruct (x_dec x0 x1).
            subst. rewrite H1 in *.
            unfold incl in *.
            intros.
            assert (H00 := H0).
            inversionx H00; try (inversion H5; fail).
            apply H8 in H0.
            unfold Aexcept, except.
            apply filter_In.
            intuition.
            apply negb_true_iff.
            simpl.
            unfold A_d'_decb, o_decb, string_decb, dec2decb.
            destruct (o_dec (fst (o0, f1)) (fst (o0, f0))); try (simpl in n; contradict n; tauto).
            destruct (string_dec (snd (o0, f1)) (snd (o0, f0))); try (simpl in e1; subst; contradict H2; tauto).
            auto.

            destruct (r x1); try (unfold incl; intuition).
            destruct v0.
            destruct x3; try inversion H0.
            destruct v0; try inversionx H0.
            

            
          
      * inversionx H5.
        simpl in H15.
        rewrite AexceptEmpty in H15.
        assumption.





(* PROOF SECTION *)
Notation "'φ'" := phi.
Notation "'ρ'" := rho.

(* determinism? *)

Definition invHeapConsistent
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    forall x o C, rho x = Some (existT _ (TClass C) (v'o C o)) -> 
      exists res fs,
        fields C = Some fs /\
        Heap o = Some (C, res) /\
        (forall (T : T) (f : f), In (T, f) fs -> exists v, res f = Some (existT _ T v))
        .
Definition invPhiHolds
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    evalphi Heap rho A phi.
Definition invTypesHold
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    forall e T, staticType phi e = Some T -> dynamicType Heap rho e = Some T.

Definition invAll
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    invHeapConsistent
      Heap rho A phi /\
    invPhiHolds
      Heap rho A phi /\
    invTypesHold
      Heap rho A phi.

Ltac uninv :=
  unfold invAll in *;
  unfold invHeapConsistent in *;
  unfold invPhiHolds in *;
  unfold invTypesHold in *.

Lemma getTypeImpliesStaticType : forall phi x,
  getType phi x = staticType phi (ex x).
Proof. auto. Qed.

Lemma HnotTotal : forall (H' : H), exists x, H' x = None.
Admitted.

Ltac applyINV1 INV1 H :=
  try auto.

Ltac applyINV2 INV2 H :=
  apply INV2 in H;
  inversion H;
  clear H;
  subst.

Ltac applyINV3 INV3 H :=
  apply INV3 in H;
  unfold dynamicType in H;
  simpl in H.

Ltac emagicProgress :=
  repeat eexists;
  econstructor; econstructor;
  unfold evale; simpl; eauto.

Ltac common :=
  repeat match goal with
    | [ H : option_map _ ?T = _ |- _ ] =>
                        destruct T eqn: ?;
                        inversionx H
    | [ H : evale _ _ _ _ |- _ ] => unfold evale in H; simpl in H
  end.

Lemma evalPhiPrefix : forall h r a p1 p2,
   evalphi h r a (p1 ++ p2) -> evalphi h r a p1.
Proof.
  induction p1;
  intros.
  * unfold evalphi.
    intros.
    inversion H1.
  * specialize (IHp1 p2).
    unfold evalphi in *.
    intros.
    inversionx H1.
    + apply H0.
      constructor.
      tauto.
    + apply IHp1 in H2; auto.
      intros.
      apply H0.
      apply in_app_or in H1.
      apply in_or_app.
      inversionx H1; auto.
      constructor.
      apply in_cons.
      auto.
Qed.

Definition soundness : Prop :=
  forall pre s post initialHeap initialRho initialAccess S',
  hoare pre s post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s) :: S') (finalHeap, (finalRho, finalAccess, []) :: S') /\
    invAll finalHeap finalRho finalAccess post.

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
    unfold fieldsNames in H9.
    destruct (fields C1); simpl in H9; inversion H9.
    apply HSubstsLeavesUntouched; auto.
    destruct (o_dec o0 o1); auto.
    subst. rewrite H3 in H8.
    inversion H8.
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
  - apply lengthId in H13.
    simpl in H13.
    contradict H13.
    auto with arith.
  - apply lengthId in H14.
    simpl in H14.
    contradict H14.
    auto with arith.
Qed.

Lemma RhoGetsMoreSpecific : forall r1 r2 a1 a2 s1 s2 S (H1 H2 : H) v1 (x : x),
  dynSemStar (H1, (r1, a1, s1) :: S) (H2, (r2, a2, s2) :: S) ->
             r1 x = Some v1 ->
  exists v2, r2 x = Some v2.
Proof.
Admitted.

Lemma rhoPhiHelper'' : forall e r x1 x2 v0 o0 C0 H0 z rt v,
  r x1 = Some (vo C0 o0) ->
  r x2 = Some v0 ->
  (∀ x0 : x, In x0 (getVarsE e) → xUserDef z = x0 ∨ xthis = x0) ->
  evale H0 r (eSubsts [(xthis, ex x1); (xUserDef z, ex x2)] e) v ->
  evale H0
    (rhoFrom3 xresult (defaultValue rt) xthis (vo C0 o0) (xUserDef z) v0)
    e v.
Proof.
  unfold evale;
  induction e0; intros; simpl in *.
  - assumption.
  - unfold rhoFrom3.
    unfold x_decb, dec2decb in *.
    destruct (x_dec x0 xthis).
    * subst.
      destruct (x_dec xthis xresult); try inversion e0.
      simpl in H4.
      rewrite H1 in H4.
      assumption.
    * destruct (x_dec x0 (xUserDef z)).
      + subst.
        destruct (x_dec (xUserDef z) xresult); try inversion e0.
        simpl in H4.
        rewrite H2 in H4.
        assumption.
      + specialize (H3 x0).
        intuition.
  - destruct (evale' H0 r (eSubsts [(xthis, ex x1); (xUserDef z, ex x2)] e0)) eqn: eva;
    try (inversion H4; fail).
    destruct v2.
    eapply IHe0 in eva; eauto.
    erewrite eva.
    apply H4.
Qed.

Lemma rhoPhiHelper' : forall r x1 x2 p' z H0 a0 v0 C0 o0 rt,
  r x1 = Some (vo C0 o0) ->
  r x2 = Some v0 ->
  (∀ x0 : x, In x0 (getVarsPhi' p') → xUserDef z = x0 ∨ xthis = x0) ->
  evalphi' H0 r a0 (phi'Substs [(xthis, ex x1); (xUserDef z, ex x2)] p') ->
  evalphi' H0 (rhoFrom3 xresult (defaultValue rt) xthis (vo C0 o0) (xUserDef z) v0) a0 p'.
Proof.
  intros.
  inversionx H4;
  unfold phi'Substs in *.
  - destruct p'; simpl in H9; inversionx H9; try constructor.
    * destruct (x_decb x0 xthis); inversionx H5.
      destruct (x_decb x0 (xUserDef z)); inversionx H6.
    * destruct (x_decb x0 xthis); inversionx H5.
      destruct (x_decb x0 (xUserDef z)); inversionx H6.
  - destruct p'; simpl in H5; inversionx H5; try constructor.
    * econstructor.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold getVarsPhi'. apply in_or_app. auto.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold getVarsPhi'. apply in_or_app. auto.
      + tauto.
    * destruct (x_decb x0 xthis); inversionx H8.
      destruct (x_decb x0 (xUserDef z)); inversionx H5.
    * destruct (x_decb x0 xthis); inversionx H8.
      destruct (x_decb x0 (xUserDef z)); inversionx H5.
  - destruct p'; simpl in H5; inversionx H5; try constructor.
    * econstructor.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold getVarsPhi'. apply in_or_app. auto.
      + eapply rhoPhiHelper''; eauto. 
        intros. specialize (H3 x0).
        apply H3.
        unfold getVarsPhi'. apply in_or_app. auto.
      + tauto.
    * destruct (x_decb x0 xthis); inversionx H8.
      destruct (x_decb x0 (xUserDef z)); inversionx H5.
    * destruct (x_decb x0 xthis); inversionx H8.
      destruct (x_decb x0 (xUserDef z)); inversionx H5.
  - destruct p'; simpl in H5; inversionx H5; try constructor.
    unfold x_decb, dec2decb in *.
    destruct (x_dec x3 xthis); inversionx H7.
    * econstructor; eauto.
      unfold optionVisO.
      inversion H6.
      exists x0.
      unfold rhoFrom3.
      unfold x_decb, dec2decb in *.
      destruct (x_dec xthis xresult); try inversion e0.
      destruct (x_dec xthis xthis); try (contradict n; tauto).
      rewrite H1 in H4.
      assumption.
    * destruct (x_dec x3 (xUserDef z)); inversionx H5.
      + econstructor; eauto.
        unfold optionVisO.
        inversion H6.
        exists x0.
        unfold rhoFrom3.
        unfold x_decb, dec2decb in *.
        destruct (x_dec (xUserDef z) xresult); try inversion e0.
        destruct (x_dec (xUserDef z) xthis); try inversion e0.
        destruct (x_dec (xUserDef z) (xUserDef z)); try (contradict n2; tauto).
        rewrite H2 in H4.
        assumption.
      + specialize (H3 x3).
        simpl in H3.
        intuition.
    * destruct (x_decb x3 xthis); inversionx H7.
      destruct (x_decb x3 (xUserDef z)); inversionx H5.
  - destruct p'; simpl in H5; inversionx H5.
    * destruct (x_decb x3 xthis); inversionx H6.
      destruct (x_decb x3 (xUserDef z)); inversionx H5.
    * specialize (H3 x3).
      simpl in H3.
      destruct v0.
      unfold vo in *.
      unfold rhoFrom3, x_decb, dec2decb in *.
      destruct (x_dec x3 xthis).
      + inversionx H6.
        destruct (x_dec xthis xresult); try inversion e0.
        rewrite H1 in H9.
        econstructor.
        destruct (x_dec xthis xresult). contradict n. assumption.
        destruct (x_dec xthis xthis). eassumption.
        contradict n1. tauto.
      + destruct (x_dec x3 (xUserDef z)); try intuition.
        subst.
        inversionx H6.
        econstructor.
        destruct (x_dec (xUserDef z) xresult). inversion e0.
        destruct (x_dec (xUserDef z) xthis). inversion e0.
        destruct (x_dec (xUserDef z) (xUserDef z)); try intuition.
        rewrite H2 in H9.
        eassumption.
Qed.

Lemma rhoPhiHelper : forall phi x1 x2 v0 o0 a z C0 rt r H,
  (∀ x : x, In x (getVarsPhi phi) → (xUserDef z) = x ∨ xthis = x) ->
  r x1 = Some (vo C0 o0) ->
  r x2 = Some v0 ->
  evalphi H r a (phiSubsts2 xthis (ex x1) (xUserDef z) (ex x2) phi) ->
  evalphi H (rhoFrom3 xresult (defaultValue rt) xthis (vo C0 o0) (xUserDef z) v0) a phi.
Proof.
  induction phi0; unfold evalphi; intros; inversionx H5.
  - clear IHphi0.
    assert (∀ x0 : x, In x0 (getVarsPhi' p') → (xUserDef z) = x0 ∨ xthis = x0).
      intros.
      apply H1.
      unfold getVarsPhi.
      apply in_flat_map.
      exists p'.
      intuition.
    clear H1.
    assert (evalphi' H0 r a0 (phi'Substs [(xthis, ex x1) ; (xUserDef z, ex x2)] p')).
      apply H4.
      unfold phiSubsts2, phiSubsts.
      apply in_map_iff. eexists. intuition.
    clear H4.
    eapply rhoPhiHelper'; eauto.
  - unfold evalphi in IHphi0.
    eapply IHphi0; eauto; intros.
    * apply (H1 x0).
      unfold getVarsPhi in *.
      apply in_flat_map.
      apply in_flat_map in H5.
      inversionx H5.
      exists x3.
      intuition.
    * apply H4.
      unfold phiSubsts2, phiSubst in *.
      unfold phiSubsts in *.
      apply in_map_iff.
      apply in_map_iff in H5.
      inversionx H5.
      exists x0.
      intuition.
Qed.

Theorem staSemProgress : forall (s'' : s) (s' : list s) (pre post : phi) initialHeap initialRho initialAccess S',
  hoareSingle pre s'' post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s'' :: s') :: S') (finalHeap, (finalRho, finalAccess, s') :: S')
.
  destruct s'';
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro HO;
  intro INV;

  uninv;
  inversion HO; clear HO; subst;

  inversion INV as [INV1 INVx]; clear INV;
  inversion INVx as [INV2 INV3]; clear INVx;
  try rewrite getTypeImpliesStaticType in *.
  - applyINV2 INV2 H8.
    applyINV2 INV2 H9.
    applyINV3 INV3 H3.
    applyINV3 INV3 H6.

    common.
    rewrite H2 in *.
    inversionx Heqo0.
    inversionx H10.
    inversionx H0.
    simpl in *.
    inversionx H1.
    inversionx H12.

    emagicProgress.

  - applyINV3 INV3 H2.
    applyINV3 INV3 H3.
    common.

    emagicProgress.

  - specialize (HnotTotal initialHeap). intros.
    inversionx H0.
    unfold fieldsNames in H5.
    destruct (fields c) eqn: fi; simpl in H5; inversionx H5.
    emagicProgress.
  - applyINV2 INV2 H7.
    applyINV3 INV3 H4.
    applyINV3 INV3 H5.
    applyINV3 INV3 H6.
    common.
    rewrite H2 in *.
    inversionx Heqo2.
    inversionx H15.

    destruct v2. simpl in *. subst.
    destruct v2. contradict H16. auto.

    assert (H1 := H2).
    apply INV1 in H1.
    inversionx H1.
    inversionx H0.
    inversionx H1.
    inversionx H3.

    (*get method*)
    unfold mparam in H12.
    destruct (mmethod C0 m0) eqn: mm; simpl in *; inversionx H12.
    destruct m1.
    inversionx H5.

    (*well def*)
    remember (Method t m1 (projT1 v0) z c l) as m2.
    assert (mm2 := mm).
    unfold mmethod in mm2.
    destruct (class C0) eqn: cc; try (inversion mm2; fail).
    specialize (pWellDefined c0). intros.
    unfold class in cc.
    apply find_some in cc.
    inversionx cc.
    destruct c0.
    unfold C_decb, string_decb, dec2decb in H6.
    destruct (string_dec c0 C0); inversionx H6.
    apply H3 in H5. clear H3.
    apply find_some in mm2.
    inversionx mm2.
    unfold m_decb, string_decb, dec2decb in H6.
    destruct (string_dec m1 m0); inversionx H6.
    unfold CWellDefined in H5.
    inversionx H5.
    apply H6 in H3. clear H6.
    unfold mWellDefined in H3.
    destruct c.
    intuition.
    rename H11 into varsPre.
    rename H13 into varsPost.
    
    (*unify method knowledge*)
    unfold mpre, mpost, mcontract in *.
    rewrite mm in *. simpl in *.
    inversionx H9.
    inversionx H10.

    remember (projT1 v1) as ret_type.
    remember (rhoFrom3 xresult (defaultValue ret_type) xthis (vo C0 o0) (xUserDef z) v0) as r'.
    remember (footprint initialHeap r' phi_pre) as fp.

    (*proof strategy*)
    assert (forall a b c d, dynSem a b -> dynSemStar b c -> dynSem c d -> dynSemStar a d)
           as strat.
      intros.
      econstructor; eauto.
      eapply dynSemStarBack; eauto.

    (*Part 1: make the call*)
    assert (dynSem 
              (initialHeap, (initialRho, initialAccess, sCall x0 x1 m0 x2 :: s') :: S')
              (initialHeap, (r', fp, l) :: (initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s') :: S')
           ).
      econstructor; unfold evale; simpl; eauto.
        unfold mbody.
        rewrite mm. simpl.
        eauto.

        unfold mparam.
        rewrite mm. simpl.
        eauto.

        unfold mpre.
        unfold mcontract.
        rewrite mm. simpl.
        eauto.

        clear INV1 INV3.
        unfold phiImplies in H8.
        apply H8 in INV2. clear H8.
        apply evalPhiPrefix in INV2.
        rewrite Heqr'.
        eapply rhoPhiHelper; eauto.
        intros.
        specialize (varsPre x5).
        intuition.

    (*Part 2: method body (assumes soundness, termination, ... for method body)*)
    assert soundness as sdn. admit.
    unfold soundness in sdn.
    remember ((initialRho, Aexcept initialAccess fp, sCall x0 x1 m0 x2 :: s') :: S') as S''.
    specialize (sdn phi_pre l phi_post initialHeap r' fp S'').
    apply sdn in H5. clear sdn.
    inversion H5; clear H5.
    inversion H10; clear H10.
    inversion H5; clear H5.
    inversion H10; clear H10.
    Focus 2.
      admit. (*that follows from preservation proof of Part 1!*)

    (*Part 3: call finish*)
    assert (exists initialRh', dynSem
              (x5, (x6, x7, []) :: (initialRho, Aexcept initialAccess fp , sCall x0 x1 m0 x2 :: s') :: S')
              (x5,                 (initialRh', Aexcept initialAccess fp ++ footprint x5 x6 phi_post, s') :: S')
           ).
      assert (dss := H5).

      (*heap*)
      eapply HeapGetsMoreSpecific in H5; try eassumption.
      inversion H5; clear H5.

      (*rho*)
      eapply RhoGetsMoreSpecific in dss.
      Focus 2.
        instantiate (2 := xresult).
        rewrite Heqr'.
        unfold rhoFrom3, x_decb, dec2decb.
        simpl. eauto.
      inversion dss; clear dss.

      eexists. econstructor; eauto.
        unfold mpost, mcontract.
        rewrite mm. simpl. tauto.

        uninv. apply H11.
    inversion H10; clear H10.
    
    (*marriage*)
    subst.
    repeat eexists.
    eapply strat; eauto.
  - applyINV3 INV3 H1.
    common.
    emagicProgress.
  - emagicProgress.
  - emagicProgress.
    unfold phiImplies in H1.
    apply H1 in INV2.
    unfold evalphi in INV2.
    apply INV2.
    constructor.
    tauto.
  - emagicProgress.
Proof.


Theorem staSemSoundness : forall (s'' : s) (s' : list s) (pre post : phi) initialHeap initialRho initialAccess S',
  hoareSingle pre s'' post ->
  invAll initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess,
    dynSemStar (initialHeap, (initialRho, initialAccess, s'' :: s') :: S') (finalHeap, (finalRho, finalAccess, s') :: S') /\
    invAll finalHeap finalRho finalAccess post
.
  destruct s'';
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro;
  intro HO;
  intro INV;

  uninv;
  inversion HO; clear HO; subst;

  inversion INV as [INV1 INVx]; clear INV;
  inversion INVx as [INV2 INV3]; clear INVx;
  try rewrite getTypeImpliesStaticType in *.
  - applyINV2 INV2 H8.
    applyINV2 INV2 H9.
    applyINV3 INV3 H3.
    applyINV3 INV3 H6.

    common.
    rewrite H2 in *.
    inversionx Heqo0.
    inversionx H10.
    inversionx H0.
    simpl in *.
    inversionx H1.
    inversionx H12.
    clear H13.
    destruct v0.
    simpl in *.

    do 3 eexists.
    constructor;
    try (econstructor; econstructor; unfold evale; simpl; eauto; fail).

    (*PRESERVATION*)
    intuition.
    * destruct (o_dec o0 o1).
      + subst.
        assert (C0 = C1).
          apply INV1 in H0.
          apply INV1 in H2.
          inversionx H0.
          inversionx H1.
          inversionx H2.
          inversionx H1.
          intuition.
          rewrite H2 in H3.
          inversion H3.
          tauto.
        subst.
        apply INV1 in H0. inversionx H0. inversionx H1.
        exists (fun f => if f_decb f f0 then Some (existT v' x2 v0) else x4 f).
        exists x5.
        intuition.
          unfold HSubst.
          unfold o_decb, f_decb, dec2decb.
          destruct (o_dec o1 o1); try (contradict n; tauto).
          rewrite H0.
          tauto.

          unfold f_decb, string_decb, dec2decb in *.
          destruct (string_dec f1 f0).
            subst.
            unfold fieldType in H4.
            unfold fields in H1.
            destruct (class C1) eqn: cc; try (inversion H1; fail).
            destruct c.
            common.
            apply find_some in Heqo0.
            destruct f1.
            inversionx Heqo0.
            unfold f_decb, string_decb, dec2decb in *.
            destruct (string_dec f1 f0); inversionx H6.
            subst.
            inversionx H1.
            apply in_map_iff in H3.
            inversionx H3.
            inversionx H1.
            destruct x2.
            inversionx H3.
            specialize (pWellDefined (Cls c l l0)).
            intros.
            unfold class in cc.
            apply find_some in cc.
            intuition.
            unfold C_decb, string_decb, dec2decb in *.
            destruct (string_dec c C1); inversionx H7.
            unfold CWellDefined in H8.
            intuition.
            eapply H7 in H4; eauto.
            subst.
            exists v0.
            tauto.

            apply H5 in H3.
            inversionx H3.
            eexists. eauto.
      + apply INV1 in H0.
        inversionx H0.
        inversionx H1.
        intuition.
        exists x4.
        exists x5.
        intuition.
        unfold HSubst.
        unfold o_decb, dec2decb.
        destruct (o_dec o1 o0); intuition.
    * unfold evalphi in *.
      intros. specialize (INV2 p').
      unfold appEnd in *.
      apply in_app_iff in H0.
      inversionx H0.
      + intuition.
        
Proof.


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

(*
Lemma phiTrueSubst : forall a b p, phiTrue = phiSubst a b p -> p = phiTrue.
Proof.
  intros.
  destruct p; auto;
  unfold phiSubst in H0; inversion H0.
Qed.
Lemma phiTrueSubsts : forall a p, phiTrue = phiSubsts a p -> p = phiTrue.
Proof.
  induction a; intros.
  - simpl in H0.
    auto.
  - simpl in H0.
    apply IHa in H0.
    symmetry in H0.
    apply phiTrueSubst in H0.
    assumption.
Qed.
Lemma phiEqSubsts : forall a p e1 e2, phiEq e1 e2 = phiSubsts a p -> exists e1' e2', p = phiEq e1' e2' /\ e1 = eSubsts a e1' /\ e2 = eSubsts a e2'.
Proof.
  induction a; intros.
  - repeat eexists.
    simpl in H0.
    subst.
    auto.
  - simpl in H0.
    apply IHa in H0.
    inversion H0; clear H0.
    inversion H1; clear H1.
    intuition.
    subst.
    destruct p; simpl in H1; inversion H1.
    repeat eexists.
    * admit.
    * admit.
Admitted.

Lemma eSubstsVal : forall x v, eSubsts x (ev v) = (ev v).
Proof.
  induction x0; intros.
  - simpl; tauto.
  - specialize (IHx0 v0).
    assert (eSubsts (a :: x0) (ev v0) = eSubsts x0 (ev v0)).
    * admit.
    * rewrite IHx0 in H0.
      assumption.
Admitted.

Lemma phiImpliesConj : forall a b c, phiImplies a (phiConj b c) -> phiImplies a b.
Admitted.*)

Ltac tmp := repeat eexists; econstructor; econstructor; eauto.
Ltac unfWT := 
  unfold wellTyped in *;
  unfold wellTypedPhi in *;
  unfold wellTypedE in *;
  simpl getType in *.

Lemma evaleTClass : forall G e' C' h r, getType G e' = Some (TClass C') -> (let res := evale h r e' in res = Some vnull \/ exists o', res = Some (vo o')).
Admitted. (* TODO: entangle *)

Definition consistent (H' : H) (r : rho) := forall x' o' res, r x' = Some (vo o') -> H' o' = Some res.

Lemma exists_forall : forall {A : Type} (b : A -> Prop) (c : Prop), ((exists a, b a) -> c) -> (forall a, b a -> c).
Proof.
  intros.
  apply H0.
  eauto.
Qed.
  

Lemma rhoVSeSubst : forall e'' e''' h r e' x' v', 
 evale h r e' = Some v' ->
 eSubst x' e' e'' = e''' ->
  evale h (rhoSubst x' v' r) e'' =
  evale h r e'''.
Proof.
  induction e''; intros; subst.
  - simpl. auto.
  - simpl eSubst. simpl. unfold rhoSubst.
    case_eq (x_decb x0 x'); intros; simpl; try tauto.
    rewrite H0.
    tauto.
Qed.

Lemma rhoVSphiSubst1 : forall e'' e''' h r e' x' v' a, 
 evale h r e' = Some v' ->
 phi'Subst x' e' e'' = e''' ->
  (evalphi' h (rhoSubst x' v' r) a e'' ->
  evalphi' h r a e''').
Proof.
  induction e''; intros; subst; intros; try constructor; simpl in *.
  - inversion H2; clear H2; subst.
    econstructor.
    * erewrite rhoVSeSubst in H4; eauto.
    * erewrite rhoVSeSubst in H8; eauto.
    * tauto.
  - inversion H2; clear H2; subst.
    econstructor.
    * erewrite rhoVSeSubst in H4; eauto.
    * erewrite rhoVSeSubst in H8; eauto.
    * tauto.
  - inversion H2; clear H2; subst.
    econstructor.
    * erewrite rhoVSeSubst in H7; eauto.
    * tauto.
Qed.
Lemma rhoVSphiSubst2 : forall e'' e''' h r e' x' v' a, 
 evale h r e' = Some v' ->
 phi'Subst x' e' e'' = e''' ->
  (evalphi' h r a e''' ->
  evalphi' h (rhoSubst x' v' r) a e'').
Proof.
  induction e''; intros; subst; intros; try constructor; simpl in *.
  - inversion H2; clear H2; subst.
    specialize (rhoVSeSubst e0 (eSubst x' e' e0) h r e' x' v').
    intros.
    specialize (rhoVSeSubst e1 (eSubst x' e' e1) h r e' x' v').
    intros.
    intuition.
    rewrite H8, H4 in *.
    econstructor; eauto.
  - inversion H2; clear H2; subst.
    specialize (rhoVSeSubst e0 (eSubst x' e' e0) h r e' x' v').
    intros.
    specialize (rhoVSeSubst e1 (eSubst x' e' e1) h r e' x' v').
    intros.
    intuition.
    rewrite H8, H4 in *.
    econstructor; eauto.
  - inversion H2; clear H2; subst.
    specialize (rhoVSeSubst e0 (eSubst x' e' e0) h r e' x' v').
    intros.
    intuition.
    rewrite H7 in *.
    econstructor; eauto.
Qed.


(* playground *)
Open Scope string_scope.

Notation "AA '⊢sfrme' ee" := (sfrme AA ee) (at level 90).

Print sfrme.
Print dynSem.