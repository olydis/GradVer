Load GradVer20Hook.
Import Semantics.

(* disjunciton of phi *)
Definition phid := list phi.

Definition evalphid H r A (pd : phid) :=
  exists p, In p pd /\ evalphi H r A p.

(* playground *)
Definition phiEquiv (p1 p2 : phi) := phiImplies p1 p2 /\ phiImplies p2 p1.
Definition gradPhiA (p1 : phi) (p2 : phi) := exists p1x, phiEquiv (p1 ++ p1x) p2.
Definition gradPhiB (p1 : phi) (p2 : phi) := phiImplies p2 p1.


(* meet operation *)
Definition splitPhi (p : phi) : prod A_s phi :=
  fold_right
    (fun p pr => 
      match p with
      | phiAcc e f => ((e, f) :: fst pr, snd pr)
      | _ => (fst pr, p :: snd pr)
      end)
    ([], [])
    p.

Lemma splitPhiAlt : forall p pa pb,
  splitPhi p = (pa, pb) ->
  pa = staticFootprint p /\
  pb = filter (fun p' => match p' with
                         | phiAcc _ _ => false
                         | _ => true
                         end) p.
Proof.
  induction p0; intros; simpl in *.
  - inversionx H0.
    tauto.
  - destruct (splitPhi p0).
    simpl in *.
    specialize (IHp0 a0 p1).
    intuition; subst;
    destruct a; simpl in *; inversionx H0; tauto.
Qed.


Lemma accFreeMeet : forall p1 p2 pb1 pb2 pa1 pa2,
  

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

