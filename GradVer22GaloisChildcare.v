Load GradVer22Galois.
Import Semantics.


(* intuition about funny condition *)
Definition gPhiApp (p : phi) (gp1 gp2 : gphi) : Prop :=
  fst gp2 = fst gp1 /\
  snd gp2 = snd gp1 ++ p /\
  (forall p'',(good p'' /\ phiImplies p'' (snd gp1 ++ p)) ->
   exists p' , good p'  /\ phiImplies p'  (snd gp1) /\ phiImplies p'' (p' ++ p)).

Definition gPhiAppWorksFor (pAdd : phi) (pBase : phi) := 
  gPhiApp pAdd (true, pBase) (true, pBase ++ pAdd).
  
Open Scope string.
Definition t_ea : e := ex (xUserDef "a").
Definition t_eb : e := ex (xUserDef "b").
Definition t_ec : e := ex (xUserDef "c").
Definition t_ed : e := ex (xUserDef "d").


Lemma gPhiApp1 : gPhiAppWorksFor [phiAcc t_ea "f"] [phiAcc t_eb "f"].
Proof.
  unfold gPhiAppWorksFor, gPhiApp. simpl.
  splau. splau.
  intros. unf.
  exists [phiAcc t_eb "f"].
  split. admit.
  splau.
Admitted.

Lemma gPhiApp2 : ~ gPhiAppWorksFor [phiAcc t_ea "f"] [phiEq (edot t_ea "f") t_eb].
Proof.
  unfold gPhiAppWorksFor, gPhiApp. simpl.
  intro. unf.
  specialize (H2 [phiAcc t_ea "f"; phiEq (edot t_ea "f") t_eb]).
  lapply H2; intros.
  - unf.
    admit.
  - split. admit.
    cut.
Admitted.

Lemma gPhiApp3 : gPhiAppWorksFor [phiEq (edot t_ea "f") t_eb] [phiAcc t_ea "f"].
Proof.
  unfold gPhiAppWorksFor, gPhiApp. simpl.
  splau. splau.
  intros. unf.
  exists [phiAcc t_ea "f"].
  split. admit.
  splau.
Admitted.

Close Scope string.


(* partial galois connection *)
Theorem GLIFT_concat : forall (p : phi),
  GLIFTmp1 (fun p' => p' ++ p) (gPhiApp p).
Proof.
  unfold gPhiApp.
  unfold GLIFTmp1.
  unfold PLIFTm1.
  intros. inv H1. inv H3.
  
  destruct gp1, gp2'. simpl in *. subst.
  rename H4 into ass.
  
  inv H.
  inv H0.
  inv H.
  
  assert (gGood (b, p1 ++ p0)) as gg.
    unf.
    assert (good x). eapp H5. subst.
    unfold gGamma' in H.
    eca; simpl in *.
      unfold gphiSatisfiable. simpl.
      destruct b; simpl in *.
        inv H0.
        invE H6 h.
        invE H6 r.
        invE H6 a.
        exists h.
        exists r.
        exists a.
        apply evalphiSymm in H6.
        apply evalphiSymm.
        apply evalphiApp in H6. unf.
        eapp evalphiAppRev.
      subst.
      apply H0.
    unfold sfrmgphi.
    destruct b. eca.
    subst.
    apply or_intror.
    simpl.
    apply H0.
  
  unf.
  assert (good x). eapp H5. subst.
  
  simpl.
  unfold gphiEquals.
  eexists.
  eexists.
  split. eca.
  split. eca.
  split.
  - destruct b.
    * repeat intro.
      inv H6. simpl in *.
      destruct gp2.
      destruct b.
      + inv H1. inv H2. inv gg. unfold gphiSatisfiable in *.
        clear H9 H10 H11.
        clear H4 H5.
        
        unfold gGamma' in *. simpl in *. unf.
        splau.
        assert (∀ p2 : phi, (good p2 ∧ phiImplies p2 p1) → good (p2 ++ p0) ∧ phiImplies (p2 ++ p0) p3).
          intros.
          apply H3. eex; apply H.
        clear H3.
        
(*         specialize (H (p2 WO p0)). *)
        specialize (ass p2).
        intuition. unf.
        specialize (H x).
        intuition.
        apply (phiImpliesTrans p2 (x ++ p0) p3); auto.
      + assert (x0 ++ p0 = p3).
          apply H3.
          exists (x0).
          cut.
        assert (phiTrue :: x0 ++ p0 = p3).
          apply H3.
          exists (phiTrue :: x0).
          splau.
          inv H0.
          eca.
            eca.
              eappIn phiImpliesSatisfiable H9.
              repeat intro. eca. apply inclEmpty. eca. common. eapp phiImpliesPrefix.
            repeat eca. eapp sfrmphiApp.
          inv H.
          eappIn phiImpliesTrans H6.
          rewrite cons2app. eapp phiImpliesSuffix.
        subst.
        apply infRecList in H9.
        tauto.
    * repeat intro.
      apply H3.
      inv H6.
      exists p1.
      splau.
      eca.
  - apply H4. assumption.
    unfold pincl. intros.
    unf. assert (good p2). eapp H5.
    subst.
    destruct b; inv H6; cut.
    unfold gGamma'.
    simpl in *.
    splau.
    repeat intro.
    apply evalphiSymm in H6.
    apply evalphiSymm.
    apply evalphiApp in H6. unf.
    eapp evalphiAppRev.
Qed.




Definition nPhiWithout (x : x) (p1 p2 : phi) :=
  phiSatisfiable p1 /\
  minWith (fun p => phiImplies p1 p /\ ~ In x (FV p)) phiImplies p2.

Lemma nPhiWithoutGoodSat : forall x p1 p2,
  nPhiWithout x p1 p2 ->
  phiSatisfiable p1 ->
  phiSatisfiable p2.
Proof.
  intros.
  eapp (phiImpliesSatisfiable p1 p2).
  apply H.
Qed.
Lemma nPhiWithoutGoodSfrm : forall x p1 p2,
  nPhiWithout x p1 p2 ->
  sfrmphi [] p1 ->
  sfrmphi [] p2.
Proof.
  intros.
  admit.
Admitted.
Lemma nPhiWithoutGood : forall x p1 p2,
  nPhiWithout x p1 p2 ->
  good p1 ->
  good p2.
Proof.
  intros.
  inv H0.
  eca.
  - eapply nPhiWithoutGoodSat; eauto.
  - eapply nPhiWithoutGoodSfrm; eauto.
Qed.

Definition gPhiWithout (x : x) (gp1 gp2 : gphi) : Prop :=
  fst gp2 = fst gp1 /\
  nPhiWithout x (snd gp1) (snd gp2).

Lemma gPhiWithoutGood : forall x p1 p2,
  gPhiWithout x p1 p2 ->
  gGood p1 ->
  gGood p2.
Proof.
  intros.
  destruct p1, p2.
  inv H.
  inv H0.
  unfold gGood, gphiSatisfiable, sfrmgphi in *.
  simpl in *. subst.
  destruct b.
  - splau.
    eapply nPhiWithoutGoodSat; eauto.
  - split.
    * eapply nPhiWithoutGoodSat; eauto.
    * apply or_intror.
      inv H3; cut.
      eapply nPhiWithoutGoodSfrm; eauto.
Qed.

(* Lemma phiImpliesNarrowWithout : forall p1 p2 x,
  sfrmphi [] p2 ->
  ~ In x (FV p2) ->
  phiImplies p1 p2 ->
  exists p',
  sfrmphi [] p' /\
  ~ In x (FV p') /\
  phiImplies p1 p' /\ phiImplies p' p2.
Proof.
Admitted. *)

Theorem GLIFT_Without : forall (x : x),
  GLIFTpp1 (nPhiWithout x) (gPhiWithout x).
Proof.
  unfold GLIFTpp1.
  unfold PLIFTp1.
  intros.
  inv H.
  unfold gphiEquals.
  eexists. eexists.
  split. eca. apply gPhiWithoutGood in H1; auto.
  split. inv H0. eca.
  unfold pphiEquals.
  unfold gPhiWithout in *.
  destruct gp1, gp2, gp2'. simpl in *. unf. subst.
  destruct b, b0.
  - inv H0.
    
    split.
    * repeat intro.
      unfold pincl in H4.
      assert (∀ p p', gGamma' (true, p0) p' ∧ nPhiWithout x p' p → gGamma' (true, p1) p)
      as ass1.
        intros.
        apply H4.
        exists p'.
        assumption.
      clear H4.
      unfold gGamma' in *. simpl in *. unf.
      splau.
      eapp phiImpliesTrans.
      assert (∀ p p', good p' -> phiImplies p' p0 -> nPhiWithout x p' p → phiImplies p p1)
      as ass2.
        intros.
        lapply (ass1 p4 p'); intros; cut.
      clear ass1.
      specialize (ass2 p2).
      admit. (*OK*)
(*       eapply ass2; auto. *)
    * apply H5; clear H5.
      + inv H3. inv H5. unf.
        eca; cut.
        eapp phiImpliesSatisfiable.
      + repeat intro.
        unf.
        admit.
  - (* CONTRADICT: a(MUCH) != static *)
    exfalso.
    inv H0.
    clear H5.
    unfold pincl in *.
    pose proof (H4 (p2)) as ap1.
    pose proof (H4 (phiTrue :: p2)) as ap2.
    clear H4.
    
    apply imply_to_or in ap1.
    apply imply_to_or in ap2.
    inv ap1.
      contradict H0.
      admit.
    inv ap2.
      contradict H4.
      admit.
    
    inv H0. inv H4.
    apply infRecList in H0.
    auto.
  - (* CONTRADICT: a(SINGLE) != gradual *)
    exfalso.
    unfold gGamma' in *. simpl in *.
    inv H0.
    unfold pincl in *.
    specialize (H4 p2). lapply H4; intros. Focus 2. exists p0. cut. clear H4.
    assert (∀ gp' : gphi,
     gGood gp'
     → (∀ p : phi, nPhiWithout x p0 p → gGamma' gp' p)
     → ∀ p : phi, good p -> phiImplies p p1 → gGamma' gp' p)
    as ass.
      intros.
      apply H5; auto.
        intros.
        apply H6. unf. subst. assumption.
      eca.
    clear H5.
    inv H0. simpl in *.
    
    specialize (ass (false, p0)).
    admit.
  - inv H0.
    clear H5.
    unfold pincl in H4.
    unfold gGamma' in *. simpl in *.
    assert (p2 = p1).
      apply H4. exists p0. cut.
    subst.
    split; cut.
Qed.
