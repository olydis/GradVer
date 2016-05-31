Load GradVer10LemmaSfrmSubst.
Import Semantics.


Definition phiOrthogonal (p1 p2 : phi) := disjoint (FV p1) (FV p2).

Definition phiSatisfiable (p : phi) := exists H r A, evalphi H r A p.

Definition phiIsIndependentVar (x : x) (p : phi) := forall H r A v,
  evalphi H r A p -> evalphi H (rhoSubst x v r) A p.

Lemma phiSatisfiableAppComm : forall p1 p2,
  phiSatisfiable (p1 ++ p2) ->
  phiSatisfiable (p2 ++ p1).
Proof.
  unfold phiSatisfiable; intros.
  unf.
  repeat eexists.
  apply evalphiSymm.
  eassumption.
Qed.

Lemma phiFVorIsIndependentVar : forall x p,
  phiIsIndependentVar x p \/ In x (FV p).
Proof.
  intros.
  assert (CL := classic (In x0 (FV p0))).
  intuition.
  constructor.
  unfold phiIsIndependentVar.
  intros.
  apply evalphiRemoveRhoSubst;
  intuition.
Qed.

Lemma phiOrthogonalityImpliesIndependence : forall p1 p2 x,
    phiOrthogonal p1 p2 ->
    In x (FV p1) ->
    phiIsIndependentVar x p2.
Proof.
  intros.
  unfold phiOrthogonal, disjoint in *.
  specialize (H0 x0).
  assert (CL := phiFVorIsIndependentVar x0 p2).
  intuition.
Qed.

Lemma phiOrthogonalAppA : forall p1a p1b p2,
  phiOrthogonal (p1a ++ p1b) p2 <->
  phiOrthogonal p1a p2 /\
  phiOrthogonal p1b p2.
Proof.
  unfold phiOrthogonal, disjoint, phiSatisfiable in *.
  split; intros;
  rewrite FVApp in *.
  - split; intros; specialize (H0 x0); intuition.
  - intuition.
    rewrite in_app_iff.
    specialize (H1 x0).
    specialize (H2 x0).
    intuition.
Qed.

Definition rhoWithOmap (omap : o -> o) (r : rho) : rho :=
  fun x => option_map
           (fun v => match v with
                     | vo o => vo (omap o)
                     | _ => v
                     end)
           (r x).

Lemma phiSatisfiableAppHelper : forall p0 p1 H0 H1 r0 r1 A0 A1,
  (∀ x, ¬ In x (FV p0) ∨ ¬ In x (FV p1)) ->
  evalphi H0 r0 A0 p0 ->
  evalphi H1 r1 A1 p1 ->
  evalphi
    (λ o : nat,
       match modulo o 2 with
       | 0 => H0 (div o 2)
       | Datatypes.S _ => H1 (div (o - 1) 2)
       end)
    (λ x,
       match rhoWithOmap (λ o, 2 * o) r0 x with
       | Some v => Some v
       | None => rhoWithOmap (λ o, 2 * o + 1) r1 x
       end)
    (A0 ++ A1)
    (p0 ++ p1).
Proof.
Admitted.

Lemma phiSatisfiableApp : forall p0 p1,
  phiOrthogonal p0 p1 ->
  phiSatisfiable p0 ->
  phiSatisfiable p1 ->
  phiSatisfiable (p0 ++ p1).
Proof.
  intros; simpl in *;
  intuition.
  unfold phiOrthogonal, disjoint, phiSatisfiable in *.
  unf.
  repeat eexists.
  eapply phiSatisfiableAppHelper; eauto.
Qed.

Lemma phiSatisfiableAppRev : forall p0 p1,
  phiSatisfiable (p0 ++ p1) ->
  phiSatisfiable p0 /\ phiSatisfiable p1.
Proof.
  unfold phiSatisfiable.
  intros.
  unf.
  split; repeat eexists.
  - eapply evalphiPrefix. eauto.
  - eapply evalphiSuffix. eauto.
Qed.

(**)
Lemma footprint'RemoveRhoSubsts2 : forall h r r' p,
  footprint' h (rhoSubsts (FV' p) r' r) p = 
  footprint' h r' p.
Proof.
  intros.
  destruct p0; simpl; try tauto.
  destruct (r' x0);
  simpl;
  rewrite rhoSubstId;
  tauto.
Qed.

(**)
Definition rhoDefinedAt (r : rho) (xs : list x) :=
  forall x, In x xs -> exists v, r x = Some v.

Lemma evaleRhoDefinedAt : forall H r e v,
  evale H r e v ->
  rhoDefinedAt r (FVe e).
Proof.
  unfold rhoDefinedAt.
  induction e0;
  intros;
  common;
  simpl in *.
  - inversion H2.
  - intuition.
    subst.
    eexists.
    eauto.
  - destruct (evale' H0 r e0) eqn: eve; inversionx H1.
    eapply IHe0; auto.
    unfold evale.
    eauto.
Qed.

Lemma evalphi'RhoDefinedAt : forall H r A p,
  evalphi' H r A p ->
  rhoDefinedAt r (FV' p).
Proof.
  unfold rhoDefinedAt.
  intros.
  inversionx H1;
  simpl in *.
  - inversion H2.
  - apply evaleRhoDefinedAt in H4.
    apply evaleRhoDefinedAt in H5.
    specialize (H4 x0).
    specialize (H5 x0).
    apply in_app_iff in H2.
    intuition.
  - apply evaleRhoDefinedAt in H4.
    apply evaleRhoDefinedAt in H5.
    specialize (H4 x0).
    specialize (H5 x0).
    apply in_app_iff in H2.
    intuition.
  - intuition.
    subst.
    eexists.
    eauto.
  - intuition.
    subst.
    eexists.
    eauto.
Qed.

Lemma rhoDefinedAtIncl : forall xs2 r xs1,
  incl xs2 xs1 ->
  rhoDefinedAt r xs1 ->
  rhoDefinedAt r xs2.
Proof.
  unfold incl, rhoDefinedAt.
  intros.
  apply H1.
  apply H0.
  assumption.
Qed.

Lemma rhoSubstsId : forall r r' x xs,
  rhoDefinedAt r' xs ->
  In x xs ->
  rhoSubsts xs r' r x = r' x.
Proof.
  induction xs;
  intros;
  inversionx H1.
  - unfold rhoSubsts.
    simpl.
    rewrite rhoSubstId.
    assert (In x0 (x0 :: xs)). constructor. tauto.
    apply H0 in H1.
    unf.
    rewrite H2.
    auto.
  - simpl.
    eapply (rhoDefinedAtIncl xs) in H0; try (apply incl_tl; apply incl_refl).
    unfold rhoSubst.
    dec (x_dec x0 a).
    * apply H0 in H2.
      unf.
      rewrite H1.
      tauto.
    * apply IHxs; auto.
Qed.

Lemma evale'RemoveRhoSubsts2 : forall h xs r r' e,
  rhoDefinedAt r' xs ->
  incl (FVe e) xs ->
  evale' h (rhoSubsts xs r' r) e = 
  evale' h r' e.
Proof.
  induction e0;
  intros;
  simpl in *;
  auto.
  - apply inclSingle in H1.
    apply rhoSubstsId; auto.
  - rewrite IHe0; auto.
Qed.

Lemma evalphi'RemoveRhoSubsts2 : forall h p r r' a,
  rhoDefinedAt r' (FV' p) ->
  evalphi' h (rhoSubsts (FV' p) r' r) a p <->
  evalphi' h r' a p.
Proof.
  split;
  intros.
  - inversionx H1;
    econstructor;
    unfold evale in *;
    eauto.
  * erewrite evale'RemoveRhoSubsts2 in H3; eauto.
    simpl.
    intuition.
  * erewrite evale'RemoveRhoSubsts2 in H4; eauto.
    simpl.
    intuition.
  * erewrite evale'RemoveRhoSubsts2 in H3; eauto.
    simpl.
    intuition.
  * erewrite evale'RemoveRhoSubsts2 in H4; eauto.
    simpl.
    intuition.
  * erewrite rhoSubstsId in H3; eauto.
    simpl.
    intuition.
  * erewrite rhoSubstsId in H3; eauto.
    simpl.
    intuition.
  - inversionx H1;
    econstructor;
    unfold evale in *;
    eauto;
    try (erewrite evale'RemoveRhoSubsts2; eauto; simpl; intuition);
    try (erewrite rhoSubstsId           ; eauto; simpl; intuition).
Qed.


Lemma inclAexcept2 : forall a a1 a2,
  incl a1 a2 ->
  incl (Aexcept a1 a) (Aexcept a2 a).
Proof.
  unfold incl, Aexcept, except.
  intros.
  apply filter_In.
  apply filter_In in H1.
  intuition.
Qed.

Lemma evalphiAccessIncl : forall p h r a1 a2,
  incl a1 a2 ->
  evalphi h r a1 p ->
  evalphi h r a2 p.
Proof.
  induction p0;
  intros;
  try constructor.
  inversionx H1.
  eca.
  - eapply incl_tran; eauto.
  - eapply IHp0; eauto.
    apply inclAexcept2.
    assumption.
Qed.

Definition invNoAlias
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    let sfp := staticFootprint phi in
      forall f x1 x2, 
        In (x1, f) sfp ->
        In (x2, f) sfp ->
        rho x1 <> rho x2.

Lemma phiImpliesNarrowingSingle : forall p p1 p2,
  phiOrthogonal [p] p2 ->
  phiSatisfiable (p :: p1) ->
  phiImplies (p :: p1) p2 ->
  phiImplies p1 p2.
Proof.
  intros.
  unfold phiOrthogonal, phiSatisfiable, phiImplies in *.
  unf.
  simpl in *.
  rewrite app_nil_r in *.
  intros.
  specialize (H2 h (rhoSubsts (FV' p0) x1 r) (footprint' h x1 p0 ++ a)).
  rewrite (evalphiRemoveRhoSubsts p2) in H2; auto.
  eapply evalphiAccessIncl; eauto.


      (* 
      
  eauto.
  
  assert (evalphi h r (footprint' h x1 p0 ++ a) p2 = evalphi h r a p2) as xxx. admit.
  rewrite xxx in *. clear xxx.
  
  apply H2.
  eca.
  - rewrite footprint'RemoveRhoSubsts2.
    intuition.
  - rewrite footprint'RemoveRhoSubsts2.
    rewrite evalphi'RemoveRhoSubsts2.
  * inversionx H3. admit.
  * inversionx H3.
    eapply evalphi'RhoDefinedAt.
    eauto.
  - rewrite footprint'RemoveRhoSubsts2.

  assert (disj) *)
  (*show that x2 is irrelevant for access to p2's expressions*)
Admitted.

Lemma phiImpliesNarrowing : forall p0 p1 p2,
  phiOrthogonal p0 p2 ->
  phiSatisfiable (p0 ++ p1) ->
  phiImplies (p0 ++ p1) p2 ->
  phiImplies p1 p2.
Proof.
  induction p0;
  intros;
  simpl in *;
  try assumption.
  assert (Hsat := H1).
  rewrite cons2app in H0.
  rewrite cons2app in H1.
  apply phiOrthogonalAppA in H0.
  apply phiSatisfiableAppRev in H1.
  unf.
  apply IHp0; auto.
  eapply phiImpliesNarrowingSingle; eauto.
Qed.

Lemma phiImpliesNarrowingSingleNeqNull : forall p p1 e,
  disjoint (FV' p) (FVe e) ->
  phiSatisfiable (p :: p1) ->
  phiImplies (p :: p1) [phiNeq e (ev vnull)] ->
  phiImplies p1 [phiNeq e (ev vnull)].
Proof.
  intros.
  unfold phiSatisfiable, phiImplies in *.
  unf.
  intros.
  specialize (H2 x0 (rhoSubsts (FV' p0) x1 r) x2).
  
  eca;
  simpl.
  - apply inclEmpty.
  - eca; unfold evale; simpl; eauto.
Admitted.

Lemma hasStaticTypeNarrowingSingle : forall p p1 e T,
  disjoint (FV' p) (FVe e) ->
  phiSatisfiable (p :: p1) ->
  hasStaticType (p :: p1) e T ->
  hasStaticType p1 e T.
Proof.
  induction e0;
  intros;
  inversionx H2.
  - eca.
  - eca.
  - eca.
    admit.
  - simpl in *.
    eca.
    eapply IHe0 in H5; eauto.
    inversionx H5.
    * unfold phiSatisfiable in H1.
      unf.
      apply H7 in H2.
      inversionx H2.
      simpl in *.
      inversionx H13.
      common.
      inversionx H4.
      inversionx H11.
      tauto.
    * unfold phiImplies.
      intros.
      simpl in *.
      unfold phiSatisfiable in H1.
      unf.
      apply H7 in H3.
    
    
    Check phiI.
  unf.
  
  inversionx H2;
  eca.
  
  simpl in *.
  
  specialize (H2 h (rhoSubsts (FV' p0) x1 r) (footprint' h x1 p0 ++ a)).
  rewrite (evalphiRemoveRhoSubsts p2) in H2; auto.
  eapply evalphiAccessIncl; eauto.
Admitted.

Lemma hasStaticTypeNarrowing : forall p0 p1 e T,
  disjoint (FV p0) (FVe e) ->
  phiSatisfiable (p0 ++ p1) ->
  hasStaticType (p0 ++ p1) e T ->
  hasStaticType p1 e T.
Proof.
  induction p0;
  intros;
  simpl in *;
  try assumption.
  assert (Hsat := H1).
  rewrite cons2app in H0.
  rewrite cons2app in H1.
  apply phiOrthogonalAppA in H0.
  apply phiSatisfiableAppRev in H1.
  unf.
  apply IHp0; auto.
  eapply phiImpliesNarrowingSingle; eauto.
Qed.

Lemma hasStaticTypeNarrowing : forall p0 p1 e T,
  disjoint (FV p0) (FVe e) ->
  phiSatisfiable (p0 ++ p1) ->
  hasStaticType (p0 ++ p1) e T ->
  hasStaticType p1 e T.
Proof.
  induction e0;
  intros;
  inversionx H2;
  try constructor.
  - eapply phiImpliesNarrowing; eauto.
  - eca.
    eapply phiImpliesNarrowing; eauto.
    unfold phiOrthogonal.
    simpl in *.
    repeat rewrite app_nil_r.
    assumption.
Qed.

(*extract to other lemmas*)
Lemma hasStaticTypePhiComm : forall p0 p1 e T,
  hasStaticType (p0 ++ p1) e T ->
  hasStaticType (p1 ++ p0) e T.
Proof.
  induction e0;
  intros;
  inversionx H0;
  try constructor.
  - apply phiImpliesAppCommA.
    assumption.
  - eca.
    apply phiImpliesAppCommA.
    assumption.
Qed.
  
  
  
  
  
  
  
