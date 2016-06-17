Load GradVer3Defs.
Import Semantics.

Lemma Aexcept2AppComm : forall A2 A3 A1,
  Aexcept A1 (A2 ++ A3) = Aexcept A1 (A3 ++ A2).
Proof.
  unfold Aexcept, except.
  intros.
  induction A1; intros; simpl in *; try tauto.
  rewrite IHA1.
  repeat rewrite existsb_app.
  rewrite orb_comm.
  tauto.
Qed.

Lemma footprintApp : forall H r p1 p2,
  footprint H r (p1 ++ p2) = footprint H r p1 ++ footprint H r p2.
Proof.
  induction p1; intros; simpl in *; try tauto.
  rewrite IHp1.
  rewrite app_assoc.
  tauto.
Qed.

Lemma footprintMapAcc : forall H r p,
  footprint H r (map (λ p, phiAcc (fst p) (snd p)) p) =
  oflatten (map (A'_s2A'_d H r) p).
Proof.
  induction p0; intros; simpl in *; try tauto.
  rewrite IHp0.
  unfold olist, A'_s2A'_d.
  destruct a.
  simpl.
  destruct (evale' H0 r e0); try tauto.
  destruct v0; tauto.
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

Lemma dynSemLift : forall a b S,
  dynSem a b ->
  dynSem (fst a, snd a ++ S) (fst b, snd b ++ S).
Proof.
  intros.
  destruct a, b. simpl.
  inversionx H0; eca.
Qed.

Lemma dynSemStarLift : forall a b S,
  dynSemStar a b ->
  dynSemStar (fst a, snd a ++ S) (fst b, snd b ++ S).
Proof.
  intros.
  induction H0; try constructor.
  eca.
  eapp dynSemLift.
Qed.

Lemma phiImpliesTauto : forall H r A p,
  phiImplies [] p ->
  evalphi H r A p.
Proof.
  intros.
  apply H1.
  constructor.
Qed.

Lemma FVApp : forall p1 p2,
  FV (p1 ++ p2) = FV p1 ++ FV p2.
Proof.
  induction p1;
  intros;
  simpl;
  try tauto.
  rewrite IHp1.
  rewrite app_assoc.
  tauto.
Qed.

Lemma evale'RemoveRhoSubst : forall H r x v e,
  ~ In x (FVe e) ->
  evale' H (rhoSubst x v r) e = evale' H r e.
Proof.
  induction e0; intros; simpl in *.
  - tauto.
  - unfold rhoSubst. dec (x_dec x1 x0); tauto.
  - apply IHe0 in H1. rewrite H1. tauto.
Qed.

Lemma FVaccListApp : forall x p l,
  FV (accListApp x l p) = map (fun asd => x) l ++ FV p.
Proof.
  induction l; simpl; try tauto.
  rewrite IHl.
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

Lemma InAexcept : forall x a a', In x (Aexcept a a') -> In x a.
Proof.
  unfold Aexcept.
  unfold except.
  induction a; intros.
  - compute in H0.
    inversion H0.
  - simpl.
    simpl filter in H0.
    destruct (existsb (A'_d_decb a) a'); simpl in H0.
    * apply IHa in H0.
      auto.
    * inversion H0; auto.
      apply IHa in H1.
      auto.
Qed.

Lemma InAexceptNot : forall x a a', In x (Aexcept a a') -> ~ In x a'.
Proof.
  unfold Aexcept.
  unfold except.
  destruct a; intuition.
  apply filter_In in H0.
  inversionx H0.
  contradict H3.
  apply not_true_iff_false.
  apply negb_false_iff.
  apply existsb_exists.
  eexists; split; eauto.
  dec (A'_d_dec x0 x0).
  auto.
Qed.

Lemma InAexceptConstr : forall x a a', ~ In x a' -> In x a -> In x (Aexcept a a').
Proof.
  unfold Aexcept.
  unfold except.
  intros.
  apply filter_In.
  intuition.
  apply negb_true_iff.
  apply not_true_iff_false.
  intuition.
  contradict H0.
  apply existsb_exists in H2.
  inversionE H2.
  inversionx H0.
  undecb.
  destruct x0, x1. simpl in *.
  dec (o_dec o0 o1); simpl in *; inversionx H3.
  dec (string_dec f0 f1); simpl in *; inversionx H4.
  auto.
Qed.

Lemma evalphiTrue : forall H r A, True -> evalphi H r A [].
Proof.
  intros.
  constructor.
Qed.


Lemma AexceptApp : forall A B1 B2,
  Aexcept (Aexcept A B1) B2 = Aexcept A (B1 ++ B2).
Proof.
  induction A; intros; simpl; try tauto.
  rewrite existsb_app.
  destruct (existsb (A'_d_decb a) B1) eqn: exb;
  simpl; rewrite IHA; tauto.
Qed.

Lemma AexceptComm : forall A1 A2 A3,
  Aexcept (Aexcept A1 A2) A3 = Aexcept (Aexcept A1 A3) A2.
Proof.
  induction A1; simpl; intros; try tauto.
  destruct (existsb (A'_d_decb a) A2) eqn: a2;
  destruct (existsb (A'_d_decb a) A3) eqn: a3;
  simpl; repeat rewrite a2;
  simpl; repeat rewrite a3;
  simpl; rewrite IHA1; tauto.
Qed.

Lemma evalphiApp : forall p1 p2 H r A,
  evalphi H r A (p1 ++ p2) ->
  evalphi H r A p1 /\
  evalphi H r (Aexcept A (footprint H r p1)) p2.
Proof.
  induction p1; intros; simpl in *.
  - rewrite AexceptEmpty.
    split; try constructor.
    assumption.
  - inversionx H1.
    apply IHp1 in H12.
    split; try econstructor; intuition.
    rewrite AexceptApp in H2.
    auto.
Qed.

Lemma evalphiAppRev : forall p1 p2 H r A,
  evalphi H r A p1 ->
  evalphi H r (Aexcept A (footprint H r p1)) p2 ->
  evalphi H r A (p1 ++ p2).
Proof.
  induction p1; intros; simpl in *.
  - rewrite AexceptEmpty in *.
    assumption.
  - inversionx H1.
    rewriteRevIn AexceptApp H2.
    eca.
Qed.

Lemma AexceptIncl : forall A' A,
  incl (Aexcept A A') A.
Proof.
  unfold incl.
  intros.
  unfold Aexcept, except in H0.
  apply filter_In in H0.
  intuition.
Qed.
  
Lemma inclAexcept : forall A1 A2 A3,
  incl A1 (Aexcept A2 A3) -> incl A1 A2.
Proof.
  intros.
  eapply incl_tran; eauto.
  apply AexceptIncl.
Qed.

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

Lemma evalphi'ImpliesIncl : forall H r A p,
  evalphi' H r A p ->
  incl (footprint' H r p) A.
Proof.
  intros.
  inversionx H1;
  simpl;
  try apply inclEmpty.
  rewrite H3.
  rewrite inclSingle.
  assumption.
Qed.

Lemma inclAexceptTriple : forall P Q A,
  incl P A ->
  incl Q (Aexcept A P) ->
  incl P (Aexcept A Q).
Proof.
  unfold incl.
  intros.
  assert (CL := classic (In a Q)).
  inversionx CL.
  * apply H1 in H3.
    apply InAexceptNot in H3.
    intuition.
  * apply H0 in H2.
    apply InAexceptConstr; auto.
Qed.

Lemma evalphiSymmHelper : forall p1 p2 H r A p,
  evalphi H r A (p :: p1 ++ p2) ->
  evalphi H r A (p1 ++ p :: p2).
Proof.
  induction p1;
  intros;
  inversionx H1;
  simpl in *;
  econstructor; eauto;
  inversionx H12;
  try assumption.
  - eapply incl_tran; eauto.
    apply AexceptIncl.
  - rewrite AexceptComm in H14.
    apply IHp1;
    try assumption.
    econstructor; eauto.
    apply inclAexceptTriple; auto.
Qed.

Lemma evalphiSymm : forall p1 p2 H r A, 
  evalphi H r A (p1 ++ p2) -> evalphi H r A (p2 ++ p1).
Proof.
  induction p1.
  - intros.
    rewrite app_nil_r.
    assumption.
  - intros.
    app_cons H1.
    inversionx H1.
    apply IHp1 in H12.
    apply evalphiSymmHelper; auto.
    econstructor; eauto.
Qed.

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
    dec (A'_d_dec (o0, f0) (o0, f0)).
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


Lemma evalphiPrefix : forall p1 h r a p2,
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

Lemma evalphiSuffix : forall p1 h r a p2,
   evalphi h r a (p1 ++ p2) -> evalphi h r a p2.
Proof.
  induction p1;
  intros.
  * rewrite app_nil_l in H0.
    assumption.
  * app_cons H0.
    inversionx H0.
    apply IHp1 in H11.
    apply evalphiAexcept in H11.
    assumption.
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
  - unfold HeapNotSetAt in H9.
    exists m1.
    unfold Halloc.
    rewrite H10.
    dec (o_dec o1 o0); auto.
    rewrite H9 in *.
    discriminate.
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

Axiom RhoGetsMoreSpecific : forall r1 r2 a1 a2 s1 s2 S (H1 H2 : H) v1 (x : x),
  dynSemStar (H1, (r1, a1, s1) :: S) (H2, (r2, a2, s2) :: S) ->
             r1 x = Some v1 ->
  exists v2, r2 x = Some v2.
(*TODO - actually need to make sure stack isn't getting smaller in the meantime!*)

Lemma phiImpliesRefl : forall x, phiImplies x x.
Proof.
  unfold phiImplies.
  auto.
Qed.
Hint Resolve phiImpliesRefl.

Lemma AexceptEmptier : forall a b b', 
  Aexcept a b = [] -> Aexcept a (b' :: b) = [].
Proof.
  induction a; intros; simpl; try tauto.
  simpl in *.
  destruct (existsb (A'_d_decb a) b).
  - rewrite orb_true_r.
    simpl in *.
    apply IHa.
    assumption.
  - simpl in *.
    discriminate H0.
Qed.

Lemma AexceptSame : forall a, Aexcept a a = [].
Proof.
  induction a; simpl; try tauto.
  destruct a.
  undecb.
  simpl.
  dec (o_dec o0 o0).
  dec (string_dec f0 f0).
  simpl.
  apply AexceptEmptier.
  assumption.
Qed.

Lemma evalphiImplies : forall H' r A' q1 q2,
  phiImplies q1 q2 -> evalphi H' r A' q1 -> evalphi H' r A' q2.
Proof.
  intros.
  unfold phiImplies in H0.
  specialize (H0 H' r A').
  intuition.
Qed.

Lemma InReorder : forall {T : Type} (a : T) a1 a2 a3 a4,
  In a (a1 ++ a2 ++ a3 ++ a4) ->
  In a (a1 ++ a3 ++ a2 ++ a4).
Proof.
  intros.
  repeat rewrite in_app_iff in H0.
  repeat rewrite in_app_iff.
  intuition.
Qed.

Lemma sfrmeAccessReorder : forall p a1 a2 a3 a4,
  sfrme (a1 ++ a2 ++ a3 ++ a4) p ->
  sfrme (a1 ++ a3 ++ a2 ++ a4) p.
Proof.
  induction p0;
  intros;
  try constructor.
  - inversionx H0.
    apply InReorder.
    assumption.
  - inversionx H0.
    apply IHp0.
    assumption.
Qed.

Lemma sfrmphi'AccessReorder : forall p a1 a2 a3 a4,
  sfrmphi' (a1 ++ a2 ++ a3 ++ a4) p ->
  sfrmphi' (a1 ++ a3 ++ a2 ++ a4) p.
Proof.
  destruct p0;
  intros;
  constructor;
  inversionx H0;
  apply sfrmeAccessReorder;
  assumption.
Qed.

Lemma sfrmphiAccessReorder : forall p a1 a2 a3 a4,
  sfrmphi (a1 ++ a2 ++ a3 ++ a4) p ->
  sfrmphi (a1 ++ a3 ++ a2 ++ a4) p.
Proof.
  induction p0;
  intros;
  constructor;
  inversionx H0.
  - apply sfrmphi'AccessReorder.
    assumption.
  - rewrite app_assoc.
    rewrite app_assoc in H2.
    apply IHp0.
    assumption.
Qed.

Lemma sfrmphiApp' : forall p1 p2 a,
  sfrmphi a p1 ->
  sfrmphi (a ++ staticFootprint p1) p2 ->
  sfrmphi a (p1 ++ p2).
Proof.
  induction p1; intros; simpl in *.
  - rewrite app_nil_r in H1.
    assumption.
  - inversionx H0.
    intuition.
    apply IHp1; try auto.
    rewrite app_assoc_reverse.
    rewriteRev (app_nil_l (staticFootprint' a ++ a0 ++ staticFootprint p1)).
    apply sfrmphiAccessReorder.
    assumption.
Qed.

Lemma sfrmphiApp : forall p1 p2,
  sfrmphi [] p1 ->
  sfrmphi (staticFootprint p1) p2 ->
  sfrmphi [] (p1 ++ p2).
Proof.
  intros.
  apply sfrmphiApp'; simpl; assumption.
Qed.

Lemma rhoSubstId : forall x v r, rhoSubst x v r x = Some v.
Proof.
  intros.
  unfold rhoSubst.
  dec (x_dec x0 x0).
  tauto.
Qed.
    
Lemma phiImpliesPrefix : forall A B C,
  phiImplies A (B ++ C) -> phiImplies A B.
Proof.
  intros.
  unfold phiImplies in *.
  intros.
  apply H0 in H1.
  apply evalphiPrefix in H1.
  assumption.
Qed.

Lemma phiImpliesSuffix : forall A B C,
  phiImplies A (B ++ C) -> phiImplies A C.
Proof.
  intros.
  unfold phiImplies in *.
  intros.
  apply H0 in H1.
  apply evalphiSuffix in H1.
  assumption.
Qed.

Lemma hasDynamicTypeId : forall H t,
  hasDynamicType H (defaultValue t) t.
Proof.
  intros.
  destruct t; constructor.
Qed.


(* RemoveRhoSubst *)
Lemma evaleRemoveRhoSubst : forall e H r x v,
  ~ In x (FVe e) ->
  evale' H (rhoSubst x v r) e = evale' H r e.
Proof.
  induction e0;
  unfold evale in *;
  simpl in *;
  intros.
  - tauto.
  - unfold rhoSubst.
    dec (x_dec x0 x1);
    intuition.
  - destruct (evale' H0 (rhoSubst x0 v0 r) e0) eqn: eve;
    rewrite IHe0 in eve;
    auto;
    rewrite eve;
    tauto.
Qed.

Lemma evalphi'RemoveRhoSubst : forall p H r A x v,
  ~ In x (FV' p) ->
  evalphi' H (rhoSubst x v r) A p <->
  evalphi' H r A p.
Proof.
  intros.
  destruct p0; simpl;
  intuition;
  inversionx H2;
  simpl in *;
  eca;
  unfold evale in *;
  try erewrite evaleRemoveRhoSubst in *;
  eauto;
  intuition;
  unfold rhoSubst in *;
  dec (x_dec x1 x0);
  intuition.
Qed.

Lemma footprint'RemoveRhoSubst : forall p H r x v,
  ~ In x (FV' p) ->
  footprint' H (rhoSubst x v r) p =
  footprint' H r p.
Proof.
  destruct p0;
  intros;
  simpl;
  try tauto.
  
  simpl in *.
  rewrite evaleRemoveRhoSubst; auto.
Qed.

Lemma footprintRemoveRhoSubst : forall p H r x v,
  ~ In x (FV p) ->
  footprint H (rhoSubst x v r) p =
  footprint H r p.
Proof.
  induction p0;
  intros;
  simpl in *;
  try tauto.
  rewrite footprint'RemoveRhoSubst; intuition.
  rewrite IHp0; intuition.
Qed.

Lemma evalphiRemoveRhoSubst : forall p H r A x v,
  ~ In x (FV p) ->
  evalphi H (rhoSubst x v r) A p <->
  evalphi H r A p.
Proof.
  induction p0;
  intros.
  - split; constructor.
  - split; intros.
    * inversionx H2.
      simpl in *.
      rewrite footprint'RemoveRhoSubst in *; intuition.
      apply evalphi'RemoveRhoSubst in H12; intuition.
      apply IHp0 in H13; intuition.
      eca.
    * inversionx H2.
      simpl in *.
      eca;
      rewrite footprint'RemoveRhoSubst;
      intuition.
      + rewrite evalphi'RemoveRhoSubst; intuition.
      + rewrite IHp0; intuition.
Qed.

Definition option_alt {T : Type} (a : option T) (b : T) :=
  match a with
  | Some x => x
  | None => b
  end.

Definition rhoSubsts (x : list x) (rAlt : rho) (r : rho) : rho :=
  fold_right (fun x r => rhoSubst x (option_alt (rAlt x) (ve vnull)) r) r x.

Lemma evalphiRemoveRhoSubsts : forall p H r A v x,
  disjoint x (FV p) ->
  evalphi H (rhoSubsts x v r) A p <->
  evalphi H r A p.
Proof.
  induction x0; unfold rhoSubsts; intros; simpl in *.
  - tauto.
  - rewrite cons2app in H1.
    apply disjointSplitA in H1.
    inversionx H1.
    apply IHx0 in H3.
    unfold disjoint in H2.
    specialize (H2 a).
    rewrite evalphiRemoveRhoSubst; intuition.
Qed.

(*end RemoveRhoSubst*)

(* incl and sfrm *)
Lemma sfrmeIncl : forall p a b, incl a b -> sfrme a p -> sfrme b p.
Proof.
  induction p0;
  intros;
  inversionx H1; try constructor.
  - apply H0.
    assumption.
  - eapply IHp0; eauto.
Qed.

Lemma sfrm'Incl : forall p a b, incl a b -> sfrmphi' a p -> sfrmphi' b p.
Proof.
  intros.
  inversionx H1; try constructor;
  eapply sfrmeIncl; eauto.
Qed.

Lemma sfrmIncl : forall p a b, incl a b -> sfrmphi a p -> sfrmphi b p.
Proof.
  induction p0; intros.
  - constructor.
  - inversionx H1.
    eapply sfrm'Incl in H2; eauto.
    econstructor; eauto.
    eapply IHp0; eauto.
    Search incl.
    apply incl_app.
    * apply incl_appl.
      apply incl_refl.
    * apply incl_appr.
      assumption.
Qed.

Lemma sfrmdIncl : forall p a b, incl a b -> sfrmphid a p -> sfrmphid b p.
Proof.
  unfold sfrmphid.
  intros.
  eapp sfrmIncl.
Qed.
(* end incl and sfrm *)


Lemma phiImpliesTrans : forall p1 p2 p3,
  phiImplies p1 p2 ->
  phiImplies p2 p3 ->
  phiImplies p1 p3.
Proof.
  unfold phiImplies.
  intuition.
Qed.

Lemma edotSubst : forall m e f, exists e' f', (eSubsts m (edot e f)) = edot e' f'.
Proof.
  intros; simpl; repeat eexists; eauto.
Qed.


Lemma eSubstsEmpty : forall p, eSubsts [] p = p.
Proof.
  induction p0; simpl; try tauto.
  rewrite IHp0. tauto.
Qed.

Lemma phiSubstsEmpty : forall p, phiSubsts [] p = p.
Proof.
  induction p0; simpl; try tauto.
  rewrite IHp0.
  unfold phi'Substs.
  destruct a; repeat rewrite eSubstsEmpty; tauto.
Qed.


Lemma hasDynamicTypeDefault : forall H t,
  hasDynamicType H (defaultValue t) t.
Proof.
  intros.
  destruct t; simpl; constructor.
Qed.


Lemma phiImpliesAppCommA : forall p1a p1b p2,
  phiImplies (p1a ++ p1b) p2 ->
  phiImplies (p1b ++ p1a) p2.
Proof.
  unfold phiImplies.
  intros.
  apply evalphiSymm in H1.
  auto.
Qed.

Lemma evalphiTypeUnlift : forall x T H r A p,
  In (phiType x T) p -> evalphi H r A p -> evalphi' H r A (phiType x T).
Proof.
  induction p0; intros; inversionx H1.
  - inversionx H2.
    inversionx H11.
    econstructor; eauto.
  - apply IHp0; auto.
    inversionx H2.
    apply evalphiAexcept in H13.
    assumption.
Qed.

Lemma hasDynamicTypeHSubst : forall H v T o f x,
  hasDynamicType H v T <-> hasDynamicType (HSubst o f x H) v T.
Proof.
  split; intros.
  * inversionx H1; try constructor.
    dec (o_dec o1 o0).
    - eca.
      unfold HSubst.
      dec (o_dec o0 o0).
      rewrite H3.
      eauto.
    - eca.
      unfold HSubst.
      rename de2 into des.
      dec (o_dec o1 o0); try tauto.
      eauto.
  * inversionx H1; try constructor.
    unfold HSubst in *.
    dec (o_dec o1 o0).
    - destruct (H0 o0) eqn: H0e; try discriminate.
      destruct p0. inversionx H3.
      eca.
    - eca.
Qed.

Lemma phiImpliesStaticType : forall p1 p2 e T,
  phiImplies p1 p2 -> 
  hasStaticType p2 e T -> 
  hasStaticType p1 e T.
Proof.
  induction e0; intros; inversionx H1; try constructor.
  - unfold phiImplies in *.
    intros.
    apply H4.
    apply H0.
    assumption.
  - econstructor; eauto.
    eapply phiImpliesTrans; eauto.
Qed.

Lemma evalphiImpliesType : forall H r A p x T,
  evalphi H r A p -> phiImplies p [phiType x T] -> ehasDynamicType H r (ex x) T.
Proof.
  intros.
  apply H2 in H1.
  inversionx H1.
  inversionx H12.
  unfold ehasDynamicType.
  eexists; eauto.
Qed.



Lemma FVeMaxOne : forall e x1 x2,
  In x1 (FVe e) ->
  In x2 (FVe e) ->
  x1 = x2.
Proof.
  induction e0; simpl; intros; intuition; subst; auto.
Qed.

Lemma ehasDynamicTypeRemoveRhoSubst : forall H r e x v T,
  ¬ In x (FVe e) ->
  ehasDynamicType H r e T ->
  ehasDynamicType H (rhoSubst x v r) e T.
Proof.
  intros.
  unfold ehasDynamicType, evale in *.
  rewrite evaleRemoveRhoSubst; eauto.
Qed.

Lemma evalphiImpliesAccess : forall H r p A,
  evalphi H r A p ->
  incl (footprint H r p) A.
Proof.
  induction p0; intros; simpl in *.
  - apply inclEmpty.
  - inversionx H1.
    apply IHp0 in H12.
    apply inclAexcept in H12.
    apply incl_app; auto.
Qed.



Lemma AexceptAppFirst : forall B A2 A1,
  Aexcept (A1 ++ A2) B = Aexcept A1 B ++ Aexcept A2 B.
Proof.
  induction A1; intros; simpl in *; try tauto.
  rewrite IHA1.
  destruct (existsb (A'_d_decb a) B); simpl; tauto.
Qed.

Lemma AexceptReduceSecond : forall a aa A,
  ~ In a A ->
  Aexcept A (a :: aa) = Aexcept A aa.
Proof.
  induction A; intros; simpl in *; try tauto.
  apply not_or_and in H0. unf.
  apply IHA in H2.
  rewrite H2.
  undecb.
  destruct a0, a. simpl.
  dec (o_dec o0 o1); try tauto.
  dec (string_dec f0 f1); try tauto.
Qed.

Lemma fieldsDistinct : forall c l,
      fields c = Some l ->
      listDistinct (map snd l).
Proof.
  intros.
  assert (fi := H0).
  unfold fields in H0.
  destruct (class c) eqn: cc; try discriminate.
  destruct c0.
  apply IsClassWellDef in cc.
  unfold CWellDefined in cc. unf.
  inversionx H0.
  generalize l0 H1. clear.
  induction l0; intros; simpl in *; auto.
  unf. apply IHl0 in H2. intuition.
  contradict H0.
  destruct a. simpl in *.
  apply in_map_iff in H1. unf.
  apply in_map_iff in H3. unf.
  destruct x0. simpl in *. subst.
  destruct x1. inversionx H3.
  apply in_map_iff.
  eex.
  simpl.
  tauto.
Qed.


Lemma inclAexcept2 : forall A1 A2 B,
  incl A1 A2 ->
  incl (Aexcept A1 B) (Aexcept A2 B).
Proof.
  unfold incl, Aexcept, except.
  intros.
  apply filter_In.
  apply filter_In in H1.
  intuition.
Qed.

Lemma evalphiIncl : forall H r p A1 A2,
  incl A1 A2 ->
  evalphi H r A1 p ->
  evalphi H r A2 p.
Proof.
  induction p0; intros; simpl in *; try constructor.
  inversionx H2.
  eca.
  - eapp incl_tran.
  - eapp IHp0.
    eapp inclAexcept2.
Qed.

Lemma evalphiNarrowAccess : forall H r p A,
  evalphi H r A p ->
  evalphi H r (footprint H r p) p.
Proof.
  induction p0; intros; simpl in *; try constructor.
  inversionx H1.
  destruct a; eca; simpl in *;
  try apply inclEmpty;
  try rewrite AexceptEmpty;
  intuition;
  try eapp IHp0.
  
  inversionx H11.
  destruct (evale' H0 r e0); try tauto.
  destruct v0; try tauto.
  simpl.
  undecb.
  simpl.
  dec (o_dec o1 o1).
  dec (string_dec f0 f0).
  simpl.
  rewrite AexceptReduceSecond.
    rewrite AexceptEmpty.
    eapp IHp0.
  apply evalphiImpliesAccess in H12.
  specialize (H12 (o1, f0)).
  intuition.
  apply InAexceptNot in H2.
  intuition.
Qed.
  
