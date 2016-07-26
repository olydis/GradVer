Load GradVer14LemmaAliasing.
(* Load GradVer12LemmaFootprint. *)
Import Semantics.



Definition phiOrthogonal (p1 p2 : phi) := disjoint (FV p1) (FV p2).

Definition phiIsIndependentVar (x : x) (p : phi) := forall H r A v,
  evalphi H r A p -> evalphi H (rhoSubst x v r) A p.

Lemma phiImpliesSatisfiable : forall p1 p2,
  phiImplies p1 p2 ->
  phiSatisfiable p1 ->
  phiSatisfiable p2.
Proof.
  unfold phiImplies, phiSatisfiable.
  intros.
  unf.
  repeat eexists.
  apply H0.
  eauto.
Qed.

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

Lemma disjointAppA : forall {T : Type} (p1a p1b p2 : list T),
  disjoint (p1a ++ p1b) p2 <->
  disjoint p1a p2 /\
  disjoint p1b p2.
Proof.
  unfold disjoint in *.
  split; intros.
  - split; intros; specialize (H0 x0); intuition.
  - intuition.
    rewrite in_app_iff.
    specialize (H1 x0).
    specialize (H2 x0).
    intuition.
Qed.

Lemma phiOrthogonalAppA : forall p1a p1b p2,
  phiOrthogonal (p1a ++ p1b) p2 <->
  phiOrthogonal p1a p2 /\
  phiOrthogonal p1b p2.
Proof.
  unfold phiOrthogonal in *.
  intros;
  rewrite FVApp in *.
  apply disjointAppA.
Qed.

Definition vWithOmap (omap : o -> o) (v' : v) : v :=
  match v' with
  | vo o => vo (omap o)
  | _ => v'
  end.
Definition rhoWithOmap (omap : o -> o) (r : rho) : rho :=
  fun x => option_map
           (vWithOmap omap)
           (r x).

(* Definition colocateH (H0 H1 : H) := λ o : nat,
       match modulo o 2 with
       | 0 => H0 (div o 2)
       | Datatypes.S _ => H1 (div (o - 1) 2)
       end.

Definition colocateRho (xs0 : list x) (r0 r1 : rho) := λ x,
       if existsb (x_decb x) xs0
       then rhoWithOmap (λ o, 2 * o) r0 x
       else rhoWithOmap (λ o, 2 * o + 1) r1 x.

Definition colocateAccess (A0 A1 : A_d) :=
    map (fun x => (2 * (fst x)    , snd x)) A0 ++ 
    map (fun x => (2 * (fst x) + 1, snd x)) A1. *)


(* Require Import Coq.Logic.FunctionalExtensionality.

Lemma colocateRhoEmpty : forall r0 r1,
  colocateRho [] r0 r1 = rhoWithOmap (λ o, 2 * o + 1) r1.
Proof.
  intros.
  unfold colocateRho.
  apply functional_extensionality.
  simpl.
  tauto.
Qed. *)

(*
Lemma phiSatisfiableAppHelper : forall p0 p1 H0 H1 r0 r1 A0 A1,
  (∀ x, ¬ In x (FV p0) ∨ ¬ In x (FV p1)) ->
  evalphi H0 r0 A0 p0 ->
  evalphi H1 r1 A1 p1 ->
  evalphi
    (colocateH H0 H1)
    (colocateRho (FV p0) r0 r1)
    (colocateAccess A0 A1)
    (p0 ++ p1).
Proof.
  induction p0.
  - induction p1; intros; simpl in *; try constructor.
    inversionx H4.
    eca.
    * apply incl_appr.
      generalize A1 H2 H9. clear.
      induction A1; intros; simpl in *.
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
Lemma evale'RemoveRhoSubstsVo : forall h r r' e o,
  evale' h (rhoSubsts (FVe e) r' r) e = Some (vo o) <->
  evale' h r' e = Some (vo o).
Proof.
  induction e0; intros; simpl in *.
  - tauto.
  - unfold rhoSubst.
    dec (x_dec x0 x0).
    destruct (r' x0); simpl; split; intros; try tauto; inversion H0.
  - destruct (evale' h r' e0);
    destruct (evale' h (rhoSubsts (FVe e0) r' r) e0);
    try destruct v0;
    try destruct v1;
    try tauto;
    specialize (IHe0 o1); unf; intuition;
    inversionx H2;
    assumption.
Qed.
  
Lemma footprint'RemoveRhoSubsts2 : forall h r r' p,
  footprint' h (rhoSubsts (FV' p) r' r) p = 
  footprint' h r' p.
Proof.
  intros.
  destruct p0; simpl; try tauto.
  assert (ee := evale'RemoveRhoSubstsVo h r r' e0).
  destruct (evale' h r' e0);
  destruct (evale' h (rhoSubsts (FVe e0) r' r) e0);
  try destruct v0;
  try destruct v1;
  try tauto;
  specialize (ee o0);
  intuition;
  inversionx H2.
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
  - apply evaleRhoDefinedAt in H4.
    intuition.
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
  * apply evale'RemoveRhoSubstsVo in H3.
    assumption.
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

(* Definition invNoAlias
  (Heap : H) (rho : rho) (A : A_d) (phi : phi) : Prop :=
    let sfp := staticFootprint phi in
      forall f x1 x2, 
        In (e1, f) sfp ->
        In (e2, f) sfp ->
        evale H rho e1 <> rho x2. *)
        
(* x = 3 * x = y => y = 3 *)
(* BUT NOT x = y => y = 3 *)

(* x = 3 * y = 3 => y = 3 *)
(* BUT NOT x = y => y = 3 *)

(* x = 3 * x = y => y : int *)
(* BUT NOT x = y => y : int *)

 (* 
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

  assert (disj) 
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
Admitted.*)

Definition envIdenticalAt
  (xs : list x)
  (H0 : H) (r0 : rho) (A0 : A_d)
  (H1 : H) (r1 : rho) (A1 : A_d) : Prop :=
  (forall x, In x xs -> r0 x = r1 x) /\
  (forall o, (exists x, r0 x = Some (vo o)) ->
    H0 o = H1 o /\
    forall f, In (o, f) A0 <-> In (o, f) A1).
Definition envEqualsAt
  (xs : list x)
  (H0 : H) (r0 : rho) (A0 : A_d)
  (H1 : H) (r1 : rho) (A1 : A_d) : Prop :=
  forall (p : phi),
    incl (FV p) xs ->
    (evalphi H0 r0 A0 p <-> evalphi H1 r1 A1 p).

(* Lemma envIdenticalEquals : forall xs H0 r0 A0 H1 r1 A1,
  envIdenticalAt xs H0 r0 A0 H1 r1 A1 ->
  envEqualsAt    xs H0 r0 A0 H1 r1 A1.
Proof.
  unfold envIdenticalAt, envEqualsAt.
  induction xs;
  intros;
  simpl in *.
  - generalize p0 H3. clear.
    induction p0; intros; try (split; intros; constructor).
    simpl in *.
    assert (incl (FV p0) []). unfold incl in *. intuition.
    assert (incl (FV' a) []). unfold incl in *. intuition.
    intuition.
    * .
    destruct p0; try (split; intros; constructor).
    simpl in *.
    
    rewrite inclEmptyFalse in H3.
  unfold  *)

(*colocate H r A without touching , so that p still holds, *)
Lemma evalphiRelocate : forall xs H1 r1 A1 H0 r0 A0 p,
  disjoint xs (FV p) ->
  evalphi H0 r0 A0 p ->
  exists Hx rx Ax,
    evalphi Hx rx Ax p /\
    envEqualsAt xs H1 r1 A1 Hx rx Ax.
Proof.
  induction xs; intros; simpl in *.
  - repeat eexists; eauto.
Admitted.

Lemma evalphiAppRev : ∀ (p1 p2 : list phi') (H : H) (r : rho) (A : A_d),
      evalphi H r A p1 ∧ evalphi H r (Aexcept A (footprint H r p1)) p2
      -> evalphi H r A (p1 ++ p2).
Proof.
  induction p1; intros; simpl in *; unf.
  - common.
    assumption.
  - inversionx H2.
    eca.
    apply IHp1.
    rewrite AexceptApp.
    intuition.
Qed.


Lemma phiImpliesNarrowing : forall p0 p1 p2,
  phiOrthogonal p1 p0 ->
  phiOrthogonal p2 p0 ->
  phiSatisfiable p0 ->
  phiSatisfiable p1 ->
  phiImplies (p0 ++ p1) p2 ->
  phiImplies p1 p2.
Proof.
  unfold phiImplies. intros.
  unfold phiSatisfiable in H2.
  unf.
  assert (disjoint (FV p1 ++ FV p2) (FV p0)).
    unfold phiOrthogonal in *.
    rewrite disjointAppA.
    auto.
  eapply (evalphiRelocate (FV p1 ++ FV p2) h r a) in H6; auto.
  unf.
  specialize (H4 x3 x4 x5).
  assert (incl (FV p1) (FV p1 ++ FV p2)). intuition.
  assert (incl (FV p2) (FV p1 ++ FV p2)). intuition.
  assert (evalphi x3 x4 x5 (p0 ++ p1)).
    apply evalphiAppRev.
    intuition.
    specialize (H8 p1).
    intuition.
Admitted.

(* x = 3 * x = y => y = 3 *)
(* BUT NOT x = y => y = 3 *)

(* x = 3 * x = y => y : int *)
(* BUT NOT x = y => y : int *)

Lemma hasStaticTypeNarrowing : forall p0 p1 e T,
  disjoint (FV p1) (FV p0) ->
  disjoint (FVe e) (FV p0) ->
  phiSatisfiable p0 ->
  phiSatisfiable p1 ->
  hasStaticType (p0 ++ p1) e T ->
  hasStaticType p1 e T.
Proof.
  induction e0;
  intros;
  inversionx H4;
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
  
*)