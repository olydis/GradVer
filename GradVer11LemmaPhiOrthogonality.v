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
  specialize (H2 h (rhoSubsts (FV' p0) x1 r) (x2 ++ a)).
  rewrite (evalphiRemoveRhoSubsts p2) in H2; auto.
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
  
  
  
  
  
  
  
