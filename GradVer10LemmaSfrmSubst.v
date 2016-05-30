Load GradVer9Ltac.
Import Semantics.


Definition A_sSubsts m (A : A_s) : A_s := 
  flat_map (fun p =>
    match p with
    | phiAcc x f => [(x, f)]
    | _ => []
    end
  )
  (phiSubsts m (map (fun a => phiAcc (fst a) (snd a)) A)).


Definition mMapsTo (m : list (x * e)) (x' : x) : Prop :=
  exists m', In m' m /\ FVeo (snd m') = Some x'.

Definition mMapsToUnique (m : list (x * e)) (x' : x) : Prop :=
  forall f1 f2 e1 e2, 
      In (f1, e1) m -> 
      In (f2, e2) m -> 
      FVeo e1 = Some x' -> 
      FVeo e2 = Some x' -> 
      f1 = f2
.

(* sfrme (A_sSubsts (a => b) (a.f)) (eSubsts (a => b) (b.f)) -> sfrme (a.f) (b.f) *)
Lemma sfrmeSubst : forall m e a,
      (forall x, mMapsToUnique m x /\ (mMapsTo m x -> (~ In x (FVe e) /\ ~ In x (FVA_s a)))) ->
      sfrme (A_sSubsts m a) (eSubsts m e) ->
      sfrme a e.
Proof.
  intros.
  destruct e0; try constructor.
  simpl in *;
  try apply inclEmpty;
  try constructor.
  inversionx H1.
  destruct e0; simpl in H0; inversionx H2.
  constructor.
  destruct (find (λ r : x * e, x_decb x1 (fst r)) m0) eqn: ff.
  - destruct p0.
    subst.
    apply find_some in ff.
    inversionx ff.
    dec (x_dec x1 (fst (x2, ex x0))); try inversionx H2.
    simpl in *.
    unfold A_sSubsts in H4.
    apply in_flat_map in H4.
    inversionx H4.
    inversionx H2.
    destruct x3; inversionx H4; inversionx H2.
    unfold phiSubsts, phi'Substs in H3.
    simpl in *.
    apply in_map_iff in H3.
    inversionx H3.
    inversionx H2.
    apply in_map_iff in H4.
    inversionE H4.
    inversionx H2.
    destruct x4.
    simpl in *.
    destruct (find (λ r : x * e, x_decb x3 (fst r)) m0) eqn: fff1; inversionx H3.
    * destruct p0. destruct e0; inversionx H4.
      apply find_some in fff1.
      inversionx fff1.
      simpl in *.
      dec (x_dec x3 x4); inversionx H3.
      specialize (H0 x0).
      inversionx H0.
      unfold mMapsToUnique in H3.
      eapply H3 in H1; eauto.
      subst.
      assumption.
    * specialize (H0 x0).
      inversionx H0.
      assert (mMapsTo m0 x0).
        eexists; eauto.
      intuition.
      unfold FVA_s in H6.
      rewrite in_map_iff in H6.
      contradict H6.
      eexists; split; eauto.
      auto.
  - inversionx H3.
    unfold A_sSubsts in H4.
    apply in_flat_map in H4.
    inversionx H4.
    inversionx H1.
    destruct x0; inversionx H3; try inversionx H1.
    unfold phiSubsts in H2.
    apply in_map_iff in H2.
    inversionx H2.
    inversionx H1.
    unfold phiSubsts, phi'Substs in H2.
    destruct x0; inversionx H2.
    * destruct (find (λ r : x * e, x_decb x0 (fst r)) m0) eqn: ff1.
      + destruct p0.
        destruct e0; inversionx H4.
        apply find_some in ff1.
        inversionx ff1.
        simpl in H2.
        dec (x_dec x0 x2); inversionx H2.
        apply in_map_iff in H3.
        inversionx H3.
        inversionx H2.
        inversionx H3.
        destruct x3.
        simpl in *.
        specialize (H0 x1).
        inversionx H0.
        assert (mMapsTo m0 x1).
          eexists; eauto.
        intuition.
      + inversionx H4.
        apply in_map_iff in H3.
        inversionx H3.
        inversionx H1. 
        inversionx H2.
        destruct x0.
        simpl.
        assumption.
    * apply in_map_iff in H3.
      inversionx H3.
      inversionx H1.
      inversionx H2.
Qed.

Lemma sfrmeSubstEmpty : forall m e,
      sfrme [] (eSubsts m e) -> sfrme [] e.
Proof.
  intros.
  destruct e0; try constructor.
  simpl in *.
  inversionx H0.
  inversion H3.
Qed.

Lemma sfrmphi'Subst : forall m e a,
     (forall x, mMapsToUnique m x /\ (mMapsTo m x -> (~ In x (FV' e) /\ ~ In x (FVA_s a)))) ->
      sfrmphi' (A_sSubsts m a) (phi'Substs m e)
      ->
      sfrmphi' a e.
Proof.
  intros.
  destruct e0; constructor;
  inversionx H1;
  apply (sfrmeSubst m0); intuition;
  try apply H0;
  apply H0 in H1;
  inversionx H1;
  intuition;
  contradict H3;
  simpl;
  intuition.
Qed.

(* counter-examples:
sfrmphi [] (phiSubsts (a => c, b => c) (acc(b.f) * a.f = 3)) ->
sfrmphi [] (acc(b.f) * a.f = 3)

sfrmphi [] (phiSubsts (a => b) (acc(b.f) * a.f = 3)) ->
sfrmphi [] (acc(b.f) * a.f = 3)

sfrmphi [] (phiSubsts (b => a) (acc(b.f) * a.f = 3)) ->
sfrmphi [] (acc(b.f) * a.f = 3)
*)

Lemma sfrmphiSubst : forall e m a,
     (forall x, mMapsToUnique m x /\ (mMapsTo m x -> (~ In x (FV e) /\ ~ In x (FVA_s a)))) ->
      sfrmphi (A_sSubsts m a) (phiSubsts m e)
      ->
      sfrmphi a e.
Proof.
  induction e0; intros; constructor.
  - inversionx H1.
    eapply sfrmphi'Subst; eauto.
    intros.
    split; try apply H0.
    intros.
    apply H0 in H1.
    inversionx H1.
    intuition.
    contradict H4.
    simpl.
    intuition.
  - inversionx H1.
    apply (IHe0 m0); intros.
    * specialize (H0 x0).
      inversionx H0.
      intuition.
      + contradict H4.
        simpl.
        intuition.
      + destruct a; simpl in *; intuition.
    * destruct a; simpl in *; intuition.
      destruct (find (λ r : x * e, x_decb x0 (fst r)) m0); intuition.
      destruct p0.
      destruct e1; intuition.
Qed.
