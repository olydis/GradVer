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


Definition mMapsTo (m : list (x * x)) (x' : x) : Prop :=
  exists m', In m' m /\ snd m' = x'.

Definition mMapsToUnique (m : list (x * x)) (x' : x) : Prop :=
  forall f1 f2 x1 x2, 
      In (f1, x1) m -> 
      In (f2, x2) m -> 
      x1 = x' -> 
      x2 = x' -> 
      f1 = f2
.

(* sfrme (A_sSubsts (a => b) (a.f)) (eSubsts (a => b) (b.f)) -> sfrme (a.f) (b.f) *)
Lemma sfrmeSubst : forall m e a,
      (forall x, mMapsToUnique m x /\ (mMapsTo m x -> (~ In x (FVe e) /\ ~ In x (FVA_s a)))) ->
      sfrme (A_sSubsts m a) (eSubsts m e) ->
      sfrme a e.
Proof.
  induction e0; intros; try (constructor; fail).
  inversionx H1.
  constructor; try (apply IHe0; auto).
  generalize a H0 H5. clear.

  induction a; intros; simpl in *; try tauto.
  inversionx H5.
  - destruct a. simpl in *.
    inversionx H1.
    assert (CL := classic (e0 = e1)).
    inversionx CL; subst; eauto.
    contradict H1.
    generalize e0 e1 H3 H0. clear.
    induction e0; intros; simpl in *;
    destruct e1; simpl in *; inversionx H3; try tauto.
    * unfold mMapsToUnique in *.
      unfold xSubsts in *.
      destruct (find (λ r : x * x, x_decb x0 (fst r)) m0) eqn: ff0;
      destruct (find (λ r : x * x, x_decb x1 (fst r)) m0) eqn: ff1.
      + destruct p0, p1.
        subst.
        apply find_some in ff0. unf.
        apply find_some in ff1. unf.
        simpl in *.
        dec (x_dec x1 x4); inversionx H4.
        dec (x_dec x0 x2); inversionx H2.
        specialize (H0 x3).
        unf.
        eapply H2 in H1; eauto.
        subst.
        tauto.
      + destruct p0.
        subst.
        apply find_some in ff0. unf.
        eapply find_none in ff1; eauto.
        simpl in *.
        dec (x_dec x3 x2); inversionx ff1. rename de2 into asd.
        dec (x_dec x0 x2); inversionx H2.
        specialize (H0 x3).
        unf. assert (mMapsTo m0 x3). eexists; eauto. intuition.
      + destruct p0.
        subst.
        apply find_some in ff1. unf.
        eapply find_none in ff0; eauto.
        simpl in *.
        dec (x_dec x0 x2); inversionx ff0. rename de2 into asd.
        dec (x_dec x1 x2); inversionx H2.
        specialize (H0 x0).
        unf. assert (mMapsTo m0 x0). eexists; eauto. intuition.
      + subst.
        tauto.
    * apply IHe0 in H2; subst; intuition.
  - apply or_intror.
    eapply IHa; auto.
    intros.
    specialize (H0 x0).
    unfold FVA_s in *.
    simpl in *.
    intuition.
Qed.

Lemma sfrmeSubstEmpty : forall m e,
      sfrme [] (eSubsts m e) -> sfrme [] e.
Proof.
  intros.
  induction e0; try constructor;
  simpl in *;
  inversionx H0;
  inversion H4.
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
      unf.
      intuition.
      + contradict H4.
        simpl.
        intuition.
      + destruct a; simpl in *; intuition.
        unfold FVA_s in *.
        apply in_flat_map in H5.
        unf.
        apply in_map_iff in H5.
        unf.
        subst.
        inversionx H9; simpl in *; intuition.
        contradict H6.
        apply in_flat_map.
        eexists; split; eauto.
        apply in_map_iff.
        eexists; split; eauto.
    * destruct a; simpl in *; intuition.
Qed.
