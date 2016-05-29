Load GradVer1Ltac.

Lemma InSingle : forall {T : Type} (x y : T), In x [y] -> x = y.
Proof.
  intros.
  inversionx H0; intuition.
Qed.
Ltac insing H := apply InSingle in H; inversionx H.

Lemma inclEmpty : forall {T : Type} (x : list T), incl [] x.
Proof.
  unfold incl.
  intros.
  inversion H0.
Qed.

Lemma inclSingle : forall {T : Type} (xs : list T) x, 
  incl [x] xs <-> In x xs.
Proof.
  split; unfold incl; intros.
  - apply H0.
    constructor.
    tauto.
  - inversionx H1.
    * assumption.
    * inversion H2.
Qed.

Lemma inclEmptyFalse : forall {T : Type} (x : T) xs,
  ~ incl (x :: xs) [].
Proof.
  intuition.
  unfold incl in H0.
  specialize (H0 x0).
  assert (In x0 (x0 :: xs)). apply in_eq.
  intuition.
Qed.

Lemma incl_cons_reverse : forall {T : Type} (x : T) xs ys,
  incl (x :: xs) ys -> incl xs ys /\ In x ys.
Proof.
  unfold incl.
  intuition.
Qed.


Lemma lengthId : forall {A : Type} (a b : list A), a = b -> Datatypes.length a = Datatypes.length b.
Proof.
  intros.
  rewrite H0.
  tauto.
Qed.

Lemma infRecList : forall {T : Type} (x : T) (xs : list T), ~ x :: xs = xs.
Proof.
  intuition.
  apply lengthId in H0.
  simpl in H0.
  contradict H0.
  auto with arith.
Qed.

Lemma exists_forall : forall {A : Type} (b : A -> Prop) (c : Prop), ((exists a, b a) -> c) -> (forall a, b a -> c).
Proof.
  intros.
  apply H0.
  eauto.
Qed.