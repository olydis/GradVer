Load GradVer1Ltac.

Lemma cons2app : forall {T} (x : T) xs,
  x :: xs = [x] ++ xs.
Proof.
  intuition.
Qed.
Lemma cons2app2 : forall {T} (x1 x2 : T) xs,
  x1 :: x2 :: xs = [x1 ; x2] ++ xs.
Proof.
  intuition.
Qed.


Lemma mapConcat : forall {T U : Type} (f : T -> U) xs,
  map f (concat xs) = flat_map (map f) xs.
Proof.
  intros.
  rewrite flat_map_concat_map.
  rewrite concat_map.
  tauto.
Qed.

Lemma InRemove : forall {T : Type} (x : T) x' xs de,
  In x (remove de x' xs) ->
  In x xs.
Proof.
  induction xs; intros; simpl in *; try tauto.
  des (de x'0 a).
  - eappIn IHxs H0.
  - inversionx H0; auto.
    eappIn IHxs H1.
Qed.

Lemma NoDupRemove : forall {T : Type} (x : T) xs de,
  NoDup xs ->
  NoDup (remove de x xs).
Proof.
  induction xs; intros; simpl in *; auto.
  inversionx H0.
  eappIn IHxs H4.
  destruct (de x0 a); eauto.
  constructor; auto.
  unfold not. intro. contradict H3.
  apply InRemove in H0.
  assumption.
Qed.

Lemma disjointSplitA : forall {A} (l1 l2a l2b : list A),
  disjoint (l2a ++ l2b) l1 ->
  disjoint l2a l1 /\ disjoint l2b l1.
Proof.
  unfold disjoint.
  split; intros;
  specialize (H0 x0);
  intuition.
Qed.

Lemma disjointSplitB : forall {A} (l1 l2a l2b : list A),
  disjoint l1 (l2a ++ l2b) ->
  disjoint l1 l2a /\ disjoint l1 l2b.
Proof.
  unfold disjoint.
  split; intros;
  specialize (H0 x0);
  intuition.
Qed.

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


Lemma inclApp : forall {T : Type} (A1 A2 B : list T),
  incl (A1 ++ A2) B ->
  incl A1 B /\ incl A2 B.
Proof.
  unfold incl.
  intros.
  intuition.
Qed.


Lemma flat_map_app : forall {T U : Type} (f : T -> list U) l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros.
  rewrite flat_map_concat_map.
  rewrite map_app.
  rewrite concat_app.
  repeat rewriteRev flat_map_concat_map.
  tauto.
Qed.

Lemma filterApp : forall {T : Type} (f : T -> bool) a b,
  filter f (a ++ b) = filter f a ++ filter f b.
Proof.
  induction a; intros; simpl in *; try tauto.
  rewrite IHa.
  destruct (f0 a); tauto.
Qed.

Lemma in_concat : forall {T : Type} (x : T) xss,
  In x (concat xss) <->
  exists xs, In xs xss /\ In x xs.
Proof.
  induction xss; intros; simpl in *.
  - split; try tauto.
    intros. unf. tauto.
  - rewrite in_app_iff.
    rewrite IHxss.
    split; intros.
    * inversionx H0.
      + eex.
      + unf.
        eex.
    * unf.
      inversionx H0; auto.
      apply or_intror.
      eex.
Qed.