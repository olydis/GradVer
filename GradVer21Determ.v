Load GradVer20Hook_import.
Import Semantics.

Definition inB {T:Type} (eq_dec : ∀ n m : T, {n = m} + {n ≠ m}) (x : T) (xs : list T) : bool :=
  if in_dec eq_dec x xs
  then true
  else false.

Lemma inB_In : forall {T:Type} ed (x : T) xs,
  inB ed x xs = true <-> In x xs.
Proof.
  intros.
  unfold inB.
  destruct in_dec; cut.
  split; cut.
Qed.

Definition inclB {T:Type} (eq_dec : ∀ n m : T, {n = m} + {n ≠ m}) (xs1 xs2 : list T) : bool :=
  forallb (fun x => inB eq_dec x xs2) xs1.

Lemma inclB_incl : forall {T:Type} ed (xs2 xs1 : list T),
  inclB ed xs1 xs2 = true <-> incl xs1 xs2.
Proof.
  unfold inclB.
  induction xs1;
  intros; simpl in *;
  split; intros.
  - apply inclEmpty.
  - auto.
  - apply andb_true_iff in H. unf.
    apply inB_In in H0.
    apply incl_cons; cut.
  - apply andb_true_iff.
    rewrite inB_In.
    rewrite IHxs1.
    apply incl_cons_reverse in H.
    cut.
Qed.


Definition evalphi'B (h : H) (r : rho) (a : A_d) (p : phi') : bool :=
  match p with
  | phiTrue => true
  | phiEq e1 e2 => match evale' h r e1 with
                   | None => false
                   | Some v1 => 
                     match evale' h r e2 with
                     | None => false
                     | Some v2 => v_decb v1 v2
                     end
                   end
  | phiNeq e1 e2 =>match evale' h r e1 with
                   | None => false
                   | Some v1 => 
                     match evale' h r e2 with
                     | None => false
                     | Some v2 => negb (v_decb v1 v2)
                     end
                   end
  | phiAcc e f =>  match evale' h r (edot e f) with
                   | Some _ =>
                     match evale' h r e with
                     | Some (vo o) => inB A'_d_dec (o, f) a
                     | _ => false
                     end
                   | None => false
                   end
  end.

Fixpoint evalphiB (h : H) (r : rho) (a : A_d) (p : phi) : bool :=
  match p with
  | [] => true
  | p' :: p => evalphi'B h r a p'
            && evalphiB h r (Aexcept a (footprint' h r p')) p
  end.

Lemma evalphi'B_works : forall h r a p,
  evalphi'B h r a p = true <->
  evalphi'  h r a p.
Proof.
  intros.
  unfold evalphi'B.
  destruct p0.
  - split; cut.
  - split; intros.
    * destruct (evale' h r e) eqn: ev1; cut.
      destruct (evale' h r e0) eqn: ev2; cut.
      eca.
      dec v_dec; cut.
    * inv H.
      rewrite H3, H7.
      dec v_dec; auto.
  - split; intros.
    * destruct (evale' h r e) eqn: ev1; cut.
      destruct (evale' h r e0) eqn: ev2; cut.
      eca.
      dec v_dec; cut.
    * inv H.
      rewrite H3, H7.
      dec v_dec; auto.
  - split; intros.
    * destruct evale' eqn: ev1; cut.
      destruct (evale' h r e) eqn: ev2; cut.
      destruct v0; cut.
      eca.
      eapply inB_In; eauto.
    * inv H.
      rewrite H7.
      rewrite H3.
      apply inB_In.
      auto.
Qed.

Lemma evalphiB_works : forall h r p a,
  evalphiB h r a p = true <->
  evalphi  h r a p.
Proof.
  induction p0; intros; simpl in *. split; cut.
  rewrite andb_true_iff.
  rewrite IHp0.
  rewrite evalphi'B_works.
  split; intros.
  - unf.
    eca.
    * eapp evalphi'ImpliesIncl.
    * eapp evalphi'FootprintAccess.
  - inv H.
    splau.
    inv H9;
    eca.
Qed.
  
  
  
