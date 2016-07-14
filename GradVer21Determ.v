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
  | phiAcc e f =>  match evale' h r e with
                   | Some (vo o) => inB A'_d_dec (o, f) a
                   | _ => false
                   end
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
    * destruct (evale' h r e) eqn: ev; cut.
      destruct v; cut.
      eca.
      eapply inB_In; eauto.
    * inv H.
      rewrite H6.
      apply inB_In.
      auto.
Qed.


  
  
  
  
