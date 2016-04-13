Require Import Coq.Unicode.Utf8 Arith Bool Ring Setoid String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Sets.Powerset.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Logic.Decidable.
Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.FunctionalExtensionality.

Open Scope string_scope.

(*lambda calculus*)
Definition var := string.
Definition varset := string -> bool.

Inductive term :=
| Var : var -> term
| App : term -> term -> term
| Abs : var -> term -> term.

Fixpoint free (t : term) : varset :=
match t with
| Var x => (fun v => if string_dec x v then true else false)
| App a b => (fun v => free a v || free b v)
| Abs x e => (fun v => if string_dec x v then false else free e v)
end.


(*combinators*)

Eval compute in 0.
Eval compute in (pred 0).

Print le.

Eval compute in 0 < 2.

(*semantics*)
Fixpoint D (n : nat) : Set :=
match n with
| O => option False
| S m => option (D m -> D m)
end.
Definition DBottom {n : nat} : D n :=
match n with
| O => None
| S m => None
end.

Ltac unD0 := 
  match goal with
    [ x : D 0 |- _ ] => 
      (destruct x as [ x | _ ]; try inversion x)
  end.

Theorem D0singleton : forall a : D 0, a = None.
Proof.
  intros.
  unD0.
  tauto.
Qed.

Fixpoint abrI {n : nat} : D n -> D (S n) :=
  match n with
  | O => λ _, None
  | S m => λ d,
      match d with
      | None => None
      | Some f => Some (λ x, abrI (f (abrJ x)))
      end
  end
with abrJ {n : nat} : D (S n) -> D n :=
  match n with
  | O => λ _, None
  | S m => λ d,
      match d with
      | None => None
      | Some f => Some (λ x, abrJ (f (abrI x)))
      end
  end
.

(*
Fixpoint abrJstar {n m : nat} (d : D n) (p : n >= m) : D m.
Proof.
  unfold ge in *.
  apply le_lt_eq_dec in p.
  destruct p.
  - destruct n.
    * contradict l.
      auto with arith.
    * apply abrJ in d.
      apply (abrJstar n m d).
      auto with arith.
  - subst.
    assumption.
Defined.
*)
Fixpoint abrJstar {n m : nat} (d : D n) (p : n >= m) : D m :=
  match le_lt_eq_dec m n p with
  | left l =>
     match n with
     | 0 =>
         λ (d : D 0) l,
         False_rec (D m) (Nat.nlt_0_r m l)
     | S n0 =>
         λ d l,
         abrJstar (abrJ d) (gt_S_le m n0 l)
     end d l
  | right e => eq_rec_r D d e
  end
.

(*
Fixpoint abrIstar {n m : nat} (d : D n) (p : n <= m) : D m.
Proof.
  apply le_lt_eq_dec in p.
  destruct p.
  - destruct m.
    * contradict l.
      auto with arith.
    * apply abrI.
      apply (abrIstar n m d).
      auto with arith.
  - subst.
    assumption.
Defined.
*)
Fixpoint abrIstar {n m : nat} (d : D n) (p : n <= m) : D m :=
  match le_lt_eq_dec n m p with
  | left l =>
     match m with
     | 0 =>
         λ l,
         False_rec (D 0) (Nat.nlt_0_r n l)
     | S m0 =>
         λ l,
         abrI (abrIstar d (gt_S_le n m0 l))
     end l
  | right e =>
     eq_rec_r (λ n, D n → D m) id e d
  end
.

Theorem abrIstarNone : forall {n m : nat} p, abrIstar (@DBottom n) p = (@DBottom m).
Proof.
  unfold DBottom.
  induction n.
  - induction m; intros.
    * compute.
      tauto.
    * simpl.
      rewrite IHm.
      destruct m; simpl; tauto.
  - induction m; intros.
    * contradict p.
      auto with arith.
    * specialize (le_S_n n m).
      intuition.
      simpl.
      specialize (IHn m H0).
      destruct (le_lt_eq_dec (S n) (S m) p).
      + rewrite IHm.
        destruct m; simpl; tauto.
      + inversion e.
        subst.
        destruct e.
        
        unfold eq_rec_r.
        unfold eq_rec.
        unfold eq_rect.
        unfold eq_sym.
        simpl.
        destruct (eq_sym e).
        simpl.
        Check eq_rec_r.


      destruct n, m; apply IHn.
      + rewrite IHn.


Definition Dprod := forall n, D n.
Definition DD := { d : Dprod | forall n, abrJ (d (S n)) = d n }.

Definition DDBottom' : Dprod := fun n =>
match n with
| O => None
| S _ => None
end.

(*
Definition DDBottom : DD.
Proof.
  unfold DD.
  econstructor.
  intros.
  instantiate (d := DDBottom').
  unfold DDBottom'.
  destruct n; simpl; tauto.
Qed.
*)
Definition DDBottom : DD :=
exist 
  (λ d : Dprod, ∀ n, abrJ (d (S n)) = d n)
  DDBottom'
  (λ n,
   match
     n
     return
       (abrJ None =
        match n return (D n) with
        | 0 => None
        | S n => None
        end)
   with
   | 0 => eq_refl
   | S n0 => eq_refl
   end).

Definition DDisBottom (d : DD) : bool :=
match proj1_sig d 1 with
| None => true
| Some _ => false
end.

Theorem sigEq : forall
  {A : Set}
  {p : A -> Prop}
  (x y : sig p),
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros.
  apply Subset.subset_eq.
  assumption.
Qed.

Theorem DDisBottomCorrect : forall d,
  d = DDBottom <-> DDisBottom d = true.
Proof.
  split; intros.
  - subst.
    compute.
    tauto.
  - apply sigEq.
    unfold DDisBottom in H.
    destruct d.
    simpl in *.
    apply functional_extensionality_dep.
    induction x0.
    * simpl.
      destruct (x 0); intuition.
    *specialize (e x0).
     destruct x0.
      + destruct (x 1); intuition.
      + simpl in *.
        rewrite IHx0 in e.
        destruct (x (S (S x0))); try tauto.
        inversion e.
Qed.

(*
Definition abrIinf' {n : nat} (d : D n) : Dprod.
Proof.
  unfold Dprod.
  intros.
  destruct (le_ge_dec n n0).
  - apply (@abrIstar n n0); assumption.
  - apply (@abrJstar n n0); assumption.
Qed.
*)
Definition abrIinf' {n : nat} (d : D n) : Dprod :=
fun m =>
match le_ge_dec n m with
| left l => abrIstar d l
| right g => abrJstar d g
end.

Theorem abrJI : forall {n : nat} (d : D n), abrJ (abrI d) = d.
Proof.
  induction n; intros.
  - unD0.
    simpl.
    tauto.
  - destruct d.
    * simpl.
      apply f_equal.
      apply functional_extensionality.
      intros.
      rewrite IHn.
      rewrite IHn.
      tauto.
    * simpl.
      tauto.
Qed.

Require Import Coq.Logic.ProofIrrelevance.

Definition abrIinf {n : nat} (d : D n) : DD.
Proof.
  unfold DD.
  econstructor.
  intros.
  instantiate (d := abrIinf' d).
  unfold abrIinf'.
  destruct (le_ge_dec n n0);
  destruct (le_ge_dec n (S n0)).
  - simpl.
    destruct (le_lt_eq_dec n (S n0) l0).
    * rewrite abrJI.
      apply f_equal2; try tauto.
      apply proof_irrelevance.
    * subst.
      contradict l.
      auto with arith.
  - contradict l.
    auto with arith.
  - simpl.
    destruct (le_lt_eq_dec n (S n0) l).
    * rewrite abrJI.
      simpl.
      destruct n.
      + unD0.
        simpl.
      .
      apply f_equal2; try tauto.
      apply proof_irrelevance.
    * subst.
      contradict l.
      auto with arith.


      inversion l.
      + .
      Check Streicher_K.
      destruct (gt_S_le n n0 l1).
      Check le_n.
      specialize prop_extensionality.
      eapply prop_extensionality.
      apply proof_irrelevance. le_n.
      auto with arith.
  - Check ?d.
    apply (@abrIstar n n0); assumption.
  - apply (@abrJstar n n0); assumption.
Qed.

(*
Definition abrIinf {n : nat} (d : D n) : DD.
Proof.
  unfold DD.
  intros.
  destruct (le_ge_dec n n0).
  - apply (@abrIstar n n0); assumption.
  - apply (@abrJstar n n0); assumption.
Qed.
*)


Definition abrII (d : DD) : option (DD -> DD).
Proof.
  unfold DD in *.
  intros.
  specialize (d n).
  assumption.
Defined.
(* destruct n.
  - auto.
  - constructor.
    
  apply Just.*)


Definition abrJJ (d : DD) : DD.
Proof.
  unfold DD in *.
  intros.
  
  






