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
Definition DD := forall n, D n.

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

SearchAbout le.

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

Definition abrIinf {n : nat} (d : D n) : DD.
Proof.
  unfold DD.
  intros.
  destruct (le_ge_dec n n0).
  - apply (@abrIstar n n0); assumption.
  - apply (@abrJstar n n0); assumption.
Qed.

Print abrIinf.

Definition DBottom : DD := fun n =>
match n with
| O => None
| S _ => None
end.




Check D.
Check DD.











