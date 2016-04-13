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

Definition Dprod := forall n, D n.
Definition DD := { d : Dprod | forall n, abrJ (d (S n)) = d n }.

Definition DDBottom' : Dprod := fun n =>
match n with
| O => None
| S _ => None
end.

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

Print DDBottom.

Definition DDisBottom (d : DD) : bool :=
match proj1_sig d 1 with
| None => true
| Some _ => false
end.

Theorem DDisBottomCorrect : forall d,
  d = DDBottom <-> DDisBottom d = true.
Proof.
  split; intros.
  - subst.
    compute.
    tauto.
  - unfold DDisBottom in H.
    destruct d.
    unfold DDBottom.
    unfold DDBottom'.
    apply f_equal3.
    apply functional_extensionality_dep.
    unfold DDBottom.
    
    destruct (d 1).
    * inversion H.
    * 

Definition DDBottom : DD.
Proof.
  unfold DD.
  econstructor.
  intros.
  instantiate (d := DDBottom').
  unfold DDBottom'.
  destruct n; simpl; tauto.
Qed.

Print DDBottom.

Definition abrIinf {n : nat} (d : D n) : DD.
Proof.
  unfold DD.
  Check sig.
  intros.
  destruct (le_ge_dec n n0).
  - apply (@abrIstar n n0); assumption.
  - apply (@abrJstar n n0); assumption.
Qed.

Definition abrIinf {n : nat} (d : D n) : DD :=
fun m =>
match le_ge_dec n m with
| left l => abrIstar d l
| right g => abrJstar d g
end.

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
  
  






