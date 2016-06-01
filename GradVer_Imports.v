Require Import Coq.Unicode.Utf8 Arith Bool Ring Setoid String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Sets.Powerset.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Classical_Prop.
Import ListNotations.

(* nat *)
Fixpoint divmod (x y : nat) q u :=
  match x with
    | 0 => (q,u)
    | S x' => 
              match u with
              | 0 => divmod x' y (S q) y
              | S u' => divmod x' y q u'
              end
  end.
Definition div x y :=
  match y with
    | 0 => y
    | S y' => fst (divmod x y' 0 y')
  end.
Definition modulo x y :=
  match y with
    | 0 => y
    | S y' => y' - snd (divmod x y' 0 y')
  end.

(*list*)
Fixpoint listDistinct {T : Type} (xs : list T) :=
  match xs with
  | [] => True
  | x :: xs => (~ In x xs) /\ listDistinct xs
  end.
Definition except {A : Type} (A_decb : A -> A -> bool) (a b : list A) : list A :=
  filter (fun x => negb (existsb (A_decb x) b)) a.
Definition disjoint {A : Type} (l1 l2 : list A) :=
  forall x, ~ In x l1 \/ ~ In x l2.
Definition appEnd {A : Type} (l : list A) (x : A) := l ++ [x].

(*option*)
Definition option_bind {A B : Type} (f : A -> option B) (x : option A) : option B :=
match x with
| Some x' => f x'
| None => None
end.


(*decidability*)
Definition dec2decb {A : Type} (dec : ∀ a1 a2 : A, {a1 = a2} + {a1 ≠ a2}) : (A -> A -> bool) :=
  fun a b => if dec a b then true else false.

Definition nat_decb := dec2decb eq_nat_dec.
Hint Resolve eq_nat_dec.
Hint Resolve list_eq_dec eq_nat_dec.

Program Instance string_EqDec : EqDec string eq := string_dec.
Definition string_decb := dec2decb string_dec.
Hint Resolve string_dec.
Hint Resolve list_eq_dec string_dec.
