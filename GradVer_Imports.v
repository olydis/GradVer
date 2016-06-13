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

Lemma NoDupApp : forall {T : Type} (a b : list T),
  NoDup (a ++ b) ->
  NoDup a /\
  NoDup b.
Proof.
  induction a; intros; simpl in *.
  - split.
    * constructor.
    * assumption.
  - inversion H. subst.
    apply IHa in H3.
    intuition.
    constructor; intuition.
Qed.

(*option*)
Definition option_bind {A B : Type} (f : A -> option B) (x : option A) : option B :=
match x with
| Some x' => f x'
| None => None
end.

Definition olist {T : Type} (x : option T) : list T :=
  match x with
  | Some x => [x]
  | None => []
  end.
Definition oflatten {T : Type} (xs : list (option T)) : list T :=
  flat_map olist xs.
  
Lemma oflattenMapSome : forall {T : Type} (x : list T),
  oflatten (map Some x) = x.
Proof.
  induction x; simpl in *; try tauto.
  rewrite IHx.
  tauto.
Qed.

Lemma oflattenApp : forall {T : Type} (A1 A2 : list (option T)),
  oflatten (A1 ++ A2) = oflatten A1 ++ oflatten A2.
Proof.
  intros.
  unfold oflatten.
  repeat rewrite flat_map_concat_map.
  rewrite map_app.
  rewrite concat_app.
  tauto.
Qed.

Lemma InOflatten : forall {T : Type} (x : T) xs,
  In x (oflatten xs) <->
  In (Some x) xs.
Proof.
  unfold oflatten, olist.
  split; intros.
  - apply in_flat_map in H.
    inversion H; clear H.
    inversion H0; clear H0.
    destruct (x0); try tauto.
    inversion H1; try tauto.
    subst. tauto.
  - apply in_flat_map.
    eexists; split; eauto.
    constructor.
    tauto.
Qed.


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
