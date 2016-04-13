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
Require Import Coq.Logic.ProofIrrelevance.

(* Figure 1: Syntax of a Java-like language for core language *)
Definition C := string.
Inductive T :=
| TPrimitiveInt : T
| TClass : C -> T.

Definition S := list ()

Inductive program :=
| Program : (list cls) -> (list s).


Definition phi (x : nat) := x.

Notation "'φ'" := phi.