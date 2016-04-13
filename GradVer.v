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
Require Import Coq.Lists.List.
Import ListNotations.

(* Figure 1: Syntax of a Java-like language for core language *)
Definition C := string.
Definition x := string.
Definition f := string.
Definition m := string.
Definition o := nat.
Inductive T :=
| TPrimitiveInt : T
| TClass : C -> T.
Inductive v :=
| vn : nat -> v
| vnull : v
| vo : o -> v.
Inductive e :=
| ev : v -> e
| ex : x -> e
| ethis : e
| eresult : e
| edot : e -> f -> e.
Inductive phi :=
| phiTrue : phi
| phiEq : e -> e -> phi
| phiNeq : e -> e -> phi
| phiAcc : x -> f -> phi
| phiConj : phi -> phi -> phi
| phiAssert : x -> T -> phi.
Inductive s :=
| sMemberSet : x -> f -> x -> s
| sDeclare : T -> x -> s
| sSet : x -> e -> s
| sAlloc : x -> C -> s
| sCall : x -> x -> m -> list x -> s
| sReturn : x -> s
| sAssert : phi -> s
| sRelease : phi -> s.
Inductive contract :=
| Contract : phi -> phi -> contract.
Inductive method :=
| Method : T -> m -> list (T * x) -> contract -> list s -> method.
Inductive field :=
| Field : T -> f -> field.
Inductive cls :=
Cls : C -> list field -> list method -> cls.
Inductive program :=
| Program : (list cls) -> (list s) -> program.

Definition H := o -> C * (list (f * v)).
Definition rho := list (x * v).
Inductive name :=
| namex : x -> name
| nameo : o -> name.
Definition A := list (name * f).
Definition S := list (rho * A * list s).

(* notation *)
Notation "'φ'" := phi.
Notation "'ρ'" := rho.

(* Figure 2: Static typing rules for expressions of the core language *)
Inductive sfrme : A -> e -> Prop :=
| WFVar : forall a (x' : x), sfrme a (ex x')
| WFValue : forall a (v' : v), sfrme a (ev v')
| WFField : forall a (x' : x) (f' : f), sfrme a (edot (ex x') f')
.


(* Figure 4: Deﬁnition of a static version of footprint *)
Fixpoint staticFootprint (p : phi) : A :=
  match p with
  | phiAcc x' f' => [(namex x', f')]
  | phiConj p1 p2 => staticFootprint p1 ++ staticFootprint p2
  | _ => []
  end.

(* Figure 3: Static rules for syntactically self-framed formulas *)
Inductive sfrmphi : A -> phi -> Prop :=
| WFTrue : forall a, sfrmphi a phiTrue
| WFEqual : forall a (e1 e2 : e), sfrme a e1 -> sfrme a e2 -> sfrmphi a (phiEq e1 e2)
| WFNEqual : forall a (e1 e2 : e), sfrme a e1 -> sfrme a e2 -> sfrmphi a (phiNeq e1 e2)
| WFAcc : forall a x f, sfrmphi a (phiAcc x f)
| WFSepOp : forall a phi1 phi2, sfrmphi a phi1 -> sfrmphi (a ++ staticFootprint phi1) phi2 -> sfrmphi a (phiConj phi1 phi2)
| WFType : forall a x T, sfrmphi a (phiAssert x T)
.