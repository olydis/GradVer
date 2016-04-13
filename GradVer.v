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
| sAssign : x -> e -> s
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
| Cls : C -> list field -> list method -> cls.
Inductive program :=
| Program : (list cls) -> (list s) -> program.

Definition H := o -> C * (list (f * v)).
Definition rho := list (x * v).
Inductive name :=
| namex : x -> name
| nameo : o -> name.
Definition A := list (name * f).
Definition S := list (rho * A * list s).

Notation "'φ'" := phi.
Notation "'ρ'" := rho.

(** helper methods **)
Definition string_decb (a b : string) := if string_dec a b then true else false.

(* accessors *)
Definition class (p : program) (C' : C) : option cls :=
match p with
| Program clss _ =>
  find (fun class => match class with Cls C'' _ _ => string_decb C'' C' end) clss
end.
Definition fields (p : program) (C' : C) : option (list (C * f)) :=
match class p C' with
| None => None
| Some class => 
  match class with
  | Cls C'' fs _ => Some (map (fun f => (C'', match f with Field _ f' => f' end)) fs)
  end
end.
Definition mcontract (p : program) (C' : C) (m' : m) : option contract :=
match class p C' with
| None => None
| Some class => 
  match class with
  | Cls C'' _ ms =>
    match find (fun me => match me with Method _ m'' _ _ _ => string_decb m'' m' end) ms with
    | None => None
    | Some me =>
      match me with
      | Method _ _ _ contr _ => Some contr
      end
    end
  end
end.
Definition mpre (p : program) (C' : C) (m' : m) : option phi :=
option_map 
  (fun contr => match contr with Contract res _ => res end)
  (mcontract p C' m').
Definition mpost (p : program) (C' : C) (m' : m) : option phi :=
option_map 
  (fun contr => match contr with Contract _ res => res end)
  (mcontract p C' m').

(* substitution *)
Fixpoint eSubst (x' : x) (e' : e) (ee : e) : e :=
match ee with
| ex x'' => if string_decb x'' x' then e' else ee
| edot e'' f' => edot (eSubst x' e' e'') f'
| _ => ee
end.

Fixpoint phiSubst (x' : x) (e' : e) (p : phi) : phi :=
match p with
| phiEq  e1 e2 => phiEq  (eSubst x' e' e1) (eSubst x' e' e2)
| phiNeq e1 e2 => phiNeq (eSubst x' e' e1) (eSubst x' e' e2)
(* | phiAcc : x -> f -> phi ??? *)
| phiConj p1 p2 => phiConj (phiSubst x' e' p1) (phiSubst x' e' p2)
(* | phiAssert : x -> T -> phi ??? *)
| _ => p
end.

Definition phiSubsts (r : list (x * e)) (p : phi) : phi :=
  fold_left (fun a b => phiSubst (fst b) (snd b) a) r p.

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

(* implication on phi *)
Inductive phiImplies : phi -> phi -> Prop := (* TODO *).

(* Figure 5: Hoare-based proof rules for core language *)
Inductive hoare {prog : program} : phi -> list s -> phi -> Prop :=
| HSec : forall (p q1 q2 r : phi) (s1 s2 : list s),
    hoare p s1 q1 ->
    phiImplies q1 q2 ->
    hoare q2 s2 r ->
    hoare p (s1 ++ s2) r
| HInsVar : forall p (T' : T) (x' : x),
    hoare p [sDeclare T' x'] (phiConj p (phiAssert x' T'))
| HNewObj : forall p x' (C' : C) fs,
    phiImplies p (phiAssert x' (TClass C')) ->
    fields prog C' = Some fs ->
    hoare
      p
      [sAlloc x' C']
      (fold_left 
        (fun a b => phiConj (phiAcc x' (snd b)) a) 
        fs 
        (phiConj (phiNeq (ex x') (ev vnull)) p))
| HFieldAssign : forall p (x' y' : x) (f' : f),
    phiImplies p (phiConj (phiAcc x' f') (phiNeq (ex x') (ev vnull))) ->
    hoare p [sMemberSet x' f' y'] (phiConj p (phiEq (edot (ex x') f') (ex y')))
| HVarAssign : forall p' p (x' : x) (e' : e),
    p' = phiSubst x' e' p ->
    sfrmphi [] p' ->
    sfrme (staticFootprint p') e' ->
    hoare p [sAssign x' e'] p
| HReturn : forall p (x' : x),
    hoare p [sReturn x'] (phiConj p (phiEq eresult (ex x')))
| HApp : forall p pp pr pq (x' y' : x) (C' : C) (m' : m) (zX' : list (x * e)),
    phiImplies p (phiConj (phiConj (phiAssert y' (TClass C')) pp) pr) ->
    Some pp = option_map (phiSubsts ((y', ethis) :: zX')) (mpre prog C' m') ->
    Some pq = option_map (phiSubsts (((y', ethis) :: zX') ++ [(x', eresult)])) (mpost prog C' m') ->
    hoare p [sCall x' y' m' (map fst zX')] (phiConj (phiConj pq (phiAssert y' (TClass C'))) pr)
| HAssert : forall p1 p2,
    phiImplies p1 p2 ->
    hoare p1 [sAssert p2] p1
| HRelease : forall p1 p2 pr,
    phiImplies p1 (phiConj p2 pr) ->
    sfrmphi [] pr ->
    hoare p1 [sRelease p2] pr
.



