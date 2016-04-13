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

Definition string_decb (a b : string) := if string_dec a b then true else false.

(* Figure 1: Syntax of a Java-like language for core language *)
Definition C := string. Definition C_decb (a b : C) : bool := string_decb a b.
Definition x := string. Definition x_decb (a b : x) : bool := string_decb a b.
Definition f := string. Definition f_decb (a b : f) : bool := string_decb a b.
Definition m := string. Definition m_decb (a b : m) : bool := string_decb a b.
Definition o := nat.    Definition o_decb (a b : o) : bool := a ==b b.
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

Definition H := o -> option (C * (f -> option v)).
Definition rho := x -> option v. (* list (x * v). *)
Inductive name :=
| namex : x -> name
| nameo : o -> name.
Definition A := list (name * f).
Definition S := list (rho * A * list s).

Notation "'φ'" := phi.
Notation "'ρ'" := rho.

(* accessors *)
Definition class (p : program) (C' : C) : option cls :=
match p with
| Program clss _ =>
  find (fun class => match class with Cls C'' _ _ => C_decb C'' C' end) clss
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
    match find (fun me => match me with Method _ m'' _ _ _ => m_decb m'' m' end) ms with
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
| ex x'' => if x_decb x'' x' then e' else ee
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

Fixpoint HSubst (o' : o) (f' : f) (v' : v) (h : H) : H :=
  fun o'' =>
    if o_decb o'' o'
      then 
      (
        match h o'' with
        | Some (C', ff') => Some (C', fun f'' => if f_decb f'' f' then Some v' else ff' f'')
        | None => None
        end
      )
      else h o''
.

Fixpoint rhoSubst (x' : x) (v' : v) (r : rho) : rho :=
  fun x'' => if x_decb x'' x' then Some v' else r x''.

(* Figure 2: Static typing rules for expressions of the core language *)
Inductive sfrme : A -> e -> Prop :=
| WFVar : forall a (x' : x),
    sfrme a (ex x')
| WFValue : forall a (v' : v),
    sfrme a (ev v')
| WFField : forall a (x' : x) (f' : f),
    In (namex x', f') a ->
    sfrme a (edot (ex x') f')
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

(* Figure 6: Evaluation of expressions for core language *)
Fixpoint evale (h : H) (r : rho) (e' : e) : option v :=
  match e' with
  | ex x' => r x'
  | edot e'' f' =>
    match evale h r e'' with
    | Some (vo o') =>
      match h o' with
      | Some (_, ho') => ho' f'
      | _ => None
      end
    | _ => None
    end
  | ev (vnull) => Some vnull
  | ev (vn n') => Some (vn n')
  | ev (vo o') => option_map (fun _ => vo o') (h o')
  | ethis => None
  | eresult => None
  end.
(*Inductive evale : H -> rho -> e -> v -> Prop :=
| EEVar : forall h r rx x',
    r x' = Some rx ->
    evale h r (ex x') rx
| EEAcc : forall h ho lookupResult r x' (o' : o) (f' : f),
    evale h r (ex x') (vo o') ->
    h o' = Some ho ->
    snd ho f' = Some lookupResult ->
    evale h r (edot (ex x') f') lookupResult
| EENull : forall h r,
    evale h r (ev vnull) vnull
| EENum : forall h r n',
    evale h r (ev (vn n')) (vn n')
| EEObj : forall h r o' o'',
    h o' = Some o'' ->
    evale h r (ev (vo o')) (vo o')
.*)

(* Figure 7: Evaluation of formulas for core language *)
Inductive evalphi : H -> rho -> A -> phi -> Prop :=
| EATrue : forall h r a,
    evalphi h r a phiTrue
| EAEqual : forall h r a e1 e2 v1 v2,
    evale h r e1 = Some v1 ->
    evale h r e2 = Some v2 ->
    v1 = v2 ->
    evalphi h r a (phiEq e1 e2)
| EANEqual : forall h r a e1 e2 v1 v2,
    evale h r e1 = Some v1 ->
    evale h r e2 = Some v2 ->
    v1 <> v2 ->
    evalphi h r a (phiNeq e1 e2)
| EAAcc : forall h r a x' o' f',
    evale h r (ex x') = Some (vo o') ->
    In (nameo o', f') a ->
    evalphi h r a (phiAcc x' f')
| EAType : forall h r a x' t,
    evalphi h r a (phiAssert x' t)
| EASepOp : forall h r a a1 a2 p1 p2,
    a = a1 ++ a2 /\ NoDup a ->
    evalphi h r a1 p1 ->
    evalphi h r a2 p2 ->
    evalphi h r a (phiConj p1 p2)
.

(* Figure 8: Definition of footprint meta-function *)
Fixpoint footprint (h : H) (r : rho) (p : phi) : A :=
  match p with
  | phiAcc x' f' => 
      match evale h r (ex x') (* == r x' *) with
      | Some (vo o') => [(nameo o', f')]
      | _ => [] (*???*)
      end
  | phiConj p1 p2 => footprint h r p1 ++ footprint h r p2
  | _ => []
  end.

Check fields.

(* Figure 9: Dynamic semantics for core language *)
Inductive dynSem {prog : program} : (H * S) -> (H * S) -> Prop :=
| ESFieldAssign : forall h (S' : S) (s' : list s) (a : A) r h' (x' y' : x) (yv' : v) (o' : o) (f' : f),
    evale h r (ex x') = Some (vo o') ->
    evale h r (ex y') = Some yv' ->
    In (nameo o', f') a ->
    h' = HSubst o' f' yv' h ->
    dynSem (h, (r, a, sMemberSet x' f' y' :: s') :: S') (h', (r, a, s') :: S')
| ESDefVar : forall h (S' : S) (s' : list s) (a : A) r r' (x' : x) (C' : C),
    r' = rhoSubst x' vnull ->
    dynSem (h, (r, a, sDeclare (TClass C') x' :: s') :: S') (h, (r, a, s') :: S')
| ESVarAssign : forall h (S' : S) (s' : list s) (a : A) r r' (x' : x) (e' : e) (v' : v),
    evale h r e' = Some v' ->
    r' = rhoSubst x' v' ->
    dynSem (h, (r, a, sAssign x' e' :: s') :: S') (h, (r, a, s') :: S')
| ESNewObj : forall h (S' : S) (s' : list s) (a : A) r r' (x' : x) (e' : e) (v' : v),
    h o' = None ->
    fiel
    r' = rhoSubst x' v' ->
    dynSem (h, (r, a, sAssign x' e' :: s') :: S') (h, (r, a, s') :: S')


.











