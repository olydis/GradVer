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

(* helpers *)
Definition dec2decb {A : Type} (dec : ∀ a1 a2 : A, {a1 = a2} + {a1 ≠ a2}) : (A -> A -> bool) :=
  fun a b => if dec a b then true else false.
Definition except {A : Type} (A_decb : A -> A -> bool) (a b : list A) : list A :=
  filter (fun x => negb (existsb (A_decb x) b)) a.

Definition nat_decb := dec2decb eq_nat_dec.
Hint Resolve eq_nat_dec.
Hint Resolve list_eq_dec eq_nat_dec.

Program Instance string_EqDec : EqDec string eq := string_dec.
Definition string_decb := dec2decb string_dec.
Hint Resolve string_dec.
Hint Resolve list_eq_dec string_dec.

(* Figure 1: Syntax of a Java-like language for core language *)
Definition C := string.
Definition f := string.
Definition m := string.
Definition o := nat.
Inductive x :=
| xUserDef : string -> x
| xthis : x
| xresult : x.
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
Definition rho := x -> v.
Inductive name :=
| namex : x -> name
| nameo : o -> name.
Definition A := list (name * f).
Definition S := list (rho * A * list s).

(* equality *)

Definition C_decb := string_decb.
Definition f_decb := string_decb.
Definition m_decb := string_decb.
Definition o_decb := nat_decb.

Definition x_dec : ∀ n m : x, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance x_EqDec : EqDec x eq := x_dec.
Definition x_decb := dec2decb x_dec.
Hint Resolve x_dec.
Hint Resolve list_eq_dec x_dec.

Definition T_dec : ∀ n m : T, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance T_EqDec : EqDec T eq := T_dec.
Definition T_decb := dec2decb T_dec.
Hint Resolve T_dec.
Hint Resolve list_eq_dec T_dec.

Definition v_dec : ∀ n m : v, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance v_EqDec : EqDec v eq := v_dec.
Definition v_decb := dec2decb v_dec.
Hint Resolve v_dec.
Hint Resolve list_eq_dec v_dec.

Definition e_dec : ∀ n m : e, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance e_EqDec : EqDec e eq := e_dec.
Definition e_decb := dec2decb e_dec.
Hint Resolve e_dec.
Hint Resolve list_eq_dec e_dec.

Definition phi_dec : ∀ n m : phi, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance phi_EqDec : EqDec phi eq := phi_dec.
Definition phi_decb := dec2decb phi_dec.
Hint Resolve phi_dec.
Hint Resolve list_eq_dec phi_dec.

Definition s_dec : ∀ n m : s, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance s_EqDec : EqDec s eq := s_dec.
Definition s_decb := dec2decb s_dec.
Hint Resolve s_dec.
Hint Resolve list_eq_dec s_dec.

Definition contract_dec : ∀ n m : contract, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance contract_EqDec : EqDec contract eq := contract_dec.
Definition contract_decb := dec2decb contract_dec.
Hint Resolve contract_dec.
Hint Resolve list_eq_dec contract_dec.

Definition method_dec : ∀ n m : method, {n = m} + {n ≠ m}. decide equality. apply (list_eq_dec (prod_eqdec T_dec x_dec)). Defined.
Program Instance method_EqDec : EqDec method eq := method_dec.
Definition method_decb := dec2decb method_dec.
Hint Resolve method_dec.
Hint Resolve list_eq_dec method_dec.

Definition field_dec : ∀ n m : field, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance field_EqDec : EqDec field eq := field_dec.
Definition field_decb := dec2decb field_dec.
Hint Resolve field_dec.
Hint Resolve list_eq_dec field_dec.

Definition cls_dec : ∀ n m : cls, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance cls_EqDec : EqDec cls eq := cls_dec.
Definition cls_decb := dec2decb cls_dec.
Hint Resolve cls_dec.
Hint Resolve list_eq_dec cls_dec.

Definition program_dec : ∀ n m : program, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance program_EqDec : EqDec program eq := program_dec.
Definition program_decb := dec2decb program_dec.
Hint Resolve program_dec.
Hint Resolve list_eq_dec program_dec.

Definition name_dec : ∀ n m : name, {n = m} + {n ≠ m}. decide equality. Defined.
Program Instance name_EqDec : EqDec name eq := name_dec.
Definition name_decb := dec2decb name_dec.
Hint Resolve name_dec.
Hint Resolve list_eq_dec name_dec.

Definition A_dec : ∀ n m : A, {n = m} + {n ≠ m}. decide equality. apply (prod_eqdec name_dec string_dec). Defined.
Program Instance A_EqDec : EqDec A eq := A_dec.
Definition A_decb := dec2decb A_dec.
Hint Resolve A_dec.
Hint Resolve list_eq_dec A_dec.

Definition A'_decb (a b : name * f) : bool := name_decb (fst a) (fst b) && string_decb (snd a) (snd b).
Definition Aexcept := except A'_decb.

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
Definition mmethod (p : program) (C' : C) (m' : m) : option method :=
  match class p C' with
  | None => None
  | Some class => 
    match class with
    | Cls C'' _ ms =>
      find (fun me => match me with Method _ m'' _ _ _ => m_decb m'' m' end) ms
    end
  end.
Definition mcontract (p : program) (C' : C) (m' : m) : option contract :=
  option_map
    (fun me => match me with Method _ _ _ contr _ => contr end)
    (mmethod p C' m').
Definition mpre (p : program) (C' : C) (m' : m) : option phi :=
  option_map
    (fun contr => match contr with Contract res _ => res end)
    (mcontract p C' m').
Definition mpost (p : program) (C' : C) (m' : m) : option phi :=
  option_map
    (fun contr => match contr with Contract _ res => res end)
    (mcontract p C' m').
Definition mbody (p : program) (C' : C) (m' : m) : option (list s) :=
  option_map
    (fun me => match me with Method _ _ _ _ instrs => instrs end)
    (mmethod p C' m').
Definition mparams (p : program) (C' : C) (m' : m) : option (list x) :=
  option_map
    (fun me => match me with Method _ _ params _ _ => map snd params end)
    (mmethod p C' m').

Definition getMain (p : program) : list s := match p with Program _ main => main end.

(* substitution *)
Fixpoint eSubst (x' : x) (e' : e) (ee : e) : e :=
match ee with
| ex x'' => if x_decb x'' x' then e' else ee
| edot e'' f' => edot (eSubst x' e' e'') f'
| _ => ee
end.

Fixpoint eSubsts (r : list (x * e)) (ee : e) : e :=
  fold_left (fun a b => eSubst (fst b) (snd b) a) r ee.

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

Fixpoint HSubsts (o' : o) (r : list (f * v)) (h : H) : H :=
  fold_left (fun a b => HSubst o' (fst b) (snd b) a) r h.

Fixpoint rhoSubst (x' : x) (v' : v) (r : rho) : rho :=
  fun x'' => if x_decb x'' x' then v' else r x''.

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
Fixpoint phi2list (p : phi) : list phi :=
match p with
| phiTrue => []
| phiConj p1 p2 => phi2list p1 ++ phi2list p2
| _ => [p]
end.
Fixpoint list2phi (ps : list phi) : phi := fold_left phiConj ps phiTrue.
Inductive phiImplies' : list phi -> list phi -> Prop :=
| PIempty : phiImplies' [] []
| PIskip : forall h l1 l2, phiImplies' l1 l2 -> phiImplies' (h :: l1) l2
| PItake : forall h l1 l2, phiImplies' l1 l2 -> phiImplies' (h :: l1) (h :: l2)
.
Definition phiImplies (p1 p2 : phi) : Prop := phiImplies' (phi2list p1) (phi2list p2).

(* Figure 5: Hoare-based proof rules for core language *)
Inductive hoareSingle {prog : program} : phi -> s -> phi -> Prop :=
| HInsVar : forall p (T' : T) (x' : x),
    hoareSingle p (sDeclare T' x') (phiConj p (phiAssert x' T'))
| HNewObj : forall p x' (C' : C) fs,
    phiImplies p (phiAssert x' (TClass C')) ->
    fields prog C' = Some fs ->
    hoareSingle
      p
      (sAlloc x' C')
      (fold_left 
        (fun a b => phiConj (phiAcc x' (snd b)) a) 
        fs 
        (phiConj (phiNeq (ex x') (ev vnull)) p))
| HFieldAssign : forall p (x' y' : x) (f' : f),
    phiImplies p (phiConj (phiAcc x' f') (phiNeq (ex x') (ev vnull))) ->
    hoareSingle p (sMemberSet x' f' y') (phiConj p (phiEq (edot (ex x') f') (ex y')))
| HVarAssign : forall p' p (x' : x) (e' : e),
    p' = phiSubst x' e' p ->
    sfrmphi [] p' ->
    sfrme (staticFootprint p') e' ->
    hoareSingle p (sAssign x' e') p'
| HReturn : forall p (x' : x),
    hoareSingle p (sReturn x') (phiConj p (phiEq (ex xresult) (ex x')))
| HApp : forall p pp pr pq (x' y' : x) (C' : C) (m' : m) (Xz' : list (x * x)) (zs' := map snd Xz') (Xze' := map (fun pr => (fst pr, ex (snd pr))) Xz'),
    phiImplies p (phiConj (phiConj ((phiConj (phiAssert y' (TClass C')) (phiNeq (ex y') (ev vnull)))) pp) pr) ->
    Some pp = option_map (phiSubsts ((xthis, ex y') :: Xze')) (mpre prog C' m') ->
    Some pq = option_map (phiSubsts (((xthis, ex y') :: Xze') ++ [(xresult, ex x')])) (mpost prog C' m') ->
    hoareSingle p (sCall x' y' m' zs') (phiConj (phiConj pq (phiAssert y' (TClass C'))) pr)
| HAssert : forall p1 p2,
    phiImplies p1 p2 ->
    hoareSingle p1 (sAssert p2) p1
| HRelease : forall p1 p2 pr,
    phiImplies p1 (phiConj p2 pr) ->
    sfrmphi [] pr ->
    hoareSingle p1 (sRelease p2) pr
.

Inductive hoare {prog : program} : phi -> list s -> phi -> Prop :=
| HSec : forall (p q1 q2 r : phi) (s1 : s) (s2 : list s), (* w.l.o.g.??? *)
    @hoareSingle prog p s1 q1 ->
    phiImplies q1 q2 ->
    hoare q2 s2 r ->
    hoare p (s1 :: s2) r
| HEMPTY : forall p, hoare p [] p
.

(* Figure 6: Evaluation of expressions for core language *)
Fixpoint evale (h : H) (r : rho) (e' : e) : v :=
  match e' with
  | ex x' => r x'
  | edot e'' f' =>
    match evale h r e'' with
    | vo o' =>
      match h o' with
      | Some (_, ho') =>
                  match ho' f' with
                  | Some x => x
                  | _ => vnull
                  end
      | _ => vnull
      end
    | _ => vnull
    end
  | ev (vnull) => vnull
  | ev (vn n') => vn n'
  | ev (vo o') => match h o' with
                  | Some _ => vo o'
                  | _ => vnull
                  end
  end.
(* NOTE: there are tons of calls like "evale h r (ex x)", wouldn't it be clearer to just say "r x"? or is that less consistent? *)

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
    evale h r e1 = v1 ->
    evale h r e2 = v2 ->
    v1 = v2 ->
    evalphi h r a (phiEq e1 e2)
| EANEqual : forall h r a e1 e2 v1 v2,
    evale h r e1 = v1 ->
    evale h r e2 = v2 ->
    v1 <> v2 ->
    evalphi h r a (phiNeq e1 e2)
| EAAcc : forall h r a x' o' f',
    evale h r (ex x') = vo o' ->
    In (nameo o', f') a ->
    evalphi h r a (phiAcc x' f')
| EATypeP : forall h r a x' n',
    evale h r (ex x') = vn n' \/ evale h r (ex x') = vnull ->
    evalphi h r a (phiAssert x' TPrimitiveInt)
| EATypeC : forall h r a x' c' o' f,
    (evale h r (ex x') = vo o' /\ h o' = Some (c', f))
    \/ evale h r (ex x') = vnull ->
    evalphi h r a (phiAssert x' (TClass c'))
| EASepOp : forall h r a a1 a2 p1 p2,
    a1 = Aexcept a a2 ->
    evalphi h r a1 p1 ->
    evalphi h r a2 p2 ->
    evalphi h r a (phiConj p1 p2)
.

(* Figure 8: Definition of footprint meta-function *)
Fixpoint footprint (h : H) (r : rho) (p : phi) : A :=
  match p with
  | phiAcc x' f' => 
      match evale h r (ex x') with
      | vo o' => [(nameo o', f')]
      | _ => [] (*???*)
      end
  | phiConj p1 p2 => footprint h r p1 ++ footprint h r p2
  | _ => []
  end.

(* Figure 9: Dynamic semantics for core language *)
Definition execState : Set := H * S.
Inductive dynSem {prog : program} : execState -> execState -> Prop :=
| ESFieldAssign : forall h h' (S' : S) (s' : list s) (a : A) r (x' y' : x) (yv' : v) (o' : o) (f' : f),
    evale h r (ex x') = vo o' ->
    evale h r (ex y') = yv' ->
    In (nameo o', f') a ->
    h' = HSubst o' f' yv' h ->
    dynSem (h, (r, a, sMemberSet x' f' y' :: s') :: S') (h', (r, a, s') :: S')
| ESDefVar : forall h (S' : S) (s' : list s) (a : A) r r' (x' : x) (T' : T),
    r' = rhoSubst x' vnull r ->
    dynSem (h, (r, a, sDeclare T' x' :: s') :: S') (h, (r', a, s') :: S')
| ESVarAssign : forall h (S' : S) (s' : list s) (a : A) r r' (x' : x) (e' : e) (v' : v),
    evale h r e' = v' ->
    r' = rhoSubst x' v' r ->
    dynSem (h, (r, a, sAssign x' e' :: s') :: S') (h, (r', a, s') :: S')
| ESNewObj : forall h h' (S' : S) (s' : list s) (a a' : A) r r' (x' : x) (o' : o) (C' : C) Cf',
    h o' = None ->
    fields prog C' = Some Cf' ->
    r' = rhoSubst x' (vo o') r ->
    a' = a ++ map (fun cf' => (nameo o', snd cf')) Cf' ->
    h' = HSubsts o' (map (fun cf' => (snd cf', vnull)) Cf') h ->
    dynSem (h, (r, a, sAlloc x' C' :: s') :: S') (h', (r', a', s') :: S')
| ESReturn : forall h (S' : S) (s' : list s) (a : A) r r' (x' : x) (vx : v),
    evale h r (ex x') = vx ->
    r' = rhoSubst xresult vx r ->
    dynSem (h, (r, a, sReturn x' :: s') :: S') (h, (r', a, s') :: S')
| ESApp : forall pre h (S' : S) (s' rs : list s) (a a' : A) r r' (x' y' : x) (zs' : list x) (wvs' : list (x * v)) (ws' := map fst wvs') (vs' := map snd wvs') (m' : m) (o' : o) (C' : C) fvf,
    evale h r (ex y') = vo o' ->
    map (fun z' => evale h r (ex z')) zs' = vs' ->
    h o' = Some (C', fvf) ->
    mbody prog C' m' = Some rs ->
    mparams prog C' m' = Some ws' ->
    mpre prog C' m' = Some pre ->
    r' = (fun rx => if x_decb rx xthis then vo o' else
          (match find (fun wv => x_decb rx (fst wv)) wvs' with
            | Some wv => snd wv
            | None => vnull
          end)) ->
    evalphi h r' a pre ->
    a' = footprint h r' pre ->
    dynSem (h, (r, a, sCall x' y' m' zs' :: s') :: S') (h, (r', a', rs) :: (r, Aexcept a a', sCall x' y' m' zs' :: s') :: S')
| ESAppFinish : forall post h (S' : S) (s' : list s) (a a' a'' : A) r r' (x' : x) zs' (m' : m) y' (C' : C) vresult,
    mpost prog C' m' = Some post ->
    evalphi h r' a' post ->
    a'' = footprint h r' post ->
    evale h r' (ex xresult) = vresult ->
    dynSem (h, (r', a', []) :: (r, a, sCall x' y' m' zs' :: s') :: S') (h, (rhoSubst x' vresult r, a ++ a'', s') :: S')
| ESAssert : forall h r a p s' S',
    evalphi h r a p ->
    dynSem (h, (r, a, sAssert p :: s') :: S') (h, (r, a, s') :: S')
| ESRelease : forall h r a a' p s' S',
    evalphi h r a p ->
    a' = Aexcept a (footprint h r p) ->
    dynSem (h, (r, a, sRelease p :: s') :: S') (h, (r, a', s') :: S')
.

(* helper definitions *)
Definition isStuck (prog : program) (s : execState) : Prop :=
  ~ exists s', @dynSem prog s s'.
Definition isFinished (s : execState) : Prop :=
  exists r a, snd s = [(r,a,[])].
Definition isFail (prog : program) (s : execState) : Prop :=
  isStuck prog s /\ ~ isFinished s.

Inductive dynSemStar {prog : program} : execState -> execState -> Prop :=
| ESSNone : forall a, dynSemStar a a
| ESSStep : forall a b c, @dynSem prog a b -> dynSemStar b c -> dynSemStar a c
.
Definition dynSemFull {prog : program} (initial final : execState) : Prop := @dynSemStar prog initial final /\ isFinished final.

Definition newHeap : H := fun _ => None.
Definition newRho : rho := fun _ => vnull.
Definition newAccess : A := [].

(* PROOF SECTION *)
Notation "'φ'" := phi.
Notation "'ρ'" := rho.

(* determinism? *)

Lemma hoareImplies : forall prog q1 q2 q3 q4 s', phiImplies q1 q2 -> @hoare prog q2 s' q3 -> phiImplies q3 q4 -> @hoare prog q1 s' q4.
Admitted.

Lemma phiImplies'Refl : forall x, phiImplies' x x.
Proof.
  induction x0.
  * constructor.
  * apply PItake.
    assumption.
Qed.
Hint Resolve phiImplies'Refl.

Lemma phiImpliesRefl : forall x, phiImplies x x.
Proof.
  unfold phiImplies.
  auto.
Qed.
Hint Resolve phiImpliesRefl.

Lemma hoareSingleEvalPhi : forall prog s' H' r A' q1 q2,
  evalphi H' r A' q1 -> @hoareSingle prog q1 s' q2 -> evalphi H' r A' q2.
Admitted.

Lemma AexceptReverse : forall a1 a2, Aexcept (a1 ++ a2) a2 = a1.
Admitted.

Lemma evalPhiImplies : forall H' r A' q1 q2,
  phiImplies q1 q2 -> evalphi H' r A' q1 -> evalphi H' r A' q2.
Admitted.

Lemma InAexcept : forall x a a', In x (Aexcept a a') -> In x a.
Proof.
  unfold Aexcept.
  unfold except.
  induction a; intros.
  - compute in H0.
    inversion H0.
  - simpl.
    simpl filter in H0.
    destruct (existsb (A'_decb a) a'); simpl in H0.
    * apply IHa in H0.
      auto.
    * inversion H0; auto.
      apply IHa in H1.
      auto.
Qed.

Lemma HnotTotal : forall (H' : H), exists x, H' x = None.
Admitted.

Lemma mapSplitFst : forall {A B : Type} (x : list (A * B)), map fst x = fst (split x).
Admitted.
Lemma mapSplitSnd : forall {A B : Type} (x : list (A * B)), map snd x = snd (split x).
Admitted.

Lemma phiTrueSubst : forall a b p, phiTrue = phiSubst a b p -> p = phiTrue.
Proof.
  intros.
  destruct p; auto;
  unfold phiSubst in H0; inversion H0.
Qed.
Lemma phiTrueSubsts : forall a p, phiTrue = phiSubsts a p -> p = phiTrue.
Proof.
  induction a; intros.
  - simpl in H0.
    auto.
  - simpl in H0.
    apply IHa in H0.
    symmetry in H0.
    apply phiTrueSubst in H0.
    assumption.
Qed.
Lemma phiEqSubsts : forall a p e1 e2, phiEq e1 e2 = phiSubsts a p -> exists e1' e2', p = phiEq e1' e2' /\ e1 = eSubsts a e1' /\ e2 = eSubsts a e2'.
Proof.
  induction a; intros.
  - repeat eexists.
    simpl in H0.
    subst.
    auto.
  - simpl in H0.
    apply IHa in H0.
    inversion H0; clear H0.
    inversion H1; clear H1.
    intuition.
    subst.
    destruct p; simpl in H1; inversion H1.
    repeat eexists.
    * admit.
    * admit.
Admitted.

Lemma eSubstsVal : forall x v, eSubsts x (ev v) = (ev v).
Proof.
  induction x0; intros.
  - simpl; tauto.
  - specialize (IHx0 v0).
    assert (eSubsts (a :: x0) (ev v0) = eSubsts x0 (ev v0)).
    * admit.
    * rewrite IHx0 in H0.
      assumption.
Admitted.

Lemma phiImpliesConj : forall a b c, phiImplies a (phiConj b c) -> phiImplies a b.
Admitted.

Theorem staSemProgress : forall (prog : program) (s'' : s) (s' : list s) (pre post : phi) initialHeap initialRho initialAccess S',
  @hoareSingle prog pre s'' post ->
  evalphi initialHeap initialRho initialAccess pre ->
  exists finalState,
    @dynSem prog (initialHeap, (initialRho, initialAccess, s'' :: s') :: S') finalState
.
Proof.
  intro prog.
  induction S'.
  destruct s''; intros;
  inversion H0; clear H0; subst.
  - assert (evalphi initialHeap initialRho initialAccess (phiConj (phiAcc x0 f0) (phiNeq (ex x0) (ev vnull)))).
    eapply evalPhiImplies; eassumption.
    clear H1 H7.
    inversion H0; clear H0; subst.
    inversion H7; clear H7; subst.
    inversion H8; clear H8; subst.
    eexists.
    econstructor; try eassumption; try auto.
    eapply InAexcept.
    eauto.
  - eexists.
    econstructor.
    eauto.
  - eexists.
    econstructor;
    eauto.
  - specialize (HnotTotal initialHeap); intros.
    inversion H0.
    eexists.
    econstructor; eauto.
  - subst.
    specialize (evalPhiImplies initialHeap initialRho initialAccess pre (phiConj (phiConj (phiConj (phiAssert x1 (TClass C')) (phiNeq (ex x1) (ev vnull))) pp) pr)).
    intros.
    intuition.
    clear H1 H8.
    inversion H0; clear H0; subst.
    inversion H7; clear H7; subst.
    inversion H6; clear H6; subst.
    inversion H7; clear H7; subst.
    inversion H12; clear H12; subst.
    simpl in *.
    
    unfold mpre in *.
    unfold mcontract in *.
    case_eq (mmethod prog C' m0); intros.
    Focus 2.
      rewrite H0 in H9; simpl in H9; inversion H9.
    rewrite H0 in H9; simpl in H9.
    destruct m1.

    inversion H4; intuition.
    eexists (initialHeap, [(_, _, _) ; (initialRho, Aexcept initialAccess _, sCall x0 x1 m0 (map snd Xz') :: s')]).
    instantiate (l := ?y0).
    econstructor; eauto.
    * simpl.
      instantiate (wvs' := combine (map snd l) (map (λ z' : x, initialRho z') (map snd Xz'))).
      repeat rewrite mapSplitSnd.
      rewrite combine_split.
      simpl.
      repeat tauto.
      admit.
    * unfold mbody.
      rewrite H0.
      simpl.
      auto.
    * unfold mparams.
      rewrite H0.
      simpl.
      repeat rewrite mapSplitFst.
      rewrite combine_split.
      simpl.
      tauto.
      admit.
    * unfold mpre.
      unfold mcontract.
      rewrite H0.
      simpl.
      auto.
    * tauto.
    * destruct c.
      inversion H9; clear H9.
      subst.
      unfold option_map in H10.
      destruct (mpost prog C' m0); inversion H10; clear H10.
      subst.
      clear H4 H5.

      admit.
  - eexists.
    econstructor; tauto.
  - eexists.
    econstructor.
    eapply evalPhiImplies; eassumption.
  - eexists.
    econstructor.
    * eapply evalPhiImplies.
      + instantiate (q1 := pre).
        apply phiImpliesConj in H3.
        assumption.
      + assumption.
    * auto.
  - intros. intuition.
    inversion H3. clear H3.
    destruct x0.
    inversion H2; clear H2; subst;
    eexists; econstructor; try eassumption; try auto.
Admitted.

Theorem staSemSound : forall (prog : program) (body : list s) (pre post : phi) initialHeap initialRho initialAccess S',
  @hoare prog pre body post ->
  evalphi initialHeap initialRho initialAccess pre ->
  exists finalHeap finalRho finalAccess, (
    @dynSemStar prog (initialHeap, (initialRho, initialAccess, body) :: S') (finalHeap, (finalRho, finalAccess, []) :: S') /\
    evalphi finalHeap finalRho finalAccess post
  ).
Proof.
  intro prog.
  induction body; intros.
  - repeat eexists.
    * constructor.
    * inversion H0.
      subst.
      assumption.
  - inversion H0. clear H0.
    subst.
    specialize (IHbody q1 post).
    destruct a; inversion H4; clear H4; subst.
    * edestruct IHbody; clear IHbody.
      + eapply hoareImplies; repeat eauto.
      + econstructor.
      ++  eauto.
      ++  specialize (AexceptReverse initialAccess); intros.
          rewrite H0.
          eauto.
      ++  econstructor.
          ** simpl.
          inversion H0; clear H0.
          inversion H2; clear H2.
          inversion H0; clear H0.
          instantiate (initialAccess := x2).
          symmetry in H2. rewrite H2 in *.
          apply H1.

    edestruct IHbody; clear IHbody.

    Focus 3.
      inversion H0; clear H0.
      inversion H2; clear H2.
      inversion H0; clear H0.
      repeat eexists; eauto.
      econstructor.
      + destruct a; inversion H4; clear H4; subst.
    

    + eapply hoareImplies; repeat eauto.
    +
    + eapply hoareSingleEvalPhi; repeat eauto.
    + inversion H0; clear H0.
      inversion H2; clear H2.
      inversion H0; clear H0.
      repeat eexists; eauto.



    destruct a; inversion H4; clear H4; subst.
    * edestruct IHbody; clear IHbody.
      + eapply hoareImplies; repeat eauto.
      + econstructor.
      ++  eauto.
      ++  specialize (AexceptReverse initialAccess); intros.
          inversion H0; clear H0.
          inversion H2; clear H2.
          inversion H0; clear H0.
          instantiate (initialAccess := x2).
          symmetry in H2. rewrite H2 in *.
          apply H1.




      destruct a.
      * repeat econstructor.
        ++ simpl. .econstructor.
      econstructor.
      * destruct a.
      exists x0. exists x1. exists x2.
      repeat eexists.
      ++ econstructor.
      repeat eexists; eauto.
      econstructor; eauto.
      destruct a.
    inversion H4; clear H4; subst;
    repeat eexists.
    * 
      econstructor;
      edestruct IHbody.
      + econstructor.
        auto.
      + edestruct IHbody.
        specialize (IHbody initialHeap (rhoSubst x' vnull initialRho) initialAccess S').
        destruct IHbody.
        assert 
        erewrite IHbody.
        instantiate (b := (_, _)).
        admit.
      + 
    rewrite ESSStep.
    
    apply IHbody.
  generalize body. clear body


Theorem staSemSoundCorollary : forall prog : program,
  @hoare prog phiTrue (getMain prog) phiTrue -> exists endState : execState, @dynSemFull prog (newHeap, [(newRho, newAccess, getMain prog)]) endState.
Proof.
  destruct prog as [classes main]; simpl.
  generalize main. clear main.
  induction main; intros.
  - unfold runsThrough.
    eexists.
    split.
    * constructor.
    * unfold isFinished.
      repeat eexists.
  - destruct main.
    * 
  
  simpl in *.
  
  

(* playground *)
Open Scope string_scope.

Notation "AA '⊢sfrme' ee" := (sfrme AA ee) (at level 90).

Print sfrme.
Print dynSem.

Notation "classes 'main:' main" := (Program classes main) (at level 100).
Notation "'class' c { fs ms }" := (Cls c fs ms).

Check (Cls "a" [] []).



