Load GradVer20Hook_import.
Import Semantics.

(* EQ EXPANSION *)
Definition equ := prod e e.
Definition equs := list equ.

Fixpoint eSubste (eq : equ) (e' : e) : e :=
	  if e_dec e' (fst eq)
	  then (snd eq)
	  else match e' with
	       | edot e f => edot (eSubste eq e) f
	       | _ => e'
	       end.

(* enriches es using e *)
Definition eqsTransExpandSingle (e : equ) (es : equs) : equs :=
  flat_map (fun es' =>
    let es'a := fst es' in
    let es'b := snd es' in
    let es'a' := eSubste e es'a in
    let es'b' := eSubste e es'b in
    [(es'a , es'b )
    ;(es'a , es'b')
    ;(es'a', es'b )
    ;(es'a', es'b')]
    )
    es.

Fixpoint eqTransHull (es : equs) : equs :=
  match es with
  | [] => []
  | (e :: es) => e :: eqsTransExpandSingle e (eqTransHull es)
  end.

Definition phiEqualities' (p : phi) : equs :=
  flat_map (fun p =>
    match p with
    | phiEq a b => [(a, b); (b, a)]
    | _ => []
    end) p.
Fixpoint phiEqualities (p : phi) : equs := eqTransHull (phiEqualities' p).

Definition eTransExpand (e' : e) (eqs : equs) : list e :=
  map (fun eq => eSubste eq e') eqs.
Definition accTransExpand (a : A'_s) (eqs : equs) : list A'_s :=
  map (fun eq => (eSubste eq (fst a), snd a)) eqs.
Definition accsTransExpand (a : A_s) (eqs : equs) : A_s :=
  flat_map (fun a => accTransExpand a eqs) a.

Definition staticWorstCaseFootprint (p : phi) : A_s :=
  accsTransExpand (staticFootprint p) (phiEqualities p).

(* tests *)
Open Scope string_scope.
Eval compute in (phiEqualities [phiTrue]).
Definition testA : e := ex (xUserDef "a").
Definition testB : e := ex (xUserDef "b").
Definition testC : e := ex (xUserDef "c").
Definition testThis : e := ex xthis.
Definition testRes : e := ex xresult.
Eval compute in (phiEqualities [phiEq testA testB; phiEq testA testC]).
Eval compute in (phiEqualities [phiEq testA testB; phiEq testC testA]).
Eval compute in (phiEqualities [phiEq testA testB; phiEq testB testC]).
Eval compute in (phiEqualities [phiEq testA testB; phiEq testC testB]).
Eval compute in (phiEqualities [phiEq testA testC; phiEq testA testB]).
Eval compute in (phiEqualities [phiEq testC testA; phiEq testA testB]).
Eval compute in (phiEqualities [phiEq testB testC; phiEq testA testB]).
Eval compute in (phiEqualities [phiEq testC testB; phiEq testA testB]).
Eval compute in (eTransExpand testA (phiEqualities [phiEq testC testB; phiEq testA testB])).
Close Scope string_scope.
(* tests *)

(* DETERM *)

Definition isWithoutX (x : x) (phi : phi) : Prop :=
  forall p, In p phi -> ~ In x (FV' p).
Definition isWithoutAcc (A : A'_s) (phi : phi) : Prop :=
  forall p, In p phi -> ~ In A (staticFootprint' p).
Definition isWithoutAccs (A : A_s) (phi : phi) : Prop :=
  forall p, In p phi -> disjoint A (staticFootprint' p).
Definition isValidDivision (d : phi -> phi -> phi) : Prop :=
  forall a b, phiImplies a b -> phiImplies a (b ++ d a b).

Definition withoutX (x : x) (p : phi) : phi :=
  filter (fun p => negb (existsb (x_decb x) (FV' p))) p.
Definition withoutAcc (A : A'_s) (p : phi) : phi :=
  filter (fun p => negb (existsb (A'_s_decb A) (staticFootprint' p))) p.
Definition withoutAccs (A : A_s) (p : phi) : phi :=
  fold_right withoutAcc p A.
Definition divide (a : phi) (b : phi) : phi :=
  withoutAcc (staticWorstCaseFootprint b) a.

Lemma isWithoutAccsSFP : forall p1 p2,
  isWithoutAccs (staticFootprint p1) p2 <->
  disjoint (staticFootprint p1) (staticFootprint p2).
Proof.
  unfold isWithoutAccs, disjoint.
  split; intros.
  - apply not_and_or. intuition.
    unfold staticFootprint in H2.
    rewrite in_flat_map in H2.
    unf. eapply H in H2.
    inversionx H2; eauto.
  - specialize (H x).
    inversionx H; auto.
    apply or_intror.
    intuition.
    contradict H1.
    apply in_flat_map.
    eex.
Qed.

(* HOARE *)

Inductive hoareApp : Gamma -> phi -> list s -> phi -> Prop :=
| H'App : forall G(*\Gamma*) underscore(*\_*) phi(*\phi*) phi_p(*\*) phi_r(*\*) phi_q(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
    hasStaticType G (ex y) (TClass C) ->
    mmethod C m = Some (Method T_r m T_p z (Contract phi_pre phi_post) underscore) ->
    hasStaticType G (ex x) T_r ->
    hasStaticType G (ex z') T_p ->
    phiImplies phi [phiNeq (ex y) (ev vnull)] ->
    phiImplies phi phi_p ->
    phiImplies phi phi_r ->
    isWithoutAccs (staticFootprint phi_p) phi_r ->
    sfrmphi [] phi_r ->
    NotIn x (FV phi_r) ->
    listDistinct [x ; y ; z'] ->
    phi_p = phiSubsts2 xthis y (xUserDef z) z' phi_pre ->
    phi_q = phiSubsts3 xthis y (xUserDef z) z' xresult x phi_post ->
    hoareApp G phi [sCall x y m z'] (phi_q ++ phi_r)
.

Theorem hoareAppEquals : forall G p1 p2 s,
  hoareApp G p1 s p2 ->
  hoare    G p1 s p2.
Proof.
  intros.
  inversionx H.
  eca.
  unfold phiImplies.
  intros.
  
  assert (evalsIn h r (staticFootprint phi_r) (footprint h r phi_r))
  as ev_phi_r.
    eapp evalphiVSfp.
  assert (evalsIn h r (staticFootprint (phiSubsts2 xthis y (xUserDef z) z' phi_pre)) (footprint h r (phiSubsts2 xthis y (xUserDef z) z' phi_pre)))
  as ev_phi_pre.
    eapp evalphiVSfp.
  
  eca.
    apply inclEmpty.
    eappIn H4 H. inversionx H. auto.
  common.
  eapp evalphiAppRev.
  eappIn H6 H.
  eapp evalphiRemoveAexcept.
  unfold evalsIn in *.
  apply isWithoutAccsSFP in H7.
  
  unfold disjoint in *.
  intros.
  apply not_and_or. intuition.
  eappIn evalsInInRev H12.
  eappIn evalsInInRev H13.
  unf.
  specialize (H7 x1). inversionx H7; auto.
  