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
(* enriches e using es *)
Definition eqTransExpand (e : equ) (es : equs) : equs :=
  flat_map (fun es' =>
    let es'a := fst e in
    let es'b := snd e in
    let es'a' := eSubste es' es'a in
    let es'b' := eSubste es' es'b in
    [(es'a , es'b )
    ;(es'a , es'b')
    ;(es'a', es'b )
    ;(es'a', es'b')]
    )
    es.

Fixpoint eqTransHull (es : equs) : equs :=
  match es with
  | [] => []
  | (e :: es) => let es' := eqTransHull es in
                 e :: eqTransExpand e es' ++ eqsTransExpandSingle e es'
  end.

Definition phiEqualities' (p : phi) : equs :=
  flat_map (fun p =>
    match p with
    | phiEq a b => [(a, b); (b, a)]
    | _ => []
    end) p.
Definition phiEqualities (p : phi) : equs := eqTransHull (phiEqualities' p).

Definition eTransExpand (e' : e) (eqs : equs) : list e :=
  e' :: map (fun eq => eSubste eq e') eqs.
Definition accTransExpand (a : A'_s) (eqs : equs) : list A'_s :=
  a :: map (fun eq => (eSubste eq (fst a), snd a)) eqs.
Definition accsTransExpand (a : A_s) (eqs : equs) : A_s :=
  flat_map (fun a => accTransExpand a eqs) a.

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
  withoutAccs (accsTransExpand (staticFootprint b) (phiEqualities a)) a.

Lemma withoutAccsAlt : forall A p,
  withoutAccs A p = filter (fun p => negb (existsb (fun a => existsb (A'_s_decb a) A) (staticFootprint' p))) p.
Proof.
  induction A; simpl.
  - induction p0; simpl; auto.
    symmetry in IHp0.
    rewrite IHp0.
    destruct a; auto.
  - intros.
    rewrite IHA. clear IHA.
    unfold withoutAcc.
    generalize p0. clear.
    induction p0; simpl; auto.
    symmetry in IHp0.
    rewrite IHp0. clear IHp0.
    destruct a0; auto.
    simpl.
    destruct (existsb (A'_s_decb (e, f)) A) eqn: exx.
    * rewrite orb_true_r.
      auto.
    * simpl.
      dec (A'_s_dec a (e, f)).
      + dec (A'_s_dec (e, f) (e, f)).
        auto.
      + rename de2 into de.
        dec (A'_s_dec (e, f) a). tauto.
        auto.
Qed.

Lemma phiImpliesFilter : forall p f,
  phiImplies p (filter f p).
Proof.
  unfold phiImplies.
  induction p0;
  intros. eca.
  simpl.
  inversionx H.
  destruct (f a).
  - eca.
  - eapp IHp0.
    eapp evalphiAexcept.
Qed.

Lemma divideImplies : forall a b,
  phiImplies a (divide a b).
Proof.
  intros.
  unfold divide.
  rewrite withoutAccsAlt.
  apply phiImpliesFilter.
Qed.

Lemma phiImpliesAccReorder : forall e f p,
  phiSatisfiable p ->
  In (phiAcc e f) p ->
  forall h r a, evalphi h r a p <-> evalphi h r a ((phiAcc e f) :: (filter (fun p => negb (phi'_decb (phiAcc e f) p)) p)).
Proof.
Admitted.

Lemma phiEqualitiesInclCons : forall p' p,
  incl (phiEqualities p) (phiEqualities (p' :: p)).
Proof.
  unfold incl.
  intros.
  destruct a.
  destruct p'; try apply H.
  simpl.
  repeat apply or_intror.
  apply in_app_iff. apply or_intror.
  simpl.
  repeat apply or_intror.
  apply in_flat_map.
  exists (e, e0). split; simpl; auto.
  apply in_app_iff. apply or_intror.
  apply in_flat_map.
  exists (e, e0). split; simpl; auto.
Qed.

Lemma phiEqualitiesInclEq : forall p' p,
  (forall e1 e2, p' <> phiEq e1 e2) ->
  phiEqualities (p' :: p) = phiEqualities p.
Proof.
  intros.
  unfold phiEqualities.
  simpl.
  destruct p'; auto.
  specialize (H e e0).
  tauto.
Qed.

Require Import Coq.Logic.Classical_Pred_Type.

(* Lemma eSubstseChain : forall e eq1 eq2,
  eSubste eq2 (eSubste eq1 e) =
  eSubste (eSubste eq2 (fst eq1), eSubste eq2 (snd eq1)) e.
Proof.
  induction e; intros. *)

Lemma phiImplesAccHelper : forall f o h r a p0 e1 e2,
  let ff := filter (λ p : phi', negb (phi'_decb (phiAcc e2 f) p)) p0 in
  evale' h r e1 = Some (vo o) ->
  evale' h r e2 = Some (vo o) ->
  In (o, f) a ->
  phiImplies (phiAcc e2 f :: ff) [phiAcc e1 f] ->
  evalphi h r (Aexcept a [(o, f)]) ff ->
  (e1, f) = (e2, f)
    ∨ In (e2, f) (map (λ eq : equ, (eSubste eq e1, f)) (phiEqualities p0)).
Proof.
  induction p0; intros; simpl in *.
  - subst ff.
    destruct (classic (e1 = e2)). subst. auto.
    contradict H4.
    unfold phiImplies in *.
    admit.
  - unfold phi'_decb in *.
    set (ff' := filter
               (λ p : phi', negb (dec2decb phi'_dec (phiAcc e2 f) p))
               p0) in *.
    unfold dec2decb in ff.
    destruct (phi'_dec (phiAcc e2 f) a0);
    simpl in ff;
    subst ff.
    * specialize (IHp0 e1 e2). subst.
      apply IHp0 in H1; auto.
    * assert (phiImplies (a0 :: phiAcc e2 f :: ff') [phiAcc e1 f]) as pi.
        unfold phiImplies. intros.
        eapp H2.
        inversionx H4. inversionx H15.
        eca. eapp inclAexcept.
        eca. eapp inclAexceptTriple.
        rewrite AexceptComm.
        assumption.
      clear H2.
      destruct (classic (∀ e1 e2 : e, a0 ≠ phiEq e1 e2)).
      + rewrite phiEqualitiesInclEq; auto.
        eapp IHp0.
        admit.
        inversionx H3.
        eapp evalphiAexcept.
      + apply not_all_ex_not in H2. invE H2 ee1.
        apply not_all_ex_not in H2. invE H2 ee2.
        apply NNPP in H2. subst.
        clear n.
        unfold phiEqualities.
        simpl.
        specialize (IHp0 (eSubste (ee1, ee2) e1) e2).
        admit.
Admitted.

Lemma phiImpliesAcc : forall h r a e2 f p e1,
  evale' h r e1 = evale' h r e2 ->
  evalphi h r a p ->
  phiImplies p [phiAcc e1 f] ->
  In (phiAcc e2 f) p ->
  In (e2, f) (accTransExpand (e1, f) (phiEqualities p)).
Proof.
  intros.
  (*in*)
  assert (HH := H0).
  eappIn evalphiIn HH.
  inversionx HH.
  (*done*)
  common.
  set (p1 := (phiAcc e2 f) :: (filter (fun p => negb (phi'_decb (phiAcc e2 f) p)) p0)).
  assert (phiImplies p1 [phiAcc e1 f]) as H1'.
    eappIn phiImpliesTrans H1.
    subst p1.
    unfold phiImplies.
    intros.
    eapp phiImpliesAccReorder.
    eex.
  assert (evalphi h r a p1) as H0'.
    subst p1.
    rewriteRev phiImpliesAccReorder; auto.
    eex.
  clear H0 H1 H2.
  subst p1.
  inversionx H0'.
  simpl in *.
  rewrite H9 in *.
  clear H4 H11.
  eapp phiImplesAccHelper.
Qed.

Lemma divideDistinctFootprint : forall h r A a b,
  evalphi h r A a ->
  phiImplies a b ->
  disjoint (footprint h r (divide a b)) (footprint h r b).
Proof.
  induction b; simpl; intros;
  rename H0 into im;
  rename H into sat.
  - unfold disjoint.
    intuition.
  - unfold disjoint in *.
    intuition.
    assert (phiImplies a b) as IH.
      rewrite cons2app in im.
      eapp phiImpliesTrans.
      eapp phiImpliesSuffix.
    eapply H in IH. clear H.
    inversionx IH.
    * apply or_introl.
      intro HH.
      contradict H.
      unfold footprint in *.
      apply in_flat_map in HH.
      apply in_flat_map.
      unf. eex.
      unfold divide in *.
      rewrite withoutAccsAlt in *.
      apply filter_In in H0.
      apply filter_In.
      unf. split; auto.
      apply not_false_iff_true.
      apply not_false_iff_true in H2.
      intuition.
      contradict H2.
      rewrite negb_false_iff in *.
      apply existsb_exists.
      apply existsb_exists in H0.
      unf. eex.
      apply existsb_exists.
      apply existsb_exists in H3.
      unf. eex.
      simpl.
      unfold accsTransExpand in *.
      apply in_flat_map.
      apply in_flat_map in H3.
      unf. eex.
      intuition.
    * apply not_and_or.
      intuition.
      apply in_app_iff in H2.
      inversionx H2; auto. clear H.
      unfold footprint in *. apply in_flat_map in H1. unf.
      destruct a0; auto.
      destruct x0; auto.
      simpl in *.
      destruct (evale' h r e) eqn: ee1; auto.
      destruct (evale' h r e0) eqn: ee2; auto.
      destruct v; auto.
      destruct v0; auto.
      apply InSingle in H0.
      apply InSingle in H2.
      subst.
      inversionx H2.
      unfold divide in *.
      rewrite withoutAccsAlt in H1.
      apply filter_In in H1. unf.
      apply not_false_iff_true in H0.
      contradict H0.
      apply negb_false_iff.
      apply existsb_exists.
      eapply phiImpliesAcc in H.
        Focus 2. rewrite ee1, ee2. auto.
        Focus 2. eauto.
        Focus 2. rewrite cons2app in im. eapp phiImpliesTrans. eapp phiImpliesPrefix.
      
      simpl. exists (e0, f0). split; auto.
      apply orb_true_intro.
      inversionx H. inversionx H0. constructor. dec (A'_s_dec (e0, f0) (e0, f0)). auto.
      apply or_intror.
      apply existsb_exists.
      exists (e0, f0). split. Focus 2. dec (A'_s_dec (e0, f0) (e0, f0)). auto.
      apply in_app_iff.
      auto.
Qed.

Lemma divideIsValidDivision :
  isValidDivision divide.
Proof.
  unfold isValidDivision.
  intros.
  unfold phiImplies.
  intros.
  eapp evalphiAppRev.
  assert (sat := H0).
  eapply divideImplies in H0.
  eapp evalphiRemoveAexcept.
  eapp divideDistinctFootprint.
Qed.

Definition divideTrue (a : phi) (b : phi) : phi := [].

Lemma divideTrueIsValidDivision :
  isValidDivision divideTrue.
Proof.
  unfold isValidDivision.
  intros.
  unfold divideTrue.
  rewrite app_nil_r.
  assumption.
Qed.

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

Definition dividex := divideTrue.
Lemma dividexISD : isValidDivision dividex.
Proof. eapp divideTrueIsValidDivision. Qed.

Inductive hoareApp : Gamma -> phi -> list s -> phi -> Prop :=
| H'App : forall G(*\Gamma*) underscore(*\_*) phi(*\phi*) phi_p(*\*) phi_r(*\*) phi_q(*\*) T_r T_p (C : C) (m : m) z (z' : x) x y phi_post(*\phi_{post}*) phi_pre(*\phi_{pre}*),
    hasStaticType G (ex y) (TClass C) ->
    mmethod C m = Some (Method T_r m T_p z (Contract phi_pre phi_post) underscore) ->
    hasStaticType G (ex x) T_r ->
    hasStaticType G (ex z') T_p ->
    phiImplies phi [phiNeq (ex y) (ev vnull)] ->
    phiImplies phi phi_p ->
    phi_r = dividex phi phi_p ->
    sfrmphi [] phi_r ->
    NotIn x (FV phi_r) ->
    listDistinct [x ; y ; z'] ->
    phi_p = phiSubsts2 xthis y (xUserDef z) z' phi_pre ->
    phi_q = phiSubsts3 xthis y (xUserDef z) z' xresult x phi_post ->
    hoareApp G phi [sCall x y m z'] (phi_q ++ phi_r)
.

Theorem hoareAppWorks : forall G p1 p2 s,
  hoareApp G p1 s p2 ->
  hoare    G p1 s p2.
Proof.
  intros.
  inversionx H.
  eca.
  unfold phiImplies.
  intros.
  
  eca.
    apply inclEmpty.
    eappIn H4 H. inversionx H. auto.
  common.
  eapp dividexISD.
Qed.