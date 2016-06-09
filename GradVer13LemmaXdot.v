Load GradVer12LemmaFootprint.
Import Semantics.

(*staticFootprintX = the stuff that DEFINITELY evaluates if in evalphi's arg*)

Fixpoint staticFootprintXe (e' : e) : A_s :=
  match e' with
  | edot e f => (e, f) :: staticFootprintXe e
  | _ => []
  end.

Definition staticFootprintX' (p : phi') : A_s :=
  match p with
  | phiTrue => []
  | phiEq  e1 e2 => staticFootprintXe e1 ++ staticFootprintXe e2
  | phiNeq e1 e2 => staticFootprintXe e1 ++ staticFootprintXe e2
  | phiAcc e _ => staticFootprintXe e
  | phiType _ _ => []
  end.

Definition staticFootprintX (p : phi) : A_s :=
  flat_map staticFootprintX' p.

Lemma sfrmeVSsfpX : forall A e,
  sfrme A e <->
  incl (staticFootprintXe e) A.
Proof.
  induction e0;
  simpl in *;
  split;
  intros.
  - apply inclEmpty.
  - constructor.
  - apply inclEmpty.
  - constructor.
  - inversionx H0.
    eapp incl_cons.
    eapp IHe0.
  - apply incl_cons_reverse in H0. unf.
    eca.
Qed.

Lemma sfrmphi'VSsfpX : forall A p,
  sfrmphi' A p <->
  incl (staticFootprintX' p) A.
Proof.
  intros.
  destruct p0;
  simpl;
  split;
  intros.
  - apply inclEmpty.
  - constructor.
  - inversionx H0.
    apply incl_app;
    eapp sfrmeVSsfpX.
  - apply inclApp in H0. unf.
    constructor;
    eapp sfrmeVSsfpX.
  - inversionx H0.
    apply incl_app;
    eapp sfrmeVSsfpX.
  - apply inclApp in H0. unf.
    constructor;
    eapp sfrmeVSsfpX.
  - inversionx H0.
    eapp sfrmeVSsfpX.
  - constructor.
    eapp sfrmeVSsfpX.
  - apply inclEmpty.
  - constructor.
Qed.


Lemma sfrmphiVSsfpX : forall p A,
  sfrmphi A p ->
  incl (staticFootprintX p) (A ++ staticFootprint p).
Proof.
  induction p0;
  simpl;
  intros.
  - apply inclEmpty.
  - unf.
    rewrite sfrmphi'VSsfpX in H1.
    apply IHp0 in H2.
    unfold incl in *. intros.
    apply in_app_iff in H0. intuition.
    apply H2 in H3.
    apply in_app_iff in H3. intuition.
    apply in_app_iff in H0. intuition.
Qed.

Lemma evaleVSsfpX : forall H r e v A,
  evale H r e v ->
  In A (staticFootprintXe e) ->
  exists v', evalA'_s H r A = Some v'.
Proof.
  unfold evalA'_s, evalA'_d, A'_s2A'_d.
  induction e0; intros;
  inversionx H2;
  inversionx H1;
  simpl in *.
  - destruct (evale' H0 r e0); inversionx H3.
    destruct v1; inversionx H2.
    eex.
  - unfold evale in IHe0.
    destruct (evale' H0 r e0); inversionx H4.
    eapply IHe0; eauto.
Qed.

Lemma evalphi'VSsfpX : forall p A H r A',
  evalphi' H r A p ->
  In A' (staticFootprintX' p) ->
  exists v, evalA'_s H r A' = Some v.
Proof.
  intros.
  inversionx H1; try inversionx H2;
  simpl in *.
  - apply in_app_iff in H2.
    inversionx H2;
    eappIn evaleVSsfpX H1.
  - apply in_app_iff in H2.
    inversionx H2;
    eappIn evaleVSsfpX H1.
  - eapp evaleVSsfpX.
Qed.

Lemma evalphiVSsfpX : forall p A H r A',
  evalphi H r A p ->
  In A' (staticFootprintX p) ->
  exists v, evalA'_s H r A' = Some v.
Proof.
  induction p0; intros; simpl in *.
  - tauto.
  - apply in_app_iff in H2.
    inversionx H1.
    inversionx H2.
    * eapp evalphi'VSsfpX.
    * eapp IHp0.
Qed.

Lemma edotphiFootprint : forall p A H r A',
  sfrmphi [] p ->
  evalphi H r A p ->
  In A' (staticFootprintX p) ->
  exists o, In (o, f) (footprint H r p).
Proof.
  intros.
  eapply edotphiStaticFootprint in H1; eauto.
  eapply edotphiEvaluates in H2; eauto.
  unf.
  eexists.
  apply staticVSdynamicFP.
  eexists; split; eauto.
Qed.

Lemma edotphiFootprintX : forall p A H r e f,
  sfrmphi [] p ->
  evalphi H r A p ->
  edotInPhi p e f ->
  exists o, evale' H r e = Some (vo o) /\ In (o, f) (footprint H r p).
Proof.
  intros.
  eapply edotphiStaticFootprint in H1; eauto.
  eapply edotphiEvaluates in H2; eauto.
  unf.
  eex.
  apply staticVSdynamicFP.
  eexists; split; eauto.
Qed.

(*odot*)


Fixpoint odotInE (H : H) (r : rho) (e : e) (o : o) (f : f) :=
  match e with
  | edot e' f' => f = f' /\ evale H r e' (vo o)
               \/ odotInE H r e' o f
  | _ => False
  end.

Definition odotInPhi' (H : H) (r : rho) (p : phi') (o : o) (f : f) :=
  match p with
  | phiEq  e1 e2 => odotInE H r e1 o f \/ odotInE H r e2 o f
  | phiNeq e1 e2 => odotInE H r e1 o f \/ odotInE H r e2 o f
  | phiAcc e _ => odotInE H r e o f
  | _ => False
  end.

Fixpoint odotInPhi (H : H) (r : rho) (p : phi) (o : o) (f : f) :=
  match p with
  | [] => False
  | (p' :: p) => odotInPhi' H r p' o f \/ odotInPhi H r p o f
  end.


Lemma odotedotE : forall H r e' f o,
  odotInE H r e' o f <->
  exists e, evale' H r e = Some (vo o) /\ edotInE e' e f.
Proof.
  induction e'; split; intros; simpl in *; unf; try tauto.
  - inversionx H1.
    * unf. subst.
      eexists; split; eauto.
    * apply IHe' in H2.
      unf.
      eauto.
  - inversionx H3.
    * unf. subst.
      auto.
    * apply or_intror.
      apply IHe'.
      eauto.
Qed.

Lemma odotedotPhi' : forall H r p f o,
  odotInPhi' H r p o f <->
  exists e, evale' H r e = Some (vo o) /\ edotInPhi' p e f.
Proof.
  split; intros.
  - destruct p0; simpl in *;
    try inversionx H1;
    try apply odotedotE in H1;
    try apply odotedotE in H2;
    unf;
    simpl;
    eauto.
  - unf.
    destruct p0; simpl in *;
    try inversionx H3; simpl;
    repeat rewrite odotedotE;
    eauto.
Qed.

Lemma odotedotPhi : forall H r p f o,
  odotInPhi H r p o f <->
  exists e, evale' H r e = Some (vo o) /\ edotInPhi p e f.
Proof.
  induction p0; split; intros; simpl in *; unf; try tauto.
  - inversionx H1.
    * apply odotedotPhi' in H2. unf. eauto.
    * apply IHp0 in H2. unf. eauto.
  - inversionx H3.
    * rewrite odotedotPhi'. eauto.
    * apply or_intror.
      apply IHp0. 
      eauto.
Qed.


