Load GradVer12LemmaFootprint.
Import Semantics.


Fixpoint edotInE (e' : e) (ee : e) (f : f) :=
  match e' with
  | edot e' f' => f = f' /\ ee = e'
               \/ edotInE e' ee f
  | _ => False
  end.

Definition edotInPhi' (p : phi') (ee : e) (f : f) :=
  match p with
  | phiEq  e1 e2 => edotInE e1 ee f \/ edotInE e2 ee f
  | phiNeq e1 e2 => edotInE e1 ee f \/ edotInE e2 ee f
  | phiAcc e _ => edotInE e ee f
  | _ => False
  end.

Fixpoint edotInPhi (p : phi) (ee : e) (f : f) :=
  match p with
  | [] => False
  | (p' :: p) => edotInPhi' p' ee f \/ edotInPhi p ee f
  end.

Lemma edotphiStaticFootprintHelperSfrme : forall e' f A e,
  ¬ In (e', f) A ->
  edotInE e e' f ->
  sfrme A e ->
  False.
Proof.
  induction e0;
  simpl in *;
  intros;
  inversionx H1;
  inversionx H2.
  - unf. subst.
    tauto.
  - apply IHe0; auto.
Qed.

Lemma edotphiStaticFootprintHelper : forall p e f A,
  sfrmphi A p ->
  ~ In (e, f) A ->
  edotInPhi p e f ->
  In (e, f) (staticFootprint p).
Proof.
  induction p0;
  simpl;
  intros;
  inversionx H0;
  inversionx H2.
  - (*contradiction!*)
    destruct a;
    simpl in *;
    try inversionx H0;
    inversionx H3;
    eapply edotphiStaticFootprintHelperSfrme in H1; eauto;
    try tauto.
  - apply in_app_iff.
    assert (CL := classic (In (e0, f0) (staticFootprint' a))).
    intuition.
    eapply IHp0 in H0; eauto.
    intro.
    apply in_app_or in H5.
    intuition.
Qed.

Lemma edotphiStaticFootprint : forall p e f,
  sfrmphi [] p ->
  edotInPhi p e f ->
  In (e, f) (staticFootprint p).
Proof.
  intros.
  eapply edotphiStaticFootprintHelper; eauto.
Qed.

Lemma edoteEvaluates : forall H r e' f e v,
  evale H r e v ->
  edotInE e e' f ->
  exists o, evale' H r e' = Some (vo o).
Proof.
  induction e0; intros;
  inversionx H2;
  inversionx H1.
  - unf. subst.
    destruct (evale' H0 r e0); inversionx H4.
    destruct v1; inversionx H2.
    eexists; eauto.
  - unfold evale in IHe0.
    destruct (evale' H0 r e0); inversionx H4.
    eapply IHe0; eauto.
Qed.

Lemma edotphiEvaluates : forall p A H r e f,
  evalphi H r A p ->
  edotInPhi p e f ->
  exists o, evale' H r e = Some (vo o).
Proof.
  induction p0; intros; simpl in *;
  inversionx H2;
  inversionx H1.
  - inversionx H12;
    simpl in *;
    try inversionx H3;
    try eapply edoteEvaluates in H1; eauto;
    try eapply edoteEvaluates in H2; eauto.
  - eapply IHp0; eauto.
Qed.

Lemma edotphiFootprint : forall p A H r e f,
  sfrmphi [] p ->
  evalphi H r A p ->
  edotInPhi p e f ->
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


