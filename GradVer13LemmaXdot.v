Load GradVer12LemmaFootprint.
Import Semantics.

Definition evalsIn H r A_s A_d := map (A'_s2A'_d H r) A_s = map Some A_d.

Lemma evalsInIn : forall H r As Ad As',
  evalsIn H r As Ad ->
  In As' As ->
  exists Ad', A'_s2A'_d H r As' = Some Ad' /\ In Ad' Ad.
Proof.
  induction As; intros; simpl in *; try tauto.
  unfold evalsIn in *.
  destruct Ad; try discriminate.
  repeat rewrite map_cons in H1.
  inversionx H1.
  inversionx H2.
  - eex.
    eca.
  - eappIn IHAs H5.
    unf.
    eex.
    eapp in_cons.
Qed.

Lemma evalsInInRev : forall H r As Ad Ad',
  evalsIn H r As Ad ->
  In Ad' Ad ->
  exists As', A'_s2A'_d H r As' = Some Ad' /\ In As' As.
Proof.
  intros.
  unfold evalsIn in H1.
  assert (In (Some Ad') (map Some Ad)).
    apply in_map_iff. eex.
  rewriteRevIn H1 H3.
  eapp in_map_iff.
Qed.

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

(*footprintX = stuff that DEFINITELY evaluates if in evalphi's arg*)

Definition footprintXe H r (e' : e) : A_d :=
  oflatten (map (A'_s2A'_d H r) (staticFootprintXe e')).

Definition footprintX' H r p : A_d :=
  oflatten (map (A'_s2A'_d H r) (staticFootprintX' p)).

Definition footprintX H r p : A_d :=
  oflatten (map (A'_s2A'_d H r) (staticFootprintX p)).

Lemma sfrmphiVSdfpX : forall p H r,
  sfrmphi [] p ->
  incl (footprintX H r p) (footprint H r p).
Proof.
  intros.
  apply sfrmphiVSsfpX in H1.
  simpl in *.
  unfold incl in *. intros.
  unfold footprintX in *.
  apply InOflatten in H2.
  apply in_map_iff in H2.
  unf.
  apply H1 in H4.
  destruct x0, a.
  unfold A'_s2A'_d in *.
  simpl in *.
  rewriteRev staticVSdynamicFP.
  eexists e0.
  destruct (evale' H0 r e0); try discriminate.
  simpl in *.
  destruct v0; try discriminate.
  inversionx H2.
  auto.
Qed.

Lemma evaleVSfpX : forall H r e v,
  evale H r e v ->
  evalsIn H r (staticFootprintXe e) (footprintXe H r e).
Proof.
  unfold evalsIn, footprintXe, A'_s2A'_d.
  induction e0; intros; simpl in *; try tauto.
  inversionx H1.
  destruct (evale' H0 r e0) eqn: ee; try discriminate.
  erewrite IHe0; eauto.
  simpl.
  destruct v1; try discriminate.
  simpl.
  rewrite oflattenMapSome.
  tauto.
Qed.

Lemma evalphi'VSfpX : forall H r p A,
  evalphi' H r A p ->
  evalsIn H r (staticFootprintX' p) (footprintX' H r p).
Proof.
  unfold footprintX', evalsIn.
  intros.
  inversionx H1; simpl;
  try rewrite map_app;
  repeat (erewrite evaleVSfpX; eauto);
  repeat rewrite oflattenApp;
  repeat rewrite oflattenMapSome;
  try rewrite map_app;
  tauto.
Qed.

Lemma evalphiVSfpX : forall H r p A,
  evalphi H r A p ->
  evalsIn H r (staticFootprintX p) (footprintX H r p).
Proof.
  unfold footprintX, evalsIn.
  induction p0; intros; simpl in *; try tauto.
  repeat rewrite map_app.
  inversionx H1.
  erewrite IHp0; eauto.
  erewrite evalphi'VSfpX; eauto.
  rewrite oflattenApp.
  rewrite map_app.
  repeat rewrite oflattenMapSome.
  tauto.
Qed.


Lemma evalphi'VSfp : forall H r p A,
  evalphi' H r A p ->
  evalsIn H r (staticFootprint' p) (footprint' H r p).
Proof.
  unfold evalsIn, A'_s2A'_d.
  intros.
  inversionx H1; simpl; try tauto.
  rewrite H3.
  tauto.
Qed.

Lemma evalphiVSfp : forall H r p A,
  evalphi H r A p ->
  evalsIn H r (staticFootprint p) (footprint H r p).
Proof.
  unfold evalsIn.
  induction p0; intros; simpl in *; try tauto.
  repeat rewrite map_app.
  inversionx H1.
  erewrite IHp0; eauto.
  erewrite evalphi'VSfp; eauto.
Qed.


(*evaluation*)

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


(* Lemma jointFootprint : forall p A H r,
  sfrmphi [] p ->
  evalphi H r A p ->
  incl (map (A'_s2A'_d H r) (staticFootprintX p)) (map Some (footprint H r p)).
Proof.
  intros.
  eapply sfrmphiVSsfpX in H1; eauto. simpl in *.
  eapply evalphiVSfpX in H2; eauto. unfold evalsIn in *.
  apply H1 in H3.
  unfold evalA'_s, A'_s2A'_d, evalA'_d in *.
  destruct A's; simpl in *.
  destruct (evale' H0 r e0) eqn: ee; try discriminate.
  simpl in *.
  destruct v0; try discriminate.
  simpl in *.
  eex.
  apply staticVSdynamicFP.
  eex.
Qed. *)


Lemma inclFPXe : forall e f H r e',
  In (e, f) (staticFootprintXe e') ->
  incl (footprintXe H r e) (footprintXe H r e').
Proof.
  induction e'; intros; simpl in *; try tauto.
  inversionx H1.
  - inversionx H2.
    unfold footprintXe.
    simpl.
    intuition.
  - intuition.
    eapp incl_tran.
    unfold footprintXe.
    simpl.
    intuition.
Qed.

Lemma inclFPX' : forall e f H r p,
  In (e, f) (staticFootprintX' p) ->
  incl (footprintXe H r e) (footprintX' H r p).
Proof.
  intros.
  destruct p0;
  try tauto;
  unfold footprintXe, footprintX';
  simpl in *;
  try apply in_app_iff in H1;
  repeat rewrite map_app, oflattenApp;
  fold footprintXe;
  try inversionx H1;
  try eappIn inclFPXe H1;
  try eappIn inclFPXe H2;
  unfold footprintXe, footprintX' in *;
  unfold incl; intros; intuition.
Qed.

Lemma inclFPX : forall e f H r p,
  In (e, f) (staticFootprintX p) ->
  incl (footprintXe H r e) (footprintX H r p).
Proof.
  induction p0; simpl; try tauto.
  intros.
  apply in_app_iff in H1.
  inversionx H1.
  - eappIn inclFPX' H2.
    eapp incl_tran.
    unfold footprintX', footprintX.
    simpl.
    rewrite map_app.
    rewrite oflattenApp.
    intuition.
  - apply IHp0 in H2.
    unfold footprintX', footprintX.
    simpl.
    rewrite map_app.
    rewrite oflattenApp.
    intuition.
Qed.
