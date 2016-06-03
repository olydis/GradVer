Load GradVer12LemmaFootprint.
Import Semantics.


Fixpoint xdotInE (e : e) (x : x) (f : f) :=
  match e with
  | edot (ex x') f' => x = x' /\ f = f'
  | edot e' _ => xdotInE e' x f
  | _ => False
  end.

Definition xdotInPhi' (p : phi') (x : x) (f : f) :=
  match p with
  | phiEq  e1 e2 => xdotInE e1 x f \/ xdotInE e2 x f
  | phiNeq e1 e2 => xdotInE e1 x f \/ xdotInE e2 x f
  | _ => False
  end.

Fixpoint xdotInPhi (p : phi) (x : x) (f : f) :=
  match p with
  | [] => False
  | (p' :: p) => xdotInPhi' p' x f \/ xdotInPhi p x f
  end.

Lemma xdotphiStaticFootprintHelperSfrme : forall x f A e,
  ¬ In (x, f) A ->
  xdotInE e x f ->
  sfrme A e ->
  False.
Proof.
  destruct e0;
  simpl in *;
  intros;
  try inversion H1.
  inversionx H2.
  unf.
  subst.
  tauto.
Qed.

Lemma xdotphiStaticFootprintHelper : forall p x f A,
  sfrmphi A p ->
  ~ In (x, f) A ->
  xdotInPhi p x f ->
  In (x, f) (staticFootprint p).
Proof.
  induction p0;
  simpl;
  intros;
  inversionx H0;
  inversionx H2.
  - (*contradiction!*)
    destruct a; simpl in *; inversionx H0; inversionx H3;
    eapply xdotphiStaticFootprintHelperSfrme in H1; eauto;
    tauto.
  - apply in_app_iff.
    assert (CL := classic (In (x0, f0) (staticFootprint' a))).
    intuition.
    eapply IHp0 in H0; eauto.
    intro.
    apply in_app_or in H5.
    intuition.
Qed.

Lemma xdotphiStaticFootprint : forall p x f,
  sfrmphi [] p ->
  xdotInPhi p x f ->
  In (x, f) (staticFootprint p).
Proof.
  intros.
  eapply xdotphiStaticFootprintHelper; eauto.
Qed.

Lemma xdoteEvaluates : forall H r x f e v,
  evale H r e v ->
  xdotInE e x f ->
  exists o, r x = Some (vo o).
Proof.
  induction e0; intros; try inversionx H2.
  simpl in *.
  destruct e0.
  - eapply IHe0; eauto.
    eca.
  - unf.
    subst.
    inversionx H1.
    destruct (r x1); try inversionx H3.
    destruct v1; inversionx H2.
    eexists; eauto.
  - unfold evale in *.
    simpl in *.
    destruct (evale' H0 r e0); try inversionx H1.
    destruct v1; try inversionx H4.
    destruct (option_bind (λ x : C * (f → option v), snd x f2) (H0 o0)); eauto.
Qed.

Lemma xdotphiEvaluates : forall p A H r x f,
  evalphi H r A p ->
  xdotInPhi p x f ->
  exists o, r x = Some (vo o).
Proof.
  induction p0; intros; simpl in *;
  inversionx H2;
  inversionx H1.
  - inversionx H12;
    simpl in *;
    inversionx H3;
    eapply xdoteEvaluates in H1; eauto.
  - eapply IHp0; eauto.
Qed.

Lemma xdotphiFootprint : forall p A H r x f,
  sfrmphi [] p ->
  evalphi H r A p ->
  xdotInPhi p x f ->
  exists o, In (o, f) (footprint H r p).
Proof.
  intros.
  eapply xdotphiStaticFootprint in H1; eauto.
  eapply xdotphiEvaluates in H2; eauto.
  unf.
  exists x1.
  apply staticVSdynamicFP.
  eexists; split; eauto.
Qed.

(*odot*)

Definition odotInPhi (H : H) (r : rho) (p : phi) (o : o) (f : f) :=
  exists x, r x = Some (vo o) /\ xdotInPhi p x f.
