Load GradVer19Theorems.
Import Semantics.


Definition dfrme H r (A : A_d) (e : e) := 
  evale' H r e <> None /\ incl (footprintXe H r e) A.

Lemma dfrmeVar : forall H1 H2 r A1 A2 x, 
  dfrme H1 r A1 (ex x) <->
  dfrme H2 r A2 (ex x).
Proof.
  intros.
  unfold dfrme, footprintXe. simpl.
  split; intros; unf;
  split; auto;
  apply inclEmpty.
Qed.

Lemma dfrmeEdot : forall H r A e f, 
  dfrme H r A (edot e f) ->
  (exists o, In (o, f) A /\ evale' H r e = Some (vo o)) /\
  dfrme H r A e.
Proof.
  unfold dfrme.
  intros. unf.
  unfold footprintXe in *.
  simpl in *.
  apply inclApp in H3. unf.
  unfold A'_s2A'_d, olist in H1.
  simpl in *.
  destruct (evale' H0 r e0); try tauto.
  destruct v0; try tauto.
  simpl in *.
  apply inclSingle in H1.
  
  split.
  - eex.
  - split; auto.
    discriminate.
Qed.