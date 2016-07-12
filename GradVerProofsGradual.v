Load GradVer20Hook_import.
Import Semantics.


Theorem alphaSound : forall pp1 gp pp2,
  gAlpha pp1 gp ->
  gGamma gp pp2 ->
  pincl pp1 pp2.
Proof.
  intros.
  inversionx H.
  - inversionx H0.
    inversionx H1.
    unfold
      pincl,
      gGamma',
      ppIsSingleton
    in *. unf.
    intros.
    simpl.
    eapp H4.
  - inversionx H0.
    inversionx H1.
    unfold
      pincl,
      ppHasUpperBound,
      ppHasSupremum,
      ppIsSingleton
    in *. unf.
    intros.
    split.
    * eapp H4.
    * eapp H0.
  - inversionx H0.
    inversionx H1.
    unfold
      pincl,
      ppHasSupremum,
      ppIsSingleton
    in *.
    intros.
    split.
    * eapp H4.
    * unfold phiImplies.
      intros.
      constructor.
Qed.

Require Import Coq.Logic.Classical_Pred_Type.

Definition phiFalse : phi' := phiNeq (ev vnull) (ev vnull).
Lemma phiFalseNotSat : ~ phiSatisfiable [phiFalse].
Proof.
  intuition.
  inversionx H. unf.
  inversionx H0.
  inversionx H9.
  common.
  inversionx H2. inversionx H7.
  tauto.
Qed.

Fixpoint eSubste (eq : prod e e) (e' : e) : e :=
	  if e_dec e' (fst eq)
	  then (snd eq)
	  else match e' with
	       | edot e f => edot (eSubste eq e) f
	       | _ => e'
	       end.

Definition eSubstsEnum (e1 e2 : e) (e' : e) : list e :=
  [ e'
  ; eSubste (e1, e2) e'
  ; eSubste (e2, e1) e'
  ].

Definition phi'SubstsEnum (a b : e) (p : phi') : list phi' :=
  match p with
  | phiTrue => [phiTrue]
  | phiEq e1 e2 => map (fun p => phiEq (fst p) (snd p)) 
                       (list_prod (eSubstsEnum a b e1)
                                  (eSubstsEnum a b e2))
  | phiNeq e1 e2 => map (fun p => phiNeq (fst p) (snd p)) 
                       (list_prod (eSubstsEnum a b e1)
                                  (eSubstsEnum a b e2))
  | phiAcc e f => map (fun e => phiAcc e f)
                       (eSubstsEnum a b e)
  end.

Fixpoint phiSubstsEnum (a b : e) (p : phi) : list phi :=
  match p with
  | [] => [[]]
  | p :: ps => flat_map (fun ps => map (fun p => p :: ps) 
                                  (phi'SubstsEnum a b p))
                        (phiSubstsEnum a b ps)
  end.

Inductive phiImplySplit : phi -> phi -> phi -> phi -> Prop :=
| PIS : forall p1,
  phiImplySplit p1 [] [] []
| PIS1 : forall p1 p p2 p2a p2b,
  phiImplySplit p1 p2 p2a p2b ->
  phiImplies p1 [p] ->
  phiImplySplit p1 (p :: p2) (p :: p2a) p2b
| PIS2 : forall p1 p p2 p2a p2b,
  phiImplySplit p1 p2 p2a p2b ->
  ~ phiImplies p1 [p] ->
  phiImplySplit p1 (p :: p2) p2a (p :: p2b)
.

Definition phiJoin (a b c : phi) : Prop :=
  exists b1 b2 a1 a2, phiImplySplit a b b1 b2
                   /\ phiImplySplit b2 a a1 a2
                   /\ c = b1 ++ a1.

Lemma phiJoinTest1 : forall x y f g,
  x <> y ->
  f <> g ->
  phiJoin
    [phiAcc x f; phiAcc y g; phiEq x y; phiEq (edot x f) (ev (vn 3)); phiNeq (edot x f) (ev (vn 5))]
    [phiAcc y f; phiNeq (edot x f) (ev (vn 4))]
    [phiAcc y f; phiNeq (edot x f) (ev (vn 4))].
Proof.
  intros.
  exists [phiAcc y f; phiNeq (edot x f) (ev (vn 4))].
  exists [].
  exists [].
  exists [phiAcc x f; phiAcc y g; phiEq x y; phiEq (edot x f) (ev (vn 3)); phiNeq (edot x f) (ev (vn 5))].
  repeat split.
  - eca. eca. eca.
    * repeat intro.
      inversionx H1.
      inversionx H12.
      inversionx H14.
      inversionx H16.
      inversionx H17.
      common. inversionx H14.
      repeat eca.
      + apply inclEmpty.
      + discriminate.
    * repeat intro.
      inversionx H1.
      inversionx H12.
      inversionx H14.
      inversionx H11.
      inversionx H15.
      common. rewrite H10 in *. inversionx H4.
      repeat eca;
      simpl in *;
      rewrite H10, H14 in *.
      + assumption.
      + apply in_eq.
  - eca. eca. eca. eca. eca. eca.
    * intuition.
      specialize (H1 newHeap newRho newAccess).
      lapply H1; try constructor.
      intro.
      inversionx H2.
      inversionx H12.
      unfold evale in *.
      simpl in *.
      destruct (evale' newHeap newRho x); inversionx H5.
      destruct v; inversionx H3.
    * intuition.
      specialize (H1 newHeap newRho newAccess).
      lapply H1; try constructor.
      intro.
      inversionx H2.
      inversionx H12.
      unfold evale in *.
      simpl in *.
      destruct (evale' newHeap newRho x); inversionx H5.
      destruct v; inversionx H3.
    * intuition.
      specialize (H1 newHeap newRho newAccess).
      lapply H1; try constructor.
      intro.
      inversionx H2.
      inversionx H12.
      unfold evale in *.
      simpl in *.
      destruct x, y; simpl in *; try discriminate.
      + inversionx H10.
        inversionx H5.
        tauto.
      + destruct (evale' newHeap newRho y); inversionx H10.
        destruct v0; inversionx H3.
      + destruct (evale' newHeap newRho x); inversionx H5.
        destruct v0; inversionx H3.
      + destruct (evale' newHeap newRho y); inversionx H10.
        destruct v; inversionx H3.
    * intuition.
      specialize (H1 newHeap newRho newAccess).
      lapply H1; try constructor.
      intro.
      inversionx H2.
      inversionx H12.
      unfold evale in *.
      simpl in *.
      destruct y; simpl in *; try discriminate.
      destruct (evale' newHeap newRho y); inversionx H9.
      destruct v; inversionx H3.
    * intuition.
      specialize (H1 newHeap newRho newAccess).
      lapply H1; try constructor.
      intro.
      inversionx H2.
      inversionx H12.
      unfold evale in *.
      simpl in *.
      destruct x; simpl in *; try discriminate.
      destruct (evale' newHeap newRho x); inversionx H9.
      destruct v; inversionx H3.
Qed.

Lemma phiJoinTest2 : forall x y f,
  x <> y ->
  phiJoin
    [phiAcc x f]
    [phiAcc y f]
    [].
Proof.
  intros.
  exists [].
  exists [phiAcc y f].
  exists [].
  exists [phiAcc x f].
  repeat split.
  - eca. eca.
    intuition.
    admit.
  - eca. eca.
    intuition.
    admit.
Admitted.

Lemma phiJoinTest3 : forall x y f,
  x <> y ->
  phiJoin
    [phiAcc x f; phiEq x y]
    [phiAcc y f; phiEq x y]
    [phiAcc y f; phiEq x y].
Proof.
  intros. rename H into ug.
  exists [phiAcc y f; phiEq x y].
  exists [].
  exists [].
  exists [phiAcc x f; phiEq x y].
  repeat split.
  - eca. eca. eca.
    * repeat intro.
      inversionx H.
      eapp evalphiAexcept.
    * repeat intro.
      inversionx H.
      inversionx H10.
      inversionx H9.
      inversionx H11.
      common. rewrite H7 in *. inversionx H2.
      repeat eca;
      simpl in *;
      rewrite H7, H10 in *.
      + assumption.
      + apply in_eq.
  - eca. eca. eca.
    * intuition.
      specialize (H newHeap newRho newAccess).
      lapply H; try constructor.
      intro.
      inversionx H0.
      inversionx H10.
      unfold evale in *.
      destruct x, y; simpl in *; try discriminate.
      + inversionx H8.
        inversionx H3.
        tauto.
      + destruct (evale' newHeap newRho y); inversionx H8.
        destruct v0; inversionx H1.
      + destruct (evale' newHeap newRho x); inversionx H3.
        destruct v0; inversionx H1.
      + destruct (evale' newHeap newRho y); inversionx H8.
        destruct v; inversionx H1.
    * intuition.
      specialize (H newHeap newRho newAccess).
      lapply H; try constructor.
      intro.
      inversionx H0.
      inversionx H10.
      unfold evale in *.
      simpl in *.
      destruct x; simpl in *; try discriminate.
      destruct (evale' newHeap newRho x); inversionx H7.
      destruct v; inversionx H1.
Qed.

Lemma phiJoinSound : forall p2 p1 p3,
  phiJoin p1 p2 p3 ->
  phiImplies p1 p3 /\
  phiImplies p2 p3.
Proof.
  induction p2; induction p1; intros.
  - inversionx H. unf.
    inversionx H0.
    inversionx H.
    split; apply phiImpliesRefl.
  - unfold phiJoin in *. unf.
    inversionx H0.
    inversionx H.
    * specialize (IHp1 p2a).
      lapply IHp1; intros.
      + unf.
        simpl in *.
        split.
          repeat intro.
          inversionx H.
          eca.
        repeat intro.
        rewrite cons2app.
        apply evalphiAppRev.
          eapp H6.
        eapp H1. eca.
      + eexists.
        exists [].
        exists p2a.
        exists x2.
        split. eca.
        split. auto.
        auto.
    * specialize (IHp1 x1).
      lapply IHp1; intros.
      + unf.
        simpl in *.
        split.
          repeat intro.
          eapp H0.
          inversionx H.
          eapp evalphiAexcept.
        assumption.
      + eexists.
        exists [].
        exists x1.
        exists p2b.
        split. eca.
        split. auto.
        auto.
  - unfold phiJoin in *. unf.
    inversionx H.
    repeat rewrite app_nil_r in *.
    inversionx H0.
    * specialize (IHp2 [] p2a).
      lapply IHp2; intros.
      + unf.
        split.
          repeat intro.
          rewrite cons2app.
          apply evalphiAppRev.
            eapp H6.
          eapp H0.
          eca.
        repeat intro.
        inversionx H.
        eca.
      + exists p2a.
        exists x0.
        eexists.
        eexists.
        split. auto.
        split. eca.
        rewrite app_nil_r.
        auto.
    * specialize (IHp2 [] x).
      lapply IHp2; intros.
      + unf.
        split.
          auto.
        repeat intro.
        eapp H1.
        inversionx H.
        eapp evalphiAexcept.
      + exists x.
        exists p2b.
        eexists.
        eexists.
        split. auto.
        split. eca.
        rewrite app_nil_r.
        auto.
  - unfold phiJoin in *. unf.
    inversionx H0.
    * specialize (IHp2 (a0 :: p1) (p2a ++ x1)).
      lapply IHp2; intros.
      + unf.
        split.
          repeat intro.
          rewriteRev app_comm_cons.
          rewrite cons2app.
          apply evalphiAppRev.
            eapp H8.
          eapp H1.
          eca.
          
          auto.
        repeat intro.
        eapp H1.
        inversionx H.
        eapp evalphiAexcept.
      + exists x.
        exists p2b.
        eexists.
        eexists.
        split. auto.
        split. eca.
        rewrite app_nil_r.
        auto.
    repeat rewrite app_nil_r in *.
    inversionx H0.
    * subst.
      (* assert (x0 = p2). admit.
      subst.
       *)
      specialize (IHp3 p1 p2).
      lapply IHp3; intros.
        admit.
      exists [].
      exists x0.
        
      + specialize (IHp3 (a :: p5) p2).
        lapply IHp3; intros.
        admit.
        exists [].
        exists x0.
        exists x0.
      + .
    
Definition phiImpliesConsEqHelper : forall p p' px a e1 e2,
  phiSatisfiable (phiEq e1 e2 :: p) ->
  phiImplies (phiEq e1 e2 :: p) (a :: p') ->
  In px (phiSubstsEnum e1 e2 p') ->
  phiImplies p px ->
  exists x,
    In x (phi'SubstsEnum e1 e2 a) /\
    phiImplies p (x :: px).
Proof.
  (* induction p0; intros.
    assert (∀ H r A, evalphi H r A px) as tt.
      eapp phiImpliesTauto.
    admit.
  specialize *)
  destruct a; simpl.
  - eex.
    eapp phiImpliesTrans.
    admit.
  - admit.
  - admit.
  - intros.
    
Admitted.

Definition phiImpliesConsEq : forall p p' e1 e2,
  phiSatisfiable (phiEq e1 e2 :: p) ->
  phiImplies (phiEq e1 e2 :: p) p'
  -> 
  exists px,
  In px (phiSubstsEnum e1 e2 p') /\
  phiImplies p px.
Proof.
  induction p'; intros; simpl in *.
    eex.
    eapp phiImpliesPrefix. eapp phiImpliesRefl.
  assert (phiImplies (phiEq e1 e2 :: p0) p') as IH.
    eapp phiImpliesTrans.
    rewrite cons2app. eapp phiImpliesSuffix.
  apply IHp' in IH; auto.
  invE IH px. unf.
  eappIn phiImpliesConsEqHelper H.
  unf.
  eexists (x :: px).
  split; auto.
  apply in_flat_map.
  eex.
  apply in_map_iff.
  eex.
Qed.

Definition phiImpliesAccessHelper : forall p e f e1 e2,
  phiSatisfiable (phiEq e1 e2 :: p) ->
  phiImplies (phiEq e1 e2 :: p) [phiAcc e f]
  -> 
    phiImplies p [phiAcc e f]
  ∨ phiImplies p [phiAcc (eSubste (e1, e2) e) f]
  ∨ phiImplies p [phiAcc (eSubste (e2, e1) e) f].
Proof.
  induction p0; intros.
  - contradict H0.
    invE H h.
    invE H r.
    invE H a.
    apply evalphiFootprintAccess in H. simpl in *.
    
    unfold phiImplies.
    apply ex_not_not_all.
    exists h.
    apply ex_not_not_all.
    exists r.
    apply ex_not_not_all.
    exists [].
    apply ex_not_not_all.
    eexists. assumption.
    intuition.
    inversionx H0.
    inversionx H10.
    simpl in *. rewrite H7 in *.
    apply inclEmptyFalse in H5.
    tauto.
  - assert (phiSatisfiable (phiEq e1 e2 :: p0)) as IH.
      invE H h'.
      invE H r'.
      invE H a'.
      exists h'. exists r'. exists a'.
      inversionx H. eca.
      inversionx H11. common.
      eapp evalphiAexcept.
    
Admitted.

(* Definition phiImpliesAccessHelper2 : forall *)

Lemma evalphiInclFootprint : forall p1 p2,
  phiImplies p1 p2 ->
  forall H r,
    evalphi H r (footprint H r p1) p1 ->
    incl (footprint H r p2) (footprint H r p1).
Proof.
  intros.
  apply H in H1.
  eapp evalphiImpliesAccess.
Qed.

Definition phiImpliesAccess : forall p e f,
  phiSatisfiable p ->
  phiImplies p [phiAcc e f] ->
  exists e', In (phiAcc e' f) p /\ phiImplies p [phiEq e e'].
Proof.
  intros.
  assert (forall H r A, 
      evalphi H r A p0 ->
      exists o,
        evale' H r e = Some (vo o) /\
        In (o, f) A).
    intros.
    apply H0 in H2.
    inversionx H2.
    inversionx H12.
    eex.
  
  Check evalphiVSfp.
  
  assert (forall H r,
    evalphi H r (footprint H r p0) p0 ->
    evalsIn H r (staticFootprint p0) (footprint H r p0) /\
    evalsIn H r (staticFootprint [phiAcc e f]) (footprint H r [phiAcc e f]) /\
    incl (footprint H r [phiAcc e f]) (footprint H r p0)) as HH.
    intros.
    split. eapp evalphiVSfp.
    split. apply H0 in H3. eapp evalphiVSfp.
    eapp evalphiInclFootprint.
  Check dynamicASstaticFP.
  assert (forall H r,
    evalphi H r (footprint H r p0) p0 ->
    incl (footprint H r [phiAcc e f]) 
         (oflatten (map (A'_s2A'_d H r) (staticFootprint p0))) /\
    exists o, evale' H r e = Some (vo o)) as HHH.
    intros.
    repeat rewriteRev dynamicASstaticFP.
    split. eapp evalphiInclFootprint.
    apply H0 in H3.
    inversionx H3. inversionx H13.
    eex.
  assert (forall H r,
    evalphi H r (footprint H r p0) p0 ->
    exists e' o,
    In (phiAcc e' f) p0 /\
    evale' H r e' = Some (vo o) /\
    evale' H r e = Some (vo o)
    ) as HHHH.
    intros.
    apply HHH in H3.
    unf.
    simpl in *.
    rewrite H3 in H4.
    rewrite app_nil_r in *.
    apply inclSingle in H4.
    apply InOflatten in H4.
    apply in_map_iff in H4.
    unf.
    unfold staticFootprint in H6.
    apply in_flat_map in H6.
    unf.
    destruct x1; try tauto.
    simpl in *.
    inversionx H7; try tauto.
    unfold A'_s2A'_d in H4.
    simpl in *.
    destruct (evale' H2 r e0) eqn: H3'; try discriminate.
    destruct v; try discriminate.
    simpl in *.
    inversionx H4.
    eex.
  assert (forall H r a,
    evalphi H r a p0 ->
    exists e',
    In (phiAcc e' f) p0 /\
    evalphi H r [] [phiEq e e']
    ) as HHHHH.
    intros.
    apply evalphiFootprintAccess in H3.
    apply HHHH in H3.
    unf.
    eex.
    repeat eca.
    apply inclEmpty.

  destruct (classic (In (phiAcc e f) p0)).
    eex. unfold phiImplies. intros.
    assert (H3' := H3).
    eappIn evalphiIn H2. inversionx H2.
    repeat eca.
    apply inclEmpty.
  rename H2 into ni.

  invE H h.
  invE H r.
  invE H a.
  assert (H' := H).
  apply HHHHH in H'. invE H' e'. unf.
  eex.
  unfold phiImplies.
  intros.
  assert (H4' := H4).
  apply HHHHH in H4'. invE H4' e''. unf.
  apply H0 in H.
  apply H0 in H4.
  
  assert (e' = e'').
  Focus 2. subst. eapp evalphiIncl. apply inclEmpty.
  
  
Admitted.


Definition joinExists : forall p1 p2,
  exists p, phiImplies p1 p /\ phiImplies p2 p /\
  forall p', (phiImplies p1 p' /\ phiImplies p2 p') -> phiImplies p p'.
Proof.
  induction p1; intros.
  - exists [].
    split. eapp phiImpliesRefl.
    split. eapp phiImpliesPrefix. eapp phiImpliesRefl.
    intros. unf.
    auto.
  - destruct (classic (exists e f, a = phiAcc e f)).
    * unf. subst.
      admit.
    * destruct (classic (phiImplies p1 [a])).
        specialize (IHp1 p2). unf.
        exists x.
        split.
          unfold phiImplies. intros.
          inversionx H3. eapp H2.
          eapp evalphiAexcept.
        split. auto.
        intros.
        unf.
        eapp H4.
        admit. (* yes *)
      destruct (classic (phiImplies p2 [a])).
        specialize (IHp1 p2). unf.
        exists (a :: x).
        split.
          unfold phiImplies. intros.
          inversionx H4. eca.
        split.
          unfold phiImplies. intros.
          assert (footprint' h r a = []) as fp.
            destruct a; auto. contradict H. eex.
          eca.
            rewrite fp. apply inclEmpty.
            apply H1 in H4. inversionx H4. assumption.
          rewrite fp. common.
          eapp H2.
        intros. unf.
        unfold phiImplies. intros.
        destruct (classic (phiImplies p1 p')).
          eapp H5.
          rewrite cons2app in H4.
          eapp phiImpliesSuffix.
        
        
        inversionx H4.
        split. auto.
        intros. unf.
        eapp H4.
        admit.
Qed.


Theorem supremumWD : forall pp,
  exists p, ppHasSupremum p (pFromList pp).
Proof.
  induction pp.
  - exists [phiFalse].
    unfold ppHasSupremum.
    unfold ppHasUpperBound.
    split.
    * intros.
      inversionx H.
    * unfold phiImplies.
      intros.
      exfalso.
      eapp phiFalseNotSat.
      eex.
  - unfold ppHasSupremum in *.
    unfold ppHasUpperBound in *.
    unf.

Theorem alphaOptimal : forall pp1 gp1 pp2 gp2 pp3,
  gAlpha pp1 gp2 ->
  gGamma gp1 pp2 ->
  gGamma gp2 pp3 ->
  pincl pp1 pp2 ->
  pincl pp3 pp2.
Proof.
  intros.
  inversionx H;
  inversionx H0;
  inversionx H1.
  - unfold
      pincl,
      gGamma',
      ppIsSingleton
    in *.
    simpl. unf.
    intros. subst.
    eapp H2.
  - unfold pincl, gGamma' in *.
    simpl. intros. unf.
    destruct gp1.
    destruct b; simpl in *.
    * unfold
        ppHasSupremum,
        ppIsSingleton
      in *.
      unf.
      split; auto.
      apply (phiImpliesTrans p1 p0 p2); auto.
      eapp H8.
      unfold ppHasUpperBound.
      intros.
      eapp H2.
    * (* contradict *)
      unfold
        pincl,
        ppHasSupremum,
        ppIsSingleton
      in *. unf.
      inversionx H3. unf.
      assert (x = p2). eapp H2. subst.
      specialize (H4 p2). contradict H4.
      split; auto.
  - unfold pincl, gGamma' in *.
    simpl. intros. unf.
    destruct gp1.
    destruct b; simpl in *.
    * (* contradict everything but phi = true *)
      split; auto.
      destruct (classic (phiImplies [] p1)).
        eapp phiImpliesTrans.
      contradict H1.
      clear H0 H7.
      unfold phiImplies. intros. clear H0.
      inversionx H3. unf. clear H1.
      unfold ppIsSingleton in *.
        specialize (H4 x).
        apply not_and_or in H4.
        inversionx H4; try tauto.
        apply not_all_ex_not in H0. unf.
        assert (pp1 x0). eapp not_imply_elim.
        apply not_imply_elim2 in H1.
      unfold ppHasSupremum in H5.
    * (* contradict *)
      unfold
        pincl,
        ppHasSupremum,
        ppIsSingleton
      in *.
      inversionx H3. unf.
      assert (x = p1). eapp H2. subst.
      specialize (H4 p1). contradict H4.
      split; auto.
Qed.


(* disjunciton of phi *)
Definition phid := list phi.

Definition evalphid H r A (pd : phid) :=
  exists p, In p pd /\ evalphi H r A p.

(* helping defs *)
Definition isIntersection (pd1 pd2 pdi : phid) :=
  forall H r A, evalphid H r A pd1 /\ evalphid H r A pd2 <-> evalphid H r A pdi.

Definition splitPhi (p : phi) : prod A_s phi :=
  fold_right
    (fun p pr => 
      match p with
      | phiAcc e f => ((e, f) :: fst pr, snd pr)
      | _ => (fst pr, p :: snd pr)
      end)
    ([], [])
    p.

Lemma splitPhiAlt : forall p,
  splitPhi p = 
    (staticFootprint p, 
     filter (fun p' => match p' with
                         | phiAcc _ _ => false
                         | _ => true
                         end) p).
Proof.
  induction p0; intros; simpl in *; try tauto.
  rewrite IHp0. simpl.
  destruct a; tauto.
Qed.


Definition mergePhi (pa : A_s) (pb : phi) : phi :=
  map (fun p => phiAcc (fst p) (snd p)) pa ++ pb.

(* mapRem *)
Definition isCutAt {T : Type} xs ys1 (y : T) ys2 : Prop := xs = ys1 ++ y :: ys2.

Lemma isCutAtClassic : forall {T : Type} xs ys1 (y : T) ys2,
  isCutAt xs ys1 y ys2 ->
  In y xs /\ incl ys1 xs /\ incl ys2 xs.

Fixpoint mapRem {T U : Type} (f : T -> list T -> U) (xs : list T) :=
  match xs with
  | [] => []
  | x :: xs => f x xs :: mapRem (fun y ys => f y (x :: ys)) xs
  end.

Lemma in_mapRem_iff : forall {T U : Type} y xs (f : T -> list T -> U),
  In y (mapRem f xs) <->
  exists xs1 x xs2, f x (xs1 ++ xs2) = y /\ isCutAt xs xs1 x xs2.
Proof.
  induction xs; intros; simpl in *.
  - split; intros; try tauto.
    unf. inversionx H2.
    destruct x0; discriminate.
  - split; intros.
    * inversionx H0.
      + exists []. exists a. exists xs.
        unfold isCutAt.
        split; tauto.
      + apply IHxs in H1. unf. subst.
        unfold isCutAt in H2. subst.
        exists (a :: x0). exists x1. exists x2.
        unfold isCutAt.
        split; tauto.
    * unf. subst.
      inversionx H2.
      destruct x0; simpl in *.
      + inversionx H1.
        auto.
      + inversionx H1.
        apply or_intror.
        apply IHxs.
        repeat eex.
Qed.

(* meet operation *)
Fixpoint meetSplit (pa1 pa2 : A_s) (pb : phi) : phid :=
  match pa1 with
  | [] => [map (fun p => phiAcc (fst p) (snd p)) pa2 ++ pb]
  | A :: pa1 =>
    map (fun p => phiAcc (fst A) (snd A) :: p)
    (
      meetSplit pa1 pa2 pb
      ++
      concat
      (
        mapRem
        (fun A' pa2 =>
          if f_decb (snd A) (snd A')
          then map (fun p => phiEq (fst A) (fst A') :: p) (meetSplit pa1 pa2 pb)
          else []
        )
        pa2
      )
    )
  end.

Definition meetSingle (p1 p2 : phi) : phid :=
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  meetSplit (fst ps1) (fst ps2) (snd ps1 ++ snd ps2).

Definition meet (pd1 pd2 : phid) : phid :=
  flat_map (fun ps => meetSingle (fst ps) (snd ps)) (list_prod pd1 pd2).

(* 
(*BEGIN test*)
Open Scope string.
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"] [].
Eval compute in meetSingle [] [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"].
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"] [phiAcc (ex (xUserDef "b")) "f"].
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"] [phiAcc (ex (xUserDef "b")) "g"].
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"] [phiAcc (ex (xUserDef "c")) "f"].
Eval compute in meetSingle [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"]
                           [phiAcc (ex (xUserDef "a")) "f"; phiAcc (ex (xUserDef "b")) "f"].
Close Scope string.
(*END test*)
 *)

Lemma evalphiSplitMerge : forall p,
  let ps := splitPhi p in
  forall H r A,
  evalphi H r A p <->
  evalphi H r A (map (λ p, phiAcc (fst p) (snd p)) (fst ps) ++ snd ps)
  .
Proof.
  induction p0; intros; simpl in *; try tauto.
  subst ps.
  split; intros.
  - inversionx H1.
    apply IHp0 in H12.
    destruct a; simpl in *;
    try (apply evalphiSymm;
        rewriteRev app_comm_cons;
        eca; simpl;
        apply evalphiSymm;
        assumption).
    eca.
  - destruct a; simpl in *;
    try (apply evalphiSymm in H1;
        rewriteRevIn app_comm_cons H1;
        inversionx H1;
        eca;
        common;
        apply evalphiSymm in H12;
        eapp IHp0).
    inversionx H1.
    eca.
    eapp IHp0.
Qed.

Lemma evalphidApp : forall H r A p1 p2,
  evalphid H r A (p1 ++ p2) <->
  evalphid H r A p1 \/ evalphid H r A p2.
Proof.
  unfold evalphid. intros.
  split; intros; unf.
  - apply in_app_iff in H1.
    inversionx H1.
    * apply or_introl. eex.
    * apply or_intror. eex.
  - inversionx H1; unf; eex; intuition.
Qed.

Lemma meetSplitAugment1 : forall ps1 ps2 ps p H r A,
  let mc := map (cons (phiAcc (fst p) (snd p))) in
    (evalphid H r A (mc (meetSplit ps1 ps2 ps)) \/
     exists xs1 x xs2, 
      isCutAt ps2 xs1 x xs2 /\ snd p = snd x /\
      evalphid H r A (mc (map (cons (phiEq (fst p) (fst x))) (meetSplit ps1 (xs1 ++ xs2) ps))))
    <->
    (evalphid H r A (meetSplit (p :: ps1) ps2 ps))
   .
Proof.
  split; simpl in *; unfold evalphid in *; intuition; unf; intuition.
  - apply in_map_iff in H2. unf. subst.
    eex.
    apply in_map_iff. eex.
    intuition.
  - apply in_map_iff in H4. unf. subst.
    destruct p0, x1. simpl in *. subst.
    eex.
    apply in_map_iff. eex.
    apply in_app_iff. apply or_intror.
    apply in_concat. eex.
    apply in_mapRem_iff. repeat eex.
    simpl.
    dec (string_dec f1 f1).
    tauto.
  - apply in_map_iff in H1. unf. subst.
    apply in_app_iff in H4.
    inversionx H4.
    * constructor. eex.
      apply in_map_iff. eex.
    * apply in_concat in H1. unf.
      apply in_mapRem_iff in H1. unf. subst.
      destruct p0, x3. simpl in *.
      dec (string_dec f0 s0); try tauto.
      apply in_map_iff in H4. unf. subst.
      apply or_intror. repeat eex.
      apply in_map_iff. eex.
      apply in_map_iff. eex.
Qed.

Lemma meetSplitAugment : forall ps1 ps2 ps p' H r A,
   footprint' H r p' = [] ->
   (
    (evalphid H r A (meetSplit ps1 ps2 ps) /\ evalphi' H r [] p')
    <->
    (evalphid H r A (meetSplit ps1 ps2 (p' :: ps)))
   ).
Proof.
  induction ps1; intros; unf; simpl in *.
  - split; intros; unfold evalphid in *; unf; simpl in *.
    * inversionx H3; try tauto.
      eex.
      apply evalphiSymm. simpl.
      eca; rewrite H1.
      + apply inclEmpty.
      + assumption.
      + apply evalphiSymm.
        common.
        assumption.
    * inversionx H2; try tauto.
      apply evalphiSymm in H4.
      simpl in H4.
      inversionx H4. rewrite H1 in *.
      eex.
      eex.
      apply evalphiSymm in H13.
      common.
      assumption.
  - destruct a. simpl in *.
    split; intros; unfold evalphid in *; unf; simpl in *.
    * apply in_map_iff in H3. unf.
      apply in_app_iff in H6.
      inversionx H6.
      + inversionx H5. inversionx H14. common.
        simpl in *. rewrite H11 in *.
        apply (IHps1 ps2 ps p' H0 r (Aexcept A [(o0, f0)])) in H1. unf.
        lapply H3; intros; eauto.
        unf. exists (phiAcc e0 f0 :: x0).
        split.
          apply in_map_iff. eex. intuition.
        eca; simpl; rewrite H11; auto.
        eca.
      + apply in_concat in H2. unf.
        apply in_mapRem_iff in H2. unf. subst.
        destruct x3. simpl in *.
        dec (string_dec f0 s0); try tauto.
        apply in_map_iff in H6. unf. subst.
        inversionx H5. inversionx H15.
        simpl in *. rewrite H12 in *.
        apply (IHps1 (x2 ++ x4) ps p' H0 r (Aexcept A [(o0, s0)])) in H1. unf.
        lapply H2; intros.
          unf. exists (phiAcc e0 s0 :: phiEq e0 e1 :: x1).
          split.
            apply in_map_iff. eex.
            apply in_app_iff. apply or_intror.
            apply in_concat. eex.
              apply in_mapRem_iff. repeat eex.
              simpl. dec (string_dec s0 s0).
              apply in_map_iff. eex.
            eca; simpl; rewrite H12; auto.
              eca.
            inversionx H16.
            inversionx H21.
            eca; simpl. eca.
            common.
            assumption.
        split; auto.
        eex.
        inversionx H16.
        common.
        assumption.
    * apply in_map_iff in H2. unf. subst.
      apply in_app_iff in H5.
      inversionx H5.
      + inversionx H4.
        inversionx H13.
        simpl in *. rewrite H10 in *.
        apply (IHps1 ps2 ps p' H0 r (Aexcept A [(o0, f0)])) in H1. unf.
        lapply H4; intros; eex; try apply H1.
        unf.
        exists (phiAcc e0 f0 :: x0). split.
          apply in_map_iff. eex.
          intuition.
        eca; simpl; rewrite H10; auto.
        eca.
      + apply in_concat in H2. unf.
        apply in_mapRem_iff in H2. unf. subst.
        destruct x3. simpl in *.
        dec (string_dec f0 s0); try tauto.
        apply in_map_iff in H5. unf. subst.
        inversionx H4. inversionx H14. simpl in *. rewrite H11 in *.
        apply (IHps1 (x2 ++ x4) ps p' H0 r (Aexcept A [(o0, s0)])) in H1. unf.
        lapply H3; intros; unf.
          split; auto.
          exists (phiAcc e0 s0 :: phiEq e0 e1 :: x1).
          split.
            apply in_map_iff. eex.
            apply in_app_iff. apply or_intror.
            apply in_concat. eex.
              apply in_mapRem_iff. repeat eex.
              simpl. dec (string_dec s0 s0).
              apply in_map_iff. eex.
            eca; simpl; rewrite H11; auto.
              eca.
            inversionx H15.
            inversionx H21.
            eca; simpl. eca.
            common.
            assumption.
        eex.
        inversionx H15. common.
        assumption.
Qed.

Lemma InEnsuresCutAt : forall {T : Type} (x : T) p,
  In x p ->
  exists xs1 xs2, isCutAt p xs1 x xs2.
Proof.
  induction p0; intros; simpl in *; try tauto.
  inversionx H0.
  - exists []. exists p0.
    unfold isCutAt.
    tauto.
  - intuition.
    unf.
    exists (a :: x1). exists x2.
    unfold isCutAt in *.
    subst.
    tauto.
Qed.

Lemma fstSplitPhiMergePhi : forall p A,
  fst (splitPhi (mergePhi A (snd (splitPhi p)))) = A.
Proof.
  unfold mergePhi.
  induction p0; induction A; intros; simpl in *.
  - tauto.
  - destruct a. simpl.
    apply f_equal2; auto.
  - specialize (IHp0 []).
    destruct a; simpl in *; auto.
  - destruct a0. simpl.
    apply f_equal2; auto.
Qed.

Lemma sndSplitPhiMergePhi : forall p A,
  snd (splitPhi (mergePhi A (snd (splitPhi p)))) = snd (splitPhi p).
Proof.
  unfold mergePhi.
  induction p0; induction A; intros; simpl in *.
  - tauto.
  - assumption.
  - specialize (IHp0 []).
    destruct a; simpl in *;
    try apply f_equal2; auto.
  - assumption.
Qed.

Lemma evalphiIsCutAt : forall H r A A1 A2 e o f p,
  evale' H r e = Some (vo o) ->
  isCutAt (staticFootprint p) A1 (e, f) A2 ->
  incl [(o, f)] A ->
  evalphi H r A p <->
  evalphi H r (Aexcept A [(o, f)]) (mergePhi (A1 ++ A2) (snd (splitPhi p))).
Proof.
  unfold isCutAt, mergePhi.
  intros.
  rewrite evalphiSplitMerge.
  assert (fst (splitPhi p0) = A1 ++ (e0, f0) :: A2).
    rewrite splitPhiAlt. assumption.
  rewrite H4.
  repeat rewrite map_app.
  set (mm := map (λ p : e * f, phiAcc (fst p) (snd p))).
  assert (
    evalphi H0 r A ((mm A1 ++ mm ((e0, f0) :: A2)) ++ snd (splitPhi p0))
    <->
    evalphi H0 r A ((mm ((e0, f0) :: A2) ++ mm A1) ++ snd (splitPhi p0))
    ) as rw1.
    split; intros;
    apply evalphiApp in H5; unf;
    apply evalphiSymm in H6;
    rewrite footprintApp in H7;
    rewrite Aexcept2AppComm in H7;
    rewriteRevIn footprintApp H7;
    eapp evalphiAppRev.
  assert (
    evalphi H0 r (Aexcept A [(o0, f0)]) ((mm A1 ++ mm A2) ++ snd (splitPhi p0))
    <->
    evalphi H0 r (Aexcept A [(o0, f0)]) ((mm A2 ++ mm A1) ++ snd (splitPhi p0))
    ) as rw2.
    split; intros;
    apply evalphiApp in H5; unf;
    apply evalphiSymm in H6;
    rewrite footprintApp in H7;
    rewrite Aexcept2AppComm in H7;
    rewriteRevIn footprintApp H7;
    eapp evalphiAppRev.
  subst mm.
  rewrite rw1, rw2.
  repeat rewriteRev app_assoc.
  simpl.
  assert (forall p, evalphi H0 r A (phiAcc e0 f0 :: p) <->
                    evalphi H0 r (Aexcept A [(o0, f0)]) p)
  as rw.
    split; intros.
      inversionx H5. inversionx H15. simpl in *. rewrite H12 in *. inversionx H1. assumption.
      eca; simpl; rewrite H1; auto. eca. apply in_eq.
  rewrite rw.
  tauto.
Qed.

Lemma meetSplitWorks : forall p1 p2,
  let ps1 := splitPhi p1 in
  let ps2 := splitPhi p2 in
  forall H r A,
  (evalphi H r A p1 /\ evalphi H r A p2) <->
  (evalphid H r A (meetSplit (fst ps1) (fst ps2) (snd ps1 ++ snd ps2))).
Proof.
  induction p1; intros; simpl in *; unf.
    split; intros; unfold evalphid in *; unf.
      eappIn evalphiSplitMerge H3. subst ps2. eex. intuition.
      split; try constructor. apply InSingle in H1. subst. eapp evalphiSplitMerge.
  destruct (classic (exists e0 f0, a = phiAcc e0 f0)).
  - unf. subst. subst ps1 ps2.
    split; unfold evalphid in *; intros; unf.
    * inversionx H2. inversionx H12. simpl in *. rewrite H9 in *.
      destruct (classic (In (o0, x1) (footprint H0 r p2))) as [fp2 | fp2].
      + apply staticVSdynamicFP in fp2. unf.
        apply InEnsuresCutAt in H4. unf.
          
        assert (evalphi H0 r (Aexcept A [(o0, x1)]) p1 ∧ 
                evalphi H0 r (Aexcept A [(o0, x1)]) (mergePhi (x3 ++ x4) (snd (splitPhi p2)))) as IH.
          split; auto.
          eappIn evalphiIsCutAt H4.
          rewriteRev H4. assumption.
        apply IHp1 in IH. unf.
        exists (phiAcc x0 x1 :: phiEq x0 x2 :: x5).
        split.
          apply in_map_iff. eex.
          apply in_app_iff. apply or_intror.
          apply in_concat.
          exists (map (λ p0, phiEq x0 x2 :: p0) (meetSplit (fst (splitPhi p1)) (x3 ++ x4) (snd (splitPhi p1) ++ snd (splitPhi p2)))).
          split.
            apply in_mapRem_iff.
            exists x3. exists (x2, x1). exists x4.
            split.
              simpl.
              dec (string_dec x1 x1). tauto.
            rewrite splitPhiAlt. assumption.
          apply in_map_iff. eex.
          rewrite fstSplitPhiMergePhi in H5.
          rewrite sndSplitPhiMergePhi in H5.
          assumption.
        eca; simpl; rewrite H9.
          auto.
          eca.
        eca; simpl.
          apply inclEmpty.
          eca.
        common.
        assumption.
      + assert (evalphi H0 r (Aexcept A [(o0, x1)]) p1 ∧ 
                evalphi H0 r (Aexcept A [(o0, x1)]) p2) as IH.
          split; auto. eapp evalphiRemoveAexcept.
          unfold disjoint. intros. apply or_comm. apply imply_to_or. intros. simpl in *.
          inversionx H1; tauto.
        apply IHp1 in IH. unf.
        exists (phiAcc x0 x1 :: x2).
        split.
          apply in_map_iff. eex.
          apply in_app_iff. auto.
        eca; simpl; rewrite H9.
          auto.
          eca.
        assumption.
    * simpl in *.
      rewrite in_map_iff in H1. unf.
      rewrite in_app_iff in H4. inversionx H4.
      + inversionx H3. inversionx H12.
        simpl in *. rewrite H9 in *.
        assert (evalphi H0 r (Aexcept A [(o0, x1)]) p1 ∧ 
                evalphi H0 r (Aexcept A [(o0, x1)]) p2) as IH.
          eapp IHp1.
        unf.
        split.
          eca; simpl; rewrite H9.
            auto.
            eca.
            assumption.
          eapp evalphiAexcept.
      + apply in_concat in H2. unf.
        apply in_mapRem_iff in H2. unf. subst.
        destruct x5. simpl in *.
        dec (string_dec x1 s0).
        apply in_map_iff in H4. unf. subst.
        inversionx H3. inversionx H13.
        simpl in *. rewrite H10 in *.
        inversionx H14. simpl in *. common.
        assert (evalphi H0 r (Aexcept A [(o0, s0)]) p1 ∧ 
                evalphi H0 r (Aexcept A [(o0, s0)]) (mergePhi (x4 ++ x6) (snd (splitPhi p2)))) as IH.
          eapp IHp1.
          eex.
          rewrite fstSplitPhiMergePhi.
          rewrite sndSplitPhiMergePhi.
          assumption.
        unf.
        split.
          eca; simpl; rewrite H10; auto. eca.
          rewrite splitPhiAlt in H5. simpl in *.
          inversionx H16. common. rewrite H10 in *. inversionx H12.
          eappIn evalphiIsCutAt H5.
          rewrite H5. assumption.
  - subst ps1 ps2.
    split; intros.
    * unf. inversionx H3.
      destruct a; simpl in *;
      try (contradict H1; eex; fail);
      rewriteRev meetSplitAugment;
      try tauto;
      split; auto;
      apply IHp1;
      split; common; auto.
    * destruct a; simpl in *;
      try (contradict H1; eex; fail);
      rewriteRevIn meetSplitAugment H2;
      try tauto; unf;
      apply IHp1 in H3; unf;
      split; try tauto;
      eca; simpl; common; auto;
      apply inclEmpty.
Qed.

Theorem meetWorks : forall pd1 pd2,
  isIntersection pd1 pd2 (meet pd1 pd2).
Proof.
  unfold isIntersection, meet, meetSingle, evalphid.
  induction pd1; simpl.
  - split; intros; unf; tauto.
  - split; intros; unf.
    * rewrite flat_map_app.
      inversionx H2.
      + assert (evalphi H0 r A x1 /\ evalphi H0 r A x0) as ss.
          auto.
        apply meetSplitWorks in ss. unfold evalphid in ss. unf.
        exists x2.
        split; auto.
        rewrite in_app_iff. constructor.
        apply in_flat_map.
        exists (x1, x0).
        split; auto.
        rewrite in_map_iff. eex.
      + specialize (IHpd1 pd2 H0 r A).
        inversionx IHpd1.
        lapply H2; intros.
          unf. eex. intuition.
        split; eex.
    * rewrite flat_map_app in H1.
      rewrite in_app_iff in H1.
      inversionx H1.
      + apply in_flat_map in H2. unf.
        apply in_map_iff in H2. unf. subst.
        simpl in *.
        assert (evalphi H0 r A a /\ evalphi H0 r A x2).
          eapp meetSplitWorks.
        unfold evalphid.
        eex. unf.
        split; eex.
      + specialize (IHpd1 pd2 H0 r A).
        inversionx IHpd1.
        lapply H4; intros.
          unf. eex.
        eex.
Qed.
