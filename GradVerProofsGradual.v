Load GradVer20Hook_import.
Import Semantics.


Ltac cut := try discriminate; try tauto; auto.
Ltac inv H := inversionx H.
Ltac splau := split; eauto.

Fixpoint is_nodup {T : Type} (eq_decb : T -> T -> bool) (l : list T) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (eq_decb x) xs) && is_nodup eq_decb xs
  end.

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
  cut.
Qed.

Open Scope string_scope.
Definition x2string (x : x) : string :=
  match x with
  | xUserDef x => "1" ++ x
  | xthis => "2"
  | xresult => "3"
  end.
Close Scope string_scope.

(* generic ENV *)
(* 
Definition genericRho : rho := fun x => Some (vo [x2string x]).
Definition genericHeap : H := fun o => Some (EmptyString, 
                             (fun f => Some (vo (f :: o)))).
Definition genericAccess : A_d := [].

no good idea: merge of two objects already needs infinite submerges
 *)

Definition dEnv : Type := prod 
  (prod (prod (list o) (list f)) (list (prod v v)))
  (prod (prod H rho) A_d).

Definition dEnvGetHeap (env : dEnv) : H := fst (fst (snd env)).
Definition dEnvGetRho (env : dEnv) : rho := snd (fst (snd env)).
Definition dEnvGetAccess (env : dEnv) : A_d := snd (snd env).
Definition dEnvGetKnownO (env : dEnv) : list o := fst (fst (fst env)).
Definition dEnvGetKnownF (env : dEnv) : list f := snd (fst (fst env)).
Definition dEnvGetKnownIneq (env : dEnv) : list (prod v v) := snd (fst env).

Ltac dEnvGetUnf :=
  try unfold dEnvGetHeap in *;
  try unfold dEnvGetRho in *;
  try unfold dEnvGetAccess in *;
  try unfold dEnvGetKnownO in *;
  try unfold dEnvGetKnownF in *;
  try unfold dEnvGetKnownIneq in *.

Definition dEnvValidateAccB (A : A_d) : bool :=
  is_nodup A'_d_decb A.

Definition dEnvValidateIneqB (ineq : list (prod v v)) : bool :=
  negb (existsb (fun ineq => v_decb (fst ineq) (snd ineq)) ineq).

Definition dEnvConsistent (env : dEnv) : Prop :=
  (forall o,
  (
  (exists x, dEnvGetRho env x = Some (vo o)) \/
  (exists h, dEnvGetHeap env o = Some h) \/
  (exists o' C fs f, dEnvGetHeap env o' = Some (C, fs) /\ fs f = Some (vo o)) \/
  (exists f, In (o, f) (dEnvGetAccess env))
  ) -> In o (dEnvGetKnownO env)) /\
  (forall f,
  (
  (exists o' C fs o, dEnvGetHeap env o' = Some (C, fs) /\ fs f = Some (vo o)) \/
  (exists o, In (o, f) (dEnvGetAccess env))
  ) -> In f (dEnvGetKnownF env)) /\
  dEnvValidateAccB (dEnvGetAccess env) = true /\
  dEnvValidateIneqB (dEnvGetKnownIneq env) = true.


Ltac or_l := apply or_introl.
Ltac or_r := apply or_intror.
Ltac or1 := try or_l.
Ltac or2 := or_r; try or_l.
Ltac or3 := or_r; or_r; try or_l.
Ltac or4 := or_r; or_r; or_r; try or_l.

Definition dEnvKnownTo (v : v) (env : dEnv) : bool :=
  match v with
  | vo o => existsb (o_decb o) (dEnvGetKnownO env)
  | _ => true
  end.

Definition dEnvNew : dEnv := (([], [], []), (newHeap, newRho, newAccess)).
Lemma dEnvNewConsistent : dEnvConsistent dEnvNew.
Proof.
  split.
    repeat intro.
    inversionx H.
      unf. discriminate.
    inversionx H0.
      unf. discriminate.
    inversionx H.
      unf. discriminate.
    unf.
    tauto.
  split.
    repeat intro.
    inversionx H.
      unf. discriminate.
    unf.
    tauto.
  split.
    auto.
  auto.
Qed.

Definition dEnvEval (e : e) (env : dEnv) : option v :=
  evale' (dEnvGetHeap env) (dEnvGetRho env) e.
Fixpoint dEnvEnsure (e : e) (env : dEnv) : option (prod dEnv v) :=
  match e with
  | ev v => Some (env, ve v)
  | ex x => Some (
            match dEnvGetRho env x with
            | None => let newObj := [x2string x] in
                      (((newObj :: dEnvGetKnownO env, dEnvGetKnownF env, dEnvGetKnownIneq env),
                       (dEnvGetHeap env,
                        fun x' => if x_decb x x'
                                  then Some (vo newObj)
                                  else dEnvGetRho env x',
                        dEnvGetAccess env)),
                        vo newObj)
            | Some v => (env, v)
            end)
  | edot e f => 
      match dEnvEnsure e env with
      | None => None
      | Some (env, v) =>
            match v with
            | vo o => Some (
              match dEnvGetHeap env o with
              | None => 
                let newObj := f :: o in
                (((newObj :: dEnvGetKnownO env, f :: dEnvGetKnownF env, dEnvGetKnownIneq env),
                 (fun o' => if o_decb o o'
                            then Some (EmptyString, fun f' =>
                                 if f_decb f f'
                                 then Some (vo newObj)
                                 else None)
                            else dEnvGetHeap env o',
                  dEnvGetRho env,
                  dEnvGetAccess env)),
                  vo newObj)
              | Some (C, fs) =>
                match fs f with
                | None => let newObj := f :: o in
                          (((newObj :: dEnvGetKnownO env, f :: dEnvGetKnownF env, dEnvGetKnownIneq env),
                           (fun o' => if o_decb o o'
                                      then Some (C, fun f' =>
                                           if f_decb f f'
                                           then Some (vo newObj)
                                           else fs f')
                                      else dEnvGetHeap env o',
                            dEnvGetRho env,
                            dEnvGetAccess env)),
                            vo newObj)
                | Some v => (env, v)
                end
              end)
            | ve _ => None
            end
      end
  end.
  
Lemma dEnvConsistentEvals : forall env' e v,
  dEnvConsistent env' ->
  evale' (dEnvGetHeap env') (dEnvGetRho env') e = Some v ->
  dEnvKnownTo v env' = true.
Proof.
  induction e;
  intros;
  simpl in *.
  - destruct v0; simpl; auto.
    discriminate.
  - destruct env'.
    destruct p0.
    destruct p1.
    destruct p0.
    destruct p1.
    unfold dEnvConsistent in *.
    dEnvGetUnf.
    simpl in *.
    destruct v; simpl; auto.
    apply existsb_exists.
    exists o.
    dec o_dec.
    splau.
    apply H.
    constructor.
    eex.
  - destruct (evale' (dEnvGetHeap env') (dEnvGetRho env') e);
    try discriminate.
    destruct v0; cut.
    destruct v; simpl; auto.
    assert (dEnvKnownTo (vo o) env' = true) as dd.
      apply (IHe (vo o)) in H; auto.
      clear IHe.
    simpl in *.
    apply existsb_exists.
    apply existsb_exists in dd.
    unf.
    exists o0.
    dec o_dec; cut.
    dec o_dec. splau.
    destruct env'.
    destruct p0.
    destruct p1.
    destruct p0.
    destruct p1.
    dEnvGetUnf.
    unfold dEnvConsistent in *.
    simpl in *.
    apply H.
    or3.
    dEnvGetUnf.
    simpl.
    exists x.
    destruct h; cut.
    destruct p0.
    eex.
Qed.

Lemma dEnvEnsureEvals : forall e v env env',
  dEnvEnsure e env = Some (env', v) ->
  dEnvConsistent env ->
  evale' (dEnvGetHeap env') (dEnvGetRho env') e = Some v.
Proof.
  induction e; intros; simpl in *.
  - inversionx H.
    auto.
  - inversionx H.
    destruct (dEnvGetRho env x) eqn: ee.
    * inversionx H2.
      assumption.
    * inversionx H2.
      dEnvGetUnf.
      simpl in *.
      dec (x_dec x x).
      auto.
  - destruct (dEnvEnsure e env) eqn: ee; try discriminate.
    destruct p0.
    apply IHe in ee; auto.
    specialize (IHe v0).
    destruct v0; try discriminate.
    inversionx H.
    destruct (dEnvGetHeap d o) eqn: eeh.
    * destruct p0.
      destruct (o0 f) eqn: eeo; inversionx H2.
      + rewrite ee.
        rewrite eeh.
        simpl.
        assumption.
      + (* unfold dEnvConsistent in H0. *)
        dEnvGetUnf.
        destruct d.
        destruct p0.
        destruct p1.
        destruct p0.
        destruct p1.
        simpl in *.
        set (h' := (λ o' : GradVer20Hook.o,
           if o_decb o o'
           then
            Some
              (c, λ f' : string, if f_decb f f' then Some (vo (f :: o)) else o0 f')
           else h o')) in *.
        assert (forall e o, evale' h  r e = Some (vo o) ->
                            evale' h' r e = Some (vo o)) as eva.
          induction e0; intros; simpl in *; auto.
          destruct (evale' h r e0); try discriminate.
          destruct v; try discriminate.
          lapply (IHe0 o2); intros; auto.
          rewrite H1. clear H1.
          subst h'. simpl.
          destruct (h o2) eqn: htmp; try discriminate.
          destruct p0.
          simpl in *.
          dec (o_dec o o2); simpl; auto.
          rewrite eeh in htmp. inversionx htmp.
          dec (string_dec f f0); auto.
          rewrite eeo in H.
          discriminate.
        apply eva in ee.
        rewrite ee.
        dec (o_dec o o).
        simpl.
        dec (string_dec f f).
        auto.
    * inversionx H2.
      dEnvGetUnf.
      destruct d.
      destruct p0.
      destruct p1.
      destruct p0.
      destruct p1.
      simpl in *.
      set (h' := (λ o' : GradVer20Hook.o,
         if o_decb o o'
         then
          Some
            (EmptyString, λ f' : string, if f_decb f f' then Some (vo (f :: o)) else None)
         else h o')) in *.
      assert (forall e o, evale' h  r e = Some (vo o) ->
                          evale' h' r e = Some (vo o)) as eva.
        induction e0; intros; simpl in *; auto.
        destruct (evale' h r e0); try discriminate.
        destruct v; try discriminate.
        lapply (IHe0 o1); intros; auto.
        rewrite H1. clear H1.
        subst h'. simpl.
        destruct (h o1) eqn: htmp; try discriminate.
        destruct p0.
        simpl in *.
        dec (o_dec o o1); simpl; auto.
        rewrite eeh in htmp.
        discriminate.
      apply eva in ee.
      rewrite ee.
      dec (o_dec o o).
      simpl.
      dec (string_dec f f).
      auto.
Qed.

Lemma dEnvEnsureConsistent : forall env,
  dEnvConsistent env ->
  forall e env' v,
  dEnvEnsure e env = Some (env', v) ->
  dEnvConsistent env'.
Proof.
  intro. intro.
  induction e; intros; simpl in *.
  - inversionx H0.
    assumption.
  - inversionx H0.
    destruct (dEnvGetRho env x);
    inversionx H2; try assumption.
    unfold dEnvConsistent in *.
    destruct env.
    destruct p0.
    destruct p1.
    destruct p0.
    destruct p1.
    dEnvGetUnf.
    simpl in *.
    split.
      intros.
      inversionx H0; unf.
        dec (x_dec x x0). inversionx H0. auto.
        or_r.
        apply H1.
        or1.
        eex.
      or_r.
      apply H0.
      inversionx H1; unf.
        or2.
        eex.
      inversionx H3; unf.
        or3.
        eex.
      or4.
      eex.
    split.
      intros.
      inversionx H0; unf.
        apply H.
        or1.
        eex.
      apply H.
      or2.
      eex.
    split; apply H.
  - destruct (dEnvEnsure e env) eqn: ee; try discriminate.
    destruct p0.
    specialize (IHe d v0).
    assert (dEnvConsistent d) as IH.
      eapp IHe.
      clear IHe.
    destruct d.
    destruct p0.
    destruct p1.
    destruct p0.
    destruct p1.
    dEnvGetUnf.
    simpl in *.
    assert (evale' h r e = Some v0) as eva.
      eappIn dEnvEnsureEvals H.
      dEnvGetUnf. assumption.
    destruct v0; try discriminate.
    assert (In o l0) as ii.
      eappIn dEnvConsistentEvals IH.
      simpl in IH. apply existsb_exists in IH. unf.
      dec o_dec; cut.
    inversionx H0.
    destruct (h o) eqn: hh.
    * destruct p0.
      destruct (o0 f) eqn: ff;
      inversionx H2; auto.
      unfold dEnvConsistent in *.
      inversion IH as [IH1 IH234]; clear IH.
      inversion IH234 as [IH2 IH34]; clear IH234.
      inversion IH34 as [IH3 IH4]; clear IH34.
      dEnvGetUnf.
      simpl in *.
      split.
        intros.
        inversionx H0; unf.
          or_r.
          apply IH1.
          or1.
          eex.
        inversionx H1; unf.
          assert (exists x, h o1 = Some x).
            dec (o_dec o o1); eex.
          or_r.
          apply IH1.
          or2.
          assumption.
        inversionx H3; unf.
          dec (o_dec o x).
            inversionx H3.
            dec (string_dec f x2).
              inversionx H5.
              auto.
            or_r.
            apply IH1.
            or3.
            eex.
          or_r.
          apply IH1.
          or3.
          eex.
        or_r.
        apply IH1.
        or4.
        eex.
      split.
        intros.
        inversionx H0; unf.
          dec (o_dec o x).
            inversionx H0.
            dec (string_dec f f0).
              auto.
            or_r.
            apply IH2.
            or1.
            eex.
          or_r.
          apply IH2.
          or1.
          eex.
        or_r.
        apply IH2.
        or2.
        eex.
      split; auto.
    * inversionx H2.
      unfold dEnvConsistent in *.
      inversion IH as [IH1 IH234]; clear IH.
      inversion IH234 as [IH2 IH34]; clear IH234.
      inversion IH34 as [IH3 IH4]; clear IH34.
      dEnvGetUnf.
      simpl in *.
      split.
        intros.
        inversionx H0; unf.
          or_r.
          apply IH1.
          or1.
          eex.
        inversionx H1; unf.
          destruct x.
          dec (o_dec o o0); auto.
          or_r.
          apply IH1.
          or2.
          eex.
        inversionx H3; unf.
          dec (o_dec o x).
            inversionx H3.
            dec (string_dec f x2); try discriminate.
            inversionx H5.
            auto.
          or_r.
          apply IH1.
          or3.
          eex.
        or_r.
        apply IH1.
        or4.
        eex.
      split.
        intros.
        inversionx H0; unf.
          dec (o_dec o x).
            inversionx H0.
            dec (string_dec f f0).
              auto.
            discriminate.
          or_r.
          apply IH2.
          or1.
          eex.
        or_r.
        apply IH2.
        or2.
        eex.
      split; auto.
Qed.

Definition dEnvMergeObjHeapFields (fs1 fs2 : f -> option v) (fs : list f) : list (prod v v) :=
  flat_map
  (fun f => match fs1 f with
            | None => []
            | Some v1 =>
              match fs2 f with
              | None => []
              | Some v2 => [(v1, v2)]
              end
            end)
  fs.

(* removes o' from dom(heap) *)
Definition dEnvMergeObjHeap (o' : o) (v' : v) (Heap : H) (fsx : list f) : option (prod H (list (prod v v))) :=
  match Heap o' with
  | None => Some (Heap, [])
  | Some (C', fs') =>
      match v' with
      | vo o => let HeapMoveo'TOo : H := fun oo => if o_decb o' oo
                                                   then None
                                                   else
                                                    (if o_decb o oo
                                                     then Some (C', fs')
                                                     else Heap oo)
                in
                match Heap o with
                | None => (* can move Heap o' here *)
                    Some (HeapMoveo'TOo, [])
                | Some (C, fs) => (* merge required *)
                    if C_decb C C'
                    then Some (HeapMoveo'TOo, dEnvMergeObjHeapFields fs' fs fsx)
                    else None (* incompatible types *)
                end
      | ve v => None (* o' has fields BUT now has to be a vex (cannot have fields) *)
      end
  end.

(* remove vo' from codom(heap) *)
Definition dEnvMergeObjHeapC (vo' : v) (v' : v) (Heap : H) : H :=
  fun o => match Heap o with
           | None =>
             None
           | Some (C, fs) =>
             Some (C, fun f => match fs f with
                               | None =>
                                 None
                               | Some v =>
                                 Some (if v_decb vo' v
                                       then v'
                                       else v)
                               end)
           end.


Definition dEnvValidateAcc (A : A_d) : option A_d :=
  if dEnvValidateAccB A
  then Some A
  else None.

Definition dEnvAddAcc (v : v) (f : f) (env : dEnv) : option dEnv :=
  match v with
  | vo o =>
    match dEnvValidateAcc ((o, f) :: dEnvGetAccess env) with
    | None => 
      None
    | Some acc =>
      Some ( fst env
           , ( dEnvGetHeap env
             , dEnvGetRho env
             , acc))
    end
  | _ => None
  end.

Definition dEnvMergeObjAccess (o' : o) (v' : v) (A : A_d) : option A_d :=
  match v' with
  | vo o => dEnvValidateAcc
           (map (fun A => ( if o_decb o' (fst A)
                            then o
                            else (fst A)
                          , snd A)) A)
  | _ => if existsb (fun A => o_decb o' (fst A)) A
         then None
         else Some A
  end.

Definition dEnvValidateIneq (ineq : list (prod v v)) : option (list (prod v v)) :=
  if dEnvValidateIneqB ineq
  then Some ineq
  else None.

Definition dEnvAddIneq (v1 v2 : v) (env : dEnv) : option dEnv :=
  match dEnvValidateIneq ((v1, v2) :: dEnvGetKnownIneq env) with
  | None => 
    None
  | Some ineq =>
    Some ( ( dEnvGetKnownO env
           , dEnvGetKnownF env
           , ineq)
         , snd env)
  end.

(* removes o' from ineq (and checks for inconsistency) *)
Definition dEnvMergeObjIneq  (vo' : v) (v' : v) (ineq : list (prod v v)) : option (list (prod v v)) :=
  let ineq' := map (fun ineq =>
                    ( if v_decb vo' (fst ineq)
                      then v'
                      else (fst ineq)
                    , if v_decb vo' (snd ineq)
                      then v'
                      else (snd ineq)
                    )) ineq in
    dEnvValidateIneq ineq'.

(* removes o' from env *)
Definition dEnvMergeObj (o' : o) (v' : v) (env : dEnv) : option (prod dEnv (list (prod v v))) :=
  let vo' := vo o' in
  match dEnvMergeObjIneq vo' v' (dEnvGetKnownIneq env) with
  | None =>
    None
  | Some ineq =>
    match dEnvMergeObjAccess o' v' (dEnvGetAccess env) with
    | None =>
      None
    | Some A =>
      match dEnvMergeObjHeap o' v' (dEnvMergeObjHeapC vo' v' (dEnvGetHeap env)) (dEnvGetKnownF env) with
      | None =>
        None
      | Some (H', merge) =>
        Some 
        ( ( ( filter (fun o => negb (o_decb o' o)) (dEnvGetKnownO env)
            , dEnvGetKnownF env
            , ineq)
          , ( H'
            , fun x =>
                  match dEnvGetRho env x with
                  | None =>
                    None
                  | Some v =>
                    Some (if v_decb vo' v
                          then v'
                          else v)
                  end
            , A))
        , merge)
      end
    end
  end
.

Definition dEnvMerge (v1 v2 : v) (env : dEnv) : option (prod dEnv (list (prod v v))) :=
  if v_decb v1 v2 
    || negb (dEnvKnownTo v1 env)
    || negb (dEnvKnownTo v2 env)
  then Some (env, [])
  else
   (match v1 with
    | vo o1 => dEnvMergeObj o1 v2 env
    | _ =>
      match v2 with
      | vo o2 => dEnvMergeObj o2 v1 env
      | _ => None   (* two non-object values that are syntactically different *)
      end
    end).

Lemma dEnvMergeObjConsistent : forall env o v merge env',
  dEnvKnownTo v env = true ->
  In o (dEnvGetKnownO env) ->
  vo o <> v ->
  dEnvConsistent env ->
  dEnvMergeObj o v env = Some (env', merge) ->
  dEnvConsistent env'.
Proof.
  intros.
  rename H0 into kno.
  rename H into knv.
  rename H1 into ung.
  rename H2 into cons.
  rename H3 into m.
  unfold dEnvMergeObj in *.
  destruct env.
  destruct p0.
  destruct p1.
  destruct p0.
  destruct p1.
  dEnvGetUnf.
  simpl in *.
  destruct (dEnvMergeObjIneq (vo o) v l) eqn: deIneq;
  try discriminate.
  destruct (dEnvMergeObjAccess o v a) eqn: deAccess;
  try discriminate.
  destruct (dEnvMergeObjHeap o v (dEnvMergeObjHeapC (vo o) v h) l1) eqn: deHeap;
  try discriminate.
  destruct p0.
  inversionx m.
  inversion cons as [IH1 IH234]; clear cons.
  inversion IH234 as [IH2 IH34]; clear IH234.
  inversion IH34 as [IH3 IH4]; clear IH34.
  
  unfold dEnvConsistent in *.
  dEnvGetUnf.
  simpl in *.
  split.
    intros.
    apply filter_In.
    inversionx H; unf.
      destruct (r x) eqn: rx; try discriminate.
      inversionx H.
      destruct v0; try discriminate.
      undecb.
      simpl in *.
      dec (o_dec o o1); simpl in *.
        subst.
        simpl in knv.
        split. 
          apply existsb_exists in knv. unf.
          dec o_dec; cut.
        dec (o_dec o1 o0); auto.
      inversionx H1.
      rename de2 into de.
      dec (o_dec o o0); cut.
      split; auto.
      apply IH1.
      or1.
      eex.
    inversionx H0; unf.
      unfold dEnvMergeObjHeap,
             dEnvMergeObjHeapC in deHeap.
      destruct (h o) eqn: ho.
        destruct p0.
        destruct v; try discriminate.
        destruct (h o2) eqn: ho2.
          destruct p0.
          dec (string_dec c0 c); cut.
          inversionx deHeap.
          dec (o_dec o o0); cut.
          split; auto.
          apply IH1. or2.
          rename de2 into de.
          dec (o_dec o2 o0).
            eex.
          destruct (h o0); cut.
          eex.
        inversionx deHeap.
        dec (o_dec o o0); cut.
        splau.
        rename de2 into de.
        dec (o_dec o2 o0).
          simpl in knv.
          apply existsb_exists in knv. unf.
          dec o_dec; cut.
        apply IH1.
        or2.
        destruct (h o0); cut.
        eex.
      inversionx deHeap.
      dec (o_dec o o0).
        rewrite ho in *.
        cut.
      splau.
      apply IH1.
      or2.
      destruct (h o0); cut.
      eex.
    inversionx H; unf.
      unfold dEnvMergeObjHeap,
             dEnvMergeObjHeapC in deHeap.
      destruct (h o) eqn: ho.
        destruct p0.
        destruct v; try discriminate.
        destruct (h o2) eqn: ho2.
          destruct p0.
          dec (string_dec c0 c); cut.
          inversionx deHeap.
          dec (o_dec o o0); splau.
            dec (o_dec o0 x); cut. rename de2 into de.
            dec (o_dec o2 x).
              inversionx H.
              destruct (o1 x2) eqn: o1x2; cut.
              inv H1.
              destruct v; cut.
              dec (o_dec o0 o4);
              inv H0;
              cut.
            destruct (h x) eqn: hx; cut.
            destruct p0.
            inv H.
            destruct (o4 x2) eqn: o4x2; cut.
            inv H1.
            destruct v; cut.
            rename de2 into de3.
            dec (o_dec o0 o5);
            inv H0;
            cut.
          rename de2 into de.
          dec (o_dec o x); cut.
          rename de2 into de3.
          dec (o_dec o2 x).
            inv H.
            destruct (o1 x2) eqn: o1x2; cut.
            inv H1.
            destruct v; cut.
            simpl in knv.
            apply existsb_exists in knv. unf.
            dec (o_dec x x1); cut.
            dec (o_dec o o4);
            inv H0;
            cut.
            apply IH1.
            or3.
            eex.
          destruct (h x) eqn: hx; cut.
          destruct p0.
          inv H.
          destruct (o4 x2) eqn: o4x2; cut.
          inv H1.
          destruct v; cut.
          rename de2 into de4.
          simpl in knv.
          apply existsb_exists in knv. unf.
          dec (o_dec o2 x1); cut.
          dec (o_dec o o5);
          inv H0;
          cut.
          apply IH1.
          or3.
          eex.
        inv deHeap.
        dec (o_dec o x); cut.
        rename de2 into de.
        dec (o_dec o2 x).
          inv H.
          destruct (o1 x2) eqn: o1x2; cut.
          inv H1.
          destruct v; cut.
          simpl in knv.
          apply existsb_exists in knv. unf.
          dec (o_dec x x1); cut.
          dec (o_dec o o3); inv H0.
            dec (o_dec o3 o0); cut.
          rename de2 into de3.
          dec (o_dec o o0); cut.
          splau.
          apply IH1.
          or3.
          eex.
        destruct (h x) eqn: hx; cut.
        destruct p0.
        inv H.
        destruct (o3 x2) eqn: o3x2; cut.
        inv H1.
        destruct v; cut.
        simpl in knv.
        apply existsb_exists in knv. unf.
        rename de2 into de5.
        dec (o_dec o2 x1); cut.
        dec (o_dec o o4); inv H0.
          dec (o_dec o4 o0); cut.
        rename de2 into de4.
        dec (o_dec o o0); cut.
        splau.
        apply IH1.
        or3.
        eex.
      inv deHeap.
      destruct (h x) eqn: hx; cut.
      destruct p0.
      inv H.
      destruct (o1 x2) eqn: o1x2; cut.
      inv H1.
      destruct v0; cut.
      undecb. simpl in H0.
      dec (o_dec o o2); inv H0; simpl in *.
        subst.
        simpl in knv.
        apply existsb_exists in knv. unf.
        dec (o_dec o0 x1); cut.
        dec (o_dec o2 x1); cut.
      rename de2 into de.
      dec (o_dec o o0); cut.
      splau.
      apply IH1.
      or3.
      eex.
    unfold dEnvMergeObjAccess in deAccess.
    destruct v.
      destruct (existsb (λ A, o_decb o (fst A)) a) eqn: ee; cut.
      inv deAccess.
      dec (o_dec o o0).
        contradict ee.
        apply not_false_iff_true.
        apply existsb_exists.
        eex.
        simpl.
        dec (o_dec o0 o0); cut.
      splau.
      apply IH1. or4. eex.
    inv deAccess.
    unfold dEnvValidateAcc in *.
    destruct (dEnvValidateAccB _) in H1; cut.
    inv H1.
    apply in_map_iff in H. unf.
    inv H.
    destruct x0. simpl.
    simpl in knv.
    apply existsb_exists in knv. unf.
    dec (o_dec o1 x); cut.
    dec (o_dec o o0).
      dec (o_dec o0 x); cut.
    rename de2 into de.
    dec (o_dec o o0); cut.
    splau.
    apply IH1. or4. eex.
  split.
    intros.
    inv H; unf.
      apply IH2. or1.
      unfold dEnvMergeObjHeap,
             dEnvMergeObjHeapC in deHeap.
      destruct (h o) eqn: ho.
        destruct p0.
        destruct v; cut.
        destruct (h o1) eqn: ho1.
          destruct p0.
          dec (string_dec c0 c); cut.
          inv deHeap.
          dec (o_dec o x); cut.
          inv H.
          rename de2 into de.
          dec (o_dec o1 x).
            inv H2.
            destruct (o0 f) eqn: o1f; cut.
            inv H1.
            destruct v; cut.
            eex.
          destruct (h x) eqn: hx; cut.
          destruct p0.
          inv H2.
          destruct (o3 f) eqn: o3f; cut.
          inv H1.
          destruct v; cut.
          eex.
        inv deHeap.
        dec (o_dec o x); cut.
        rename de2 into de.
        dec (o_dec o1 x).
          inv H.
          destruct (o0 f) eqn: o0f; cut.
          inv H1.
          destruct v; cut.
          eex.
        destruct (h x) eqn: hx; cut.
        destruct p0.
        inv H.
        destruct (o2 f) eqn: o2f; cut.
        inv H1.
        destruct v; cut.
        eex.
      inv deHeap.
      destruct (h x) eqn: hx; cut.
      destruct p0.
      inv H.
      destruct (o0 f) eqn: o0f; cut.
      inv H1.
      destruct v0; cut.
      eex.
    apply IH2.
    or2.
    unfold dEnvMergeObjAccess in deAccess.
    destruct v.
      destruct (existsb (λ A, o_decb o (fst A)) a) eqn: ee; cut.
      inv deAccess.
      eex.
    inv deAccess.
    unfold dEnvValidateAcc in H1.
    destruct dEnvValidateAccB in H1; cut.
    inv H1.
    apply in_map_iff in H. unf.
    inv H.
    destruct x0. simpl.
    eex.
  split.
    unfold dEnvMergeObjAccess in deAccess.
    unfold dEnvValidateAcc in *.
    unfold dEnvValidateAccB in *.
    destruct v.
      destruct existsb; cut.
      inv deAccess.
      assumption.
    destruct (is_nodup _ _) eqn: ii; cut.
    inv deAccess.
    assumption.
  unfold dEnvMergeObjIneq in deIneq.
  unfold dEnvValidateIneq in *.
  unfold dEnvValidateIneqB in *.
  destruct (negb _) eqn: ii; cut.
  inv deIneq.
  assumption.
Qed.

SearchAbout dEnvKnownTo.
Lemma dEnvMergeObjMergeKnown : forall env o v merge env',
  dEnvKnownTo v env = true ->
  In o (dEnvGetKnownO env) ->
  vo o <> v ->
  dEnvConsistent env ->
  dEnvMergeObj o v env = Some (env', merge) ->
  forall v1 v2, In (v1, v2) merge ->
    dEnvKnownTo v1 env = true /\
    dEnvKnownTo v2 env = true /\
    dEnvKnownTo v1 env' = true /\
    dEnvKnownTo v2 env' = true.
Proof.
  intros.
  rename H0 into kno.
  rename H into knv.
  rename H1 into ung.
  rename H2 into cons.
  rename H3 into m.
  assert (dEnvConsistent env') as cons'.
    apply dEnvMergeObjConsistent in m; auto.
  unfold dEnvMergeObj in *.
  destruct env.
  destruct p0.
  destruct p1.
  destruct p0.
  destruct p1.
  destruct env'.
  destruct p0.
  destruct p1.
  destruct p0.
  destruct p1.
  dEnvGetUnf.
  simpl in *.
  destruct (dEnvMergeObjIneq (vo o) v l) eqn: deIneq;
  try discriminate.
  destruct (dEnvMergeObjAccess o v a) eqn: deAccess;
  try discriminate.
  destruct (dEnvMergeObjHeap o v (dEnvMergeObjHeapC (vo o) v h) l1) eqn: deHeap;
  try discriminate.
  destruct p0.
  inversionx m.
  inversion cons as [IH1 IH234]; clear cons.
  inversion IH234 as [IH2 IH34]; clear IH234.
  inversion IH34 as [IH3 IH4]; clear IH34.
  (* inversion cons' as [IH1' IH234']; clear cons'.
  inversion IH234' as [IH2' IH34']; clear IH234'.
  inversion IH34' as [IH3' IH4']; clear IH34'. *)
  dEnvGetUnf.
  simpl in *.
  
  
  unfold dEnvMergeObjHeap,
         dEnvMergeObjHeapC in deHeap.
  destruct (h o) eqn: ho.
  - destruct p0.
    destruct v; cut.
    destruct (h o1) eqn: ho1.
    * destruct p0.
      dec (string_dec c0 c); cut.
      inv deHeap.
      unfold dEnvMergeObjHeapFields in *.
      apply in_flat_map in H4. unf.
      destruct (o0 x) eqn: o0x; cut.
      destruct (o2 x) eqn: o2x; cut.
      apply InSingle in H1.
      inv H1.
      split.
        destruct v. constructor.
        dec (o_dec o o3); cut.
        simpl.
        apply existsb_exists. exists o3. rename de2 into de. dec o_dec. splau.
        apply IH1.
        or3.
        eex.
      split.
        destruct v0. constructor.
        dec (o_dec o o3); cut.
        simpl.
        apply existsb_exists. exists o3. rename de2 into de. dec o_dec. splau.
        apply IH1.
        or3.
        eex.
      split.
        destruct v. constructor.
        dec (o_dec o o3); simpl;
        dEnvGetUnf; simpl;
        apply existsb_exists.
          exists o1. dec o_dec. splau.
          apply filter_In.
          dec (o_dec o3 o1); cut.
          splau.
        rename de2 into de.
        exists o3. dec o_dec. splau.
        apply filter_In.
        dec (o_dec o o3); cut.
        splau.
        apply IH1.
        or3. eex.
      destruct v0. constructor.
      dec (o_dec o o3); simpl;
      dEnvGetUnf; simpl;
      apply existsb_exists.
        exists o1. dec o_dec. splau.
        apply filter_In.
        dec (o_dec o3 o1); cut.
        splau.
      rename de2 into de.
      exists o3. dec o_dec. splau.
      apply filter_In.
      dec (o_dec o o3); cut.
      splau.
      apply IH1.
      or3. eex.
    * inv deHeap.
      tauto.
  - inv deHeap.
    tauto.
Qed.


Lemma dEnvMergeConsistent : forall env v1 v2 merge env',
  dEnvConsistent env ->
  dEnvMerge v1 v2 env = Some (env', merge) ->
  dEnvConsistent env'.
Proof.
  intros.
  unfold dEnvMerge in *.
  dec (v_dec v1 v2). inv H0. assumption.
  rename de2 into de.
  destruct (negb (_ v1 _)) eqn: dek1.
    inv H0. assumption.
  destruct (negb (_ v2 _)) eqn: dek2.
    inv H0. assumption.
  apply negb_false_iff in dek1.
  apply negb_false_iff in dek2.
  destruct v1, v2; simpl in *; cut;
  eapply dEnvMergeObjConsistent in H0; cut.
  - apply existsb_exists in dek2. unf.
    dec o_dec; cut.
  - apply existsb_exists in dek1. unf.
    dec o_dec; cut.
  - apply existsb_exists in dek1. unf.
    dec o_dec; cut.
Qed.

Lemma dEnvMergeMergeKnown : forall env v1 v2 merge env',
  dEnvConsistent env ->
  dEnvMerge v1 v2 env = Some (env', merge) ->
  forall v1 v2, In (v1, v2) merge ->
    dEnvKnownTo v1 env' = true /\
    dEnvKnownTo v2 env' = true.
Proof.
  intros.
  unfold dEnvMerge in *.
  dec (v_dec v1 v2). inv H0. tauto.
  rename de2 into de.
  destruct (negb (_ v1 _)) eqn: dek1.
    inv H0. tauto.
  destruct (negb (_ v2 _)) eqn: dek2.
    inv H0. tauto.
  apply negb_false_iff in dek1.
  apply negb_false_iff in dek2.
  destruct v1, v2; simpl in *; cut;
  eapply dEnvMergeObjMergeKnown in H0; eauto; cut.
  - apply existsb_exists in dek2. unf.
    dec o_dec; cut.
  - apply existsb_exists in dek1. unf.
    dec o_dec; cut.
  - apply existsb_exists in dek1. unf.
    dec o_dec; cut.
Qed.

Fixpoint dEnvMergeRec' (v1 v2 : v) (env : dEnv) (n : nat) : option dEnv :=
  match n with
  | 0 => None (* unreachable, if called via dEnvMergeRec *)
  | Datatypes.S n =>
    match dEnvMerge v1 v2 env with
    | None => None
    | Some (env', todo) =>
      fold_right
        (fun eq env =>
          match env with
          | None => None
          | Some env => dEnvMergeRec' (fst eq) (snd eq) env n
          end)
        (Some env')
        todo
    end
  end.

Definition dEnvMergeRec (v1 v2 : v) (env : dEnv) : option dEnv :=
  dEnvMergeRec' v1 v2 env (Datatypes.S (length (dEnvGetKnownO env))).

Lemma dEnvMergeRec'Consistent : forall n env v1 v2 env',
  dEnvConsistent env ->
  dEnvMergeRec' v1 v2 env n = Some env' ->
  dEnvConsistent env'.
Proof.
  induction n;
  intros; cut.
  simpl in *.
  destruct dEnvMerge eqn: ee; cut.
  destruct p0.
  apply dEnvMergeConsistent in ee; auto.
  clear env H.
  generalize l d env' H0 ee. clear l d env' H0 ee.
  induction l; intros. inv H0. assumption.
  simpl in *.
  destruct a.
  specialize (IHl d).
  destruct fold_right; cut.
  simpl in *.
  apply (IHl d0) in ee; auto.
  apply IHn in H0; auto.
Qed.

Lemma dEnvMergeRecConsistent : forall env v1 v2 env',
  dEnvConsistent env ->
  dEnvMergeRec v1 v2 env = Some env' ->
  dEnvConsistent env'.
Proof.
  intros.
  unfold dEnvMergeRec in *.
  eapply dEnvMergeRec'Consistent; eauto.
Qed.

Lemma filter_lt : forall {T:Type} f (l : list T),
  length (filter f l) <= length l.
Proof.
  induction l; cut.
  simpl.
  destruct (f a); cut.
  simpl.
  auto with arith.
Qed.

(* orderly termination proof *)
Lemma dEnvMergeObjReduces : forall o v env env' todo,
  dEnvKnownTo v env = true ->
  In o (dEnvGetKnownO env) ->
  vo o <> v ->
  dEnvMergeObj o v env = Some (env', todo) ->
  length (dEnvGetKnownO env') < length (dEnvGetKnownO env).
Proof.
  intros.
  rename H0 into kno.
  rename H into knv.
  rename H1 into ung.
  rename H2 into m.
  unfold dEnvMergeObj in *.
  destruct env.
  destruct p0.
  destruct p1.
  destruct p0.
  destruct p1.
  dEnvGetUnf.
  simpl in *.
  destruct (dEnvMergeObjIneq (vo o) v l) eqn: deIneq;
  try discriminate.
  destruct (dEnvMergeObjAccess o v a) eqn: deAccess;
  try discriminate.
  destruct (dEnvMergeObjHeap o v (dEnvMergeObjHeapC (vo o) v h) l1) eqn: deHeap;
  try discriminate.
  destruct p0.
  inversionx m.
  simpl.
  generalize l0 kno. clear.
  induction l0; intros; inv kno; simpl.
  - dec (o_dec o o).
    simpl.
    unfold lt.
    apply le_n_S.
    apply filter_lt.
  - apply IHl0 in H.
    dec (o_dec o a); simpl; cut.
    auto with arith.
Qed.

Lemma dEnvMergeReduces : forall v1 v2 env env' todo,
  dEnvMerge v1 v2 env = Some (env', todo) ->
  todo = [] \/
  length (dEnvGetKnownO env') < length (dEnvGetKnownO env).
Proof.
  intros.
  unfold dEnvMerge in *.
  dec (v_dec v1 v2).
    inv H.
    auto.
  rename de2 into de.
  destruct (negb (_ v1 _)) eqn: dek1.
    inv H. tauto.
  destruct (negb (_ v2 _)) eqn: dek2.
    inv H. tauto.
  apply negb_false_iff in dek1.
  apply negb_false_iff in dek2.
  or2.
  simpl in *.
  unfold dEnvKnownTo in *.
  destruct v1, v2; cut;
  eappIn dEnvMergeObjReduces H.
  - apply existsb_exists in dek2. unf.
    dec o_dec; cut.
  - apply existsb_exists in dek1. unf.
    dec o_dec; cut.
  - apply existsb_exists in dek1. unf.
    dec o_dec; cut.
Qed.

Lemma dEnvMergeRec'Works : forall n e1 e2 v1 v2 env env',
  let v := match v1 with
           | vo _ => v2
           | _ => v1
           end in
  dEnvConsistent env ->
  dEnvMergeRec' v1 v2 env n = Some env' ->
  dEnvEval e1 env = Some v1 ->
  dEnvEval e2 env = Some v2 ->
  dEnvEval e1 env' = Some v /\
  dEnvEval e2 env' = Some v.
Proof.
  admit.
Admitted.
  
Lemma dEnvMergeRecWorks : forall e1 e2 v1 v2 env env',
  let v := match v1 with
           | vo _ => v2
           | _ => v1
           end in
  dEnvConsistent env ->
  dEnvMergeRec v1 v2 env = Some env' ->
  dEnvEval e1 env = Some v1 ->
  dEnvEval e2 env = Some v2 ->
  dEnvEval e1 env' = Some v /\
  dEnvEval e2 env' = Some v.
Proof.
  intros.
  unfold dEnvMergeRec in *.
  eapply dEnvMergeRec'Works; eauto.
Qed.

Definition dEnvAddPhi' (p : phi') (env : dEnv) : option dEnv :=
  match p with
  | phiTrue => Some env
  | phiEq e1 e2 =>
      match dEnvEnsure e1 env with
      | None => None
      | Some (env, v1) => 
        match dEnvEnsure e2 env with
        | None => None
        | Some (env, v2) => dEnvMergeRec v1 v2 env
        end
      end
  | phiNeq e1 e2 =>
      match dEnvEnsure e1 env with
      | None => None
      | Some (env, v1) => 
        match dEnvEnsure e2 env with
        | None => None
        | Some (env, v2) => dEnvAddIneq v1 v2 env
        end
      end
  | phiAcc e f =>
      match dEnvEnsure e env with
      | Some (env, v) => dEnvAddAcc v f env
      | _ => None
      end
  end.

Definition dEnvFromPhi (p : phi) : option dEnv :=
  fold_right (fun p env => 
              match env with
              | None => None
              | Some env => dEnvAddPhi' p env
              end) (Some dEnvNew) p.

Definition dEnvEvalPhi' (p : phi') (env : dEnv) : Prop :=
  evalphi'
    (dEnvGetHeap env)
    (dEnvGetRho env)
    (dEnvGetAccess env)
    p.

Definition dEnvEvalPhi (p : phi) (env : dEnv) : Prop :=
  evalphi
    (dEnvGetHeap env)
    (dEnvGetRho env)
    (dEnvGetAccess env)
    p.

Lemma dEnvAddIneqConsistent : ∀ env v1 v2 env',
       dEnvConsistent env ->
       dEnvAddIneq v1 v2 env = Some env' ->
       dEnvConsistent env'.
Proof.
  intros.
  simpl.

Lemma dEnvAddPhi'Consistent : forall p env env',
  dEnvConsistent env ->
  dEnvAddPhi' p env = Some env' ->
  dEnvConsistent env'.
Proof.
  intros.
  destruct p0; simpl in *.
  - inv H0.
    assumption.
  - destruct (dEnvEnsure e env) eqn: ee1; cut.
    destruct p0.
    destruct (dEnvEnsure e0 d) eqn: ee2; cut.
    destruct p0.
    eapply dEnvEnsureConsistent in ee1; eauto.
    eapply dEnvEnsureConsistent in ee2; eauto.
    eapply dEnvMergeRecConsistent in H0; eauto.
  - destruct (dEnvEnsure e env) eqn: ee1; cut.
    destruct p0.
    destruct (dEnvEnsure e0 d) eqn: ee2; cut.
    destruct p0.
    eapply dEnvEnsureConsistent in ee1; eauto.
    eapply dEnvEnsureConsistent in ee2; eauto.
    eapply dEnvMergeRecConsistent in H0; eauto.

Lemma dEnvAddPhi'Works : forall p env env',
  dEnvConsistent env ->
  dEnvAddPhi' p env = Some env' ->
  dEnvEvalPhi' p env'.
Proof.
  intros.
  destruct p0; simpl in *.
  - eca.
  - destruct (dEnvEnsure e env) eqn: ee1; cut.
    destruct p0.
    destruct (dEnvEnsure e0 d) eqn: ee2; cut.
    destruct p0.
    Check dEnvMergeRecWorks.
    






















Fixpoint eSubste (eq : prod e e) (e' : e) : e :=
	  if e_dec e' (fst eq)
	  then (snd eq)
	  else match e' with
	       | edot e f => edot (eSubste eq e) f
	       | _ => e'
	       end.

Lemma eSubstseEval : forall H r e a b,
  evale' H r a = evale' H r b ->
  evale' H r (eSubste (a, b) e) = evale' H r e.
Proof.
  induction e; intros;
  unfold eSubste;
  fold eSubste.
  - dec (e_dec (ev v) (fst (a, b)));
    auto.
  - dec (e_dec (ex x) (fst (a, b)));
    auto.
  - dec (e_dec (edot e f) (fst (a, b)));
    auto.
    apply IHe in H0.
    simpl.
    rewrite H0.
    auto.
Qed.

Definition eSubstsEnum (e1 e2 : e) (e' : e) : list e :=
  [ e'
  ; eSubste (e1, e2) e'
  ; eSubste (e2, e1) e'
  ].

Lemma eSubstsEnumEval : forall H r e a b,
  evale' H r a = evale' H r b ->
  forall e', In e' (eSubstsEnum a b e) ->
  evale' H r e' = evale' H r e.
Proof.
  intros.
  unfold eSubstsEnum in *.
  inversionx H1; auto.
  inversionx H2; try eapp eSubstseEval.
  inversionx H1; try eapp eSubstseEval.
  inversionx H2.
Qed.

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

Lemma in_list_prod : forall {T : Type} (a b : T) aa bb,
  In (a, b) (list_prod aa bb) <->
  In a aa /\ In b bb.
Proof.
  induction aa;
  intros;
  simpl in *.
  - tauto.
  - split; intros.
    * apply in_app_iff in H.
      inversionx H.
      + apply in_map_iff in H0. unf.
        inversionx H0.
        auto.
      + apply IHaa in H0.
        unf.
        auto.
    * unf.
      apply in_app_iff.
      rewrite IHaa.
      inversionx H0; auto.
      constructor.
      apply in_map_iff.
      eex.
Qed.


Lemma phi'SubstsEnumFP : forall H r p a b,
  evale' H r a = evale' H r b ->
  forall p', In p' (phi'SubstsEnum a b p) ->
  footprint' H r p' = footprint' H r p.
Proof.
  intros.
  destruct p0;
  unfold phi'SubstsEnum in *.
  - inversionx H1; tauto.
  - apply in_map_iff in H1. unf. subst.
    tauto.
  - apply in_map_iff in H1. unf. subst.
    tauto.
  - apply in_map_iff in H1. unf. subst.
    eappIn eSubstsEnumEval H3.
    simpl.
    rewrite H3.
    tauto.
Qed.

Lemma phi'SubstsEnumEval : forall H r A p a b,
  evale' H r a = evale' H r b ->
  forall p', In p' (phi'SubstsEnum a b p) ->
  evalphi' H r A p' <-> evalphi' H r A p.
Proof.
  intros.
  destruct p0;
  unfold phi'SubstsEnum in *.
  - inversionx H1; tauto.
  - apply in_map_iff in H1. unf. subst.
    destruct x. simpl.
    apply in_list_prod in H3. unf.
    eappIn eSubstsEnumEval H1;
    eappIn eSubstsEnumEval H2;
    intro;
    inversionx H3; eca;
    unfold evale in *;
    try rewrite H1 in *;
    try rewrite H2 in *;
    eauto.
  - apply in_map_iff in H1. unf. subst.
    destruct x. simpl.
    apply in_list_prod in H3. unf.
    eappIn eSubstsEnumEval H1;
    eappIn eSubstsEnumEval H2;
    intro;
    inversionx H3; eca;
    unfold evale in *;
    try rewrite H1 in *;
    try rewrite H2 in *;
    eauto.
  - apply in_map_iff in H1. unf. subst.
    eappIn eSubstsEnumEval H3;
    intro;
    inversionx H1; eca;
    unfold evale in *;
    try rewrite H3 in *;
    eauto.
Qed.

Fixpoint phiSubstsEnum (a b : e) (p : phi) : list phi :=
  match p with
  | [] => [[]]
  | p :: ps => flat_map (fun ps => map (fun p => p :: ps) 
                                  (phi'SubstsEnum a b p))
                        (phiSubstsEnum a b ps)
  end.


Lemma phiSubstsEnumFP : forall H r p a b,
  evale' H r a = evale' H r b ->
  forall p', In p' (phiSubstsEnum a b p) ->
  footprint H r p' = footprint H r p.
Proof.
  induction p0;
  intros;
  simpl in *.
  - inversionx H1; tauto.
  - apply in_flat_map in H1. unf.
    apply in_map_iff in H3. unf. subst.
    apply IHp0 in H1; auto.
    eappIn phi'SubstsEnumFP H4.
    simpl.
    rewrite H1, H4.
    tauto.
Qed.

Lemma phiSubstsEnumEval : forall H r A p a b,
  evale' H r a = evale' H r b ->
  forall p', In p' (phiSubstsEnum a b p) ->
  evalphi H r A p' <-> evalphi H r A p.
Proof.
  induction p0;
  intros.
  - inversionx H1;
    tauto.
  - simpl in *.
    apply in_flat_map in H1. unf.
    apply in_map_iff in H3. unf.
    subst.
    assert (footprint' H r x0 = footprint' H r a) as fp'Eq.
      eappIn phi'SubstsEnumFP H0.
    assert (footprint H r x = footprint H r p0) as fpEq.
      eappIn phiSubstsEnumFP H0.
    eapply phi'SubstsEnumEval in H4; eauto.
    eapply IHp0 in H1; eauto.
    rewrite (cons2app x0).
    rewrite (cons2app a).
    split; intros;
    apply evalphiSymm in H2;
    apply evalphiSymm;
    eappIn evalphiApp H2; inversionx H2;
    eapp evalphiAppRev;
    try eapp H1;
    inversionx H5; eca;
    try rewrite fp'Eq in *;
    try rewrite fpEq in *;
    auto;
    eapp H4.
Qed.


Definition eSubstsEnumContainsOrig : forall p e1 e2,
  In p (eSubstsEnum e1 e2 p).
Proof.
  unfold eSubstsEnum.
  intros.
  apply in_eq.
Qed.
Definition phi'SubstsEnumContainsOrig : forall p e1 e2,
  In p (phi'SubstsEnum e1 e2 p).
Proof.
  unfold phi'SubstsEnum.
  intros.
  destruct p0.
  - apply in_eq.
  - apply in_map_iff.
    exists (e, e0).
    split; auto.
    apply in_list_prod.
    split; apply eSubstsEnumContainsOrig.
  - apply in_map_iff.
    exists (e, e0).
    split; auto.
    apply in_list_prod.
    split; apply eSubstsEnumContainsOrig.
  - apply in_map_iff.
    eex.
    apply eSubstsEnumContainsOrig.
Qed.
Definition phiSubstsEnumContainsOrig : forall p e1 e2,
  In p (phiSubstsEnum e1 e2 p).
Proof.
  induction p0; intros; simpl; auto.
  apply in_flat_map. exists p0.
  split. apply IHp0.
  apply in_map_iff.
  eex.
  apply phi'SubstsEnumContainsOrig.
Qed.

Definition phiSubstsEnumImplies : forall p e1 e2,
  forall p',
  In p' (phiSubstsEnum e1 e2 p) ->
  phiImplies (phiEq e1 e2 :: p) p'.
Proof.
  unfold phiImplies.
  intros.
  inversionx H0.
  eappIn phiSubstsEnumEval H.
    eapp H. eapp evalphiAexcept.
  inversionx H10.
  rewrite H3, H8.
  auto.
Qed.

Definition phiSubstsEnumImpliesBack : forall p e1 e2,
  exists p',
  In p' (phiSubstsEnum e1 e2 p) /\
  phiImplies p' p.
Proof.
  unfold phiImplies.
  intros.
  exists p0.
  split. apply phiSubstsEnumContainsOrig.
  tauto.
Qed.

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

(* wrong!
Case:
a = x * x = b
\/
a = y * y = b
->
a = b
 *)
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

Fixpoint exprse (p : e) : list e :=
  p :: match p with
       | edot e _ => exprse e
       | _ => []
       end.

Definition exprsphi' (p : phi') : list e :=
  match p with
  | phiTrue => []
  | phiEq e1 e2 => exprse e1 ++ exprse e2
  | phiNeq e1 e2 => exprse e1 ++ exprse e2
  | phiAcc e _ => exprse e
  end.

Definition exprsphi (p : phi) : list e :=
  flat_map exprsphi' p.

(* Definition phiImpliesConsEqRemove : forall e1 e2 p1 p2,
  ~ In e1 (exprsphi p1) ->
  ~ In e1 (exprsphi p2) ->
  phiImplies (phiEq e1 e2 :: p1) p2 ->
  phiImplies p1 p2.
Proof.
  induction p2; intros.
    eapp phiImpliesPrefix. 
    eapp phiImpliesRefl.
  simpl in *.
  rewrite in_app_iff in H0.
  apply not_or_and in H0. unf.
  eappIn IHp2 H3.
  Focus 2.
    eapp phiImpliesTrans.
    rewrite cons2app.
    eapp phiImpliesSuffix.
  unfold phiImplies. intros. *)
  
(*   wrong 

a.f.x = b.g.y * a.f = c * b.g = d * d.y = 3  => c.x = 3
                a.f = c * b.g = d * d.y = 3 !=> c.x = 3

=> need ORDER!

*)
  

Definition phiImpliesConsEq : forall p p' e1 e2,
  phiSatisfiable (phiEq e1 e2 :: p) ->
  phiImplies (phiEq e1 e2 :: p) p'
  -> 
  exists px,
  In px (phiSubstsEnum e1 e2 p') /\
  phiImplies p px.
Proof.
  intros.
  Check phiSubstsEnumImpliesBack.
  assert (forall px,
      In px (phiSubstsEnum e1 e2 p') ->
      phiImplies (phiEq e1 e2 :: p0) px).
    unfold phiImplies.
    intros.
    eappIn phiSubstsEnumEval H1.
      eapp H1.
    inversionx H2. inversionx H12.
    rewrite H5, H10.
    auto.

  induction p'; intros; simpl in *.
    eex.
    eapp phiImpliesPrefix. eapp phiImpliesRefl.
  assert (phiImplies (phiEq e1 e2 :: p0) p') as IH.
    eapp phiImpliesTrans.
    rewrite cons2app. eapp phiImpliesSuffix.
  apply IHp' in IH; auto.
  invE IH px. unf.
  assert (forall H r A,
      evale' H r e1 = evale' H r e2 ->
      evalphi H r A px <-> evalphi H r A p') as eph.
    intros.
    eappIn phiSubstsEnumEval H4; inversionx H4;
    eauto.
  clear H1.

  
  
  
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
