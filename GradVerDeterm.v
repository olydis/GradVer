Load GradVer20Hook_import.
Import Semantics.

(* DETERM *)

Definition isWithoutX (x : x) (phi : phi) : Prop :=
  forall p, In p phi -> ~ In x (FV' p).
Definition isWithoutAcc (A : A'_s) (phi : phi) : Prop :=
  forall p, In p phi -> ~ In A (staticFootprint' p).
Definition isWithoutAccs (A : A_s) (phi : phi) : Prop :=
  forall p, In p phi -> disjoint A (staticFootprint' p).

Definition withoutX (x : x) (p : phi) : phi :=
  filter (fun p => negb (existsb (x_decb x) (FV' p))) p.
Definition withoutAcc (A : A'_s) (p : phi) : phi :=
  filter (fun p => negb (existsb (A'_s_decb A) (staticFootprint' p))) p.
Definition withoutAccs (A : A_s) (p : phi) : phi :=
  fold_right withoutAcc p A.

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
  