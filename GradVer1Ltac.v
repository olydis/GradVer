Load GradVer0Defs.

Ltac eax := repeat split; eauto.
Ltac eapp H := eapply H; eax.
Ltac eappIn H t := eapply H in t; eax.
Ltac eex := eexists; eax.
Ltac eca := econstructor; eauto.

Ltac inversionE H :=
  inversion H; clear H.
Ltac inversionx H :=
  inversion H; clear H; subst.

Ltac unf :=
  repeat match goal with
    | [ H : exists _, _ |- _ ] => inversionE H
    | [ H : _ /\ _ |- _ ] => inversionE H
    | [ H : _ <-> _ |- _ ] => inversionE H
  end.

Ltac app_cons h := (* _ :: _ ++ _ *)
  assert (acc := app_comm_cons);
  symmetry in acc;
  rewrite acc in h;
  clear acc.

Ltac des P :=
    destruct P as [de1 | de2];
    try (inversion de1; fail);
    try (contradict de2; tauto; fail);
    try (rewrite de1 in *);
    try (clear de1).
Ltac dec P := undecb; des P.


Ltac rewriteRev R :=
  assert (temp := R);
  symmetry in temp;
  rewrite temp;
  clear temp.

Ltac rewriteRevIn R H :=
  assert (temp := R);
  symmetry in temp;
  rewrite temp in H;
  clear temp.