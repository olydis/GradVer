Ltac inversionE H :=
  inversion H; clear H.
Ltac inversionx H :=
  inversion H; clear H; subst.

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