Load GradVer8LemmaLO.
Import Semantics.

Ltac common :=
  repeat rewrite AexceptEmpty in *;
  unfold neq in *;
  repeat match goal with
    | [ H : option_map _ ?T = _ |- _ ] =>
                        destruct T eqn: ?;
                        inversionx H
    | [ H : evale _ _ _ _ |- _ ] => unfold evale in H; simpl in H
  end.