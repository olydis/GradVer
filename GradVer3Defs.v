Load GradVer2LemmaIndependent.
Import Semantics.

Definition phiSatisfiable (p : phi) := exists H r A, evalphi H r A p.


(*GRADUAL*)
Definition gphi := prod bool phi.
Definition pphi := phi -> Prop.

Definition gphiSatisfiable (gp : gphi) := phiSatisfiable (snd gp).

Definition gUnknown : gphi := (true, []).
Definition gThat (p : phi) : gphi := (false, p).
Definition gThatOrSub (p : phi) : gphi := (true, p).

Definition pFromList (ps : list phi) := fun p => In p ps.

Definition pincl (pp1 pp2 : pphi) :=
  forall p, pp1 p -> pp2 p.

Definition evalgphi H r A (gp : gphi) := evalphi H r A (snd gp).
Definition evalpphi H r A (pp : pphi) := exists p, pp p /\ evalphi H r A p.

(* concretization *)
Definition gGamma (phi : gphi) : pphi :=
  match fst phi with
  | false => (fun p => p = snd phi)
  | true => (fun p => phiSatisfiable p /\ sfrmphi [] p /\ phiImplies p (snd phi))
  end.

(*
(* abstraction *)
Definition gAbstr (pp : list phi) : gphi :=
  fold_right join gUnknown (map gThat pp). *)

Definition PLIFT1 (prop : phi -> Prop) : (pphi -> Prop) :=
  fun pp => exists p', pp p' /\ prop p'.

Definition GLIFT1 (prop : phi -> Prop) : (gphi -> Prop) :=
  fun gp => PLIFT1 prop (gGamma gp).

Definition PLIFT2 (prop : phi -> phi -> Prop) : (pphi -> pphi -> Prop) :=
  fun pp1 pp2 => exists p1' p2', pp1 p1' /\ pp2 p2' /\ prop p1' p2'.

Definition GLIFT2 (prop : phi -> phi -> Prop) : (gphi -> gphi -> Prop) :=
  fun gp1 gp2 => PLIFT2 prop (gGamma gp1) (gGamma gp2).

Definition sfrmgphi (a : A_s) (p : gphi) : Prop :=
  fst p = true \/ sfrmphi a (snd p).


