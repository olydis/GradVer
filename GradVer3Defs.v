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

Definition sfrmgphi (a : A_s) (p : gphi) : Prop :=
  fst p = true \/ sfrmphi a (snd p).
  
Definition good (p : phi) := phiSatisfiable p /\ sfrmphi [] p.
Definition gGood (gp : gphi) := gphiSatisfiable gp /\ sfrmgphi [] gp.
Definition ppGood (pp : pphi) :=
  (exists p, pp p) /\
  (forall p, pp p -> good p).

Definition gphiImplies (gp1 gp2 : gphi) : Prop :=
  if fst gp1
  then (exists meet, good meet ∧ phiImplies meet (snd gp1) ∧ phiImplies meet (snd gp2))
  else phiImplies (snd gp1) (snd gp2).


(* concretization *)
Definition gGamma' (phi : gphi) : pphi :=
  match fst phi with
  | false => (fun p => p = snd phi)
  | true => (fun p => good p /\ phiImplies p (snd phi))
  end.

Inductive gGamma : gphi -> pphi -> Prop :=
| GammaAll : forall gp pp,
  gGood gp ->
  gGamma' gp = pp ->
  gGamma gp pp
.

(* abstraction *)
Definition ppIsSingleton (p : phi) (pp : pphi) :=
  pp p /\ (forall p', pp p' -> p' = p).
Definition ppHasUpperBound (p : phi) (pp : pphi) :=
  forall p', pp p' -> phiImplies p' p.
Definition ppHasSupremum (p : phi) (pp : pphi) :=
  ppHasUpperBound p pp /\ (forall p', ppHasUpperBound p' pp -> phiImplies p p').
Definition ppHasMaximum (p : phi) (pp : pphi) :=
  pp p /\ (forall p', pp p' -> phiImplies p' p).

Inductive gAlpha : pphi -> gphi -> Prop :=
| AlphaAll : forall gp pp,
  ppGood pp ->
  gGood gp ->
  pincl pp (gGamma' gp) ->
  (forall gp', gGood gp' -> pincl pp (gGamma' gp') -> pincl (gGamma' gp) (gGamma' gp')) ->
  gAlpha pp gp
.

Definition PLIFT1 (prop : phi -> Prop) : (pphi -> Prop) :=
  fun pp => exists p', pp p' /\ prop p'.

Definition GLIFT1 (prop : phi -> Prop) : (gphi -> Prop) :=
  fun gp => exists pp, gGamma gp pp /\ PLIFT1 prop pp.

Definition PLIFT2 (prop : phi -> phi -> Prop) : (pphi -> pphi -> Prop) :=
  fun pp1 pp2 => exists p1' p2', pp1 p1' /\ pp2 p2' /\ prop p1' p2'.

Definition GLIFT2 (prop : phi -> phi -> Prop) : (gphi -> gphi -> Prop) :=
  fun gp1 gp2 => exists pp1 pp2, gGamma gp1 pp1 /\ gGamma gp2 pp2 /\ PLIFT2 prop pp1 pp2.

Definition PLIFT4 (prop : phi -> phi -> phi -> phi -> Prop) : (pphi -> pphi -> pphi -> pphi -> Prop) :=
  fun pp1 pp2 pp3 pp4 => exists p1' p2' p3' p4', pp1 p1' /\ pp2 p2' /\ pp3 p3' /\ pp4 p4' /\ prop p1' p2' p3' p4'.

Definition GLIFT4 (prop : phi -> phi -> phi -> phi -> Prop) : (gphi -> gphi -> gphi -> gphi -> Prop) :=
  fun gp1 gp2 gp3 gp4 => exists pp1 pp2 pp3 pp4, gGamma gp1 pp1 /\ gGamma gp2 pp2 /\ gGamma gp3 pp3 /\ gGamma gp4 pp4 /\ PLIFT4 prop pp1 pp2 pp3 pp4.


(* hasWellFormedSubtype *)
Axiom hasWellFormedSubtype : forall p,
  phiSatisfiable p ->
  ∃ p' : phi, phiSatisfiable p' ∧ sfrmphi [] p' ∧ FV p = FV p' ∧ phiImplies p' p.

Definition pphiEquals (pp1 pp2 : pphi) :=
    pincl pp1 pp2 /\ pincl pp2 pp1.

Definition gphiEquals (gp1 gp2 : gphi) :=
  exists pp1 pp2,
    gGamma gp1 pp1 /\ gGamma gp2 pp2 /\
    pphiEquals pp1 pp2.
