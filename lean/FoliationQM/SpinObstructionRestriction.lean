module
public import FoliationQM.SignRefinementPrism
public import FoliationQM.SpinFixedCoverObstruction

/-!
# Naturality of the physical Clifford sign obstruction

Source scope: the Spin-frame component of v13 `prop:takabayasi`. The
class computed from normalized lifts on the smaller charts agrees with
the restriction of the physical class computed on the original cover.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinObstructionRestriction
open CliffordSpinCoverRefinement CliffordSpinTransitionLifts CliffordSpinCocycleCorrection
open SpinSignCohomology SpinSignDefectRepresentative SpinFixedCoverObstruction SignClassRestriction

variable {E H B ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- On a refined triple overlap the extended physical representative and the restricted old representative have the same actual kernel value. -/
theorem representative_on_refinement (P : PairLifts D) (R : Refinement D.domain κ)
    (a b c : κ) (x : B) (ha : x ∈ R.domain a) (hb : x ∈ R.domain b) (hc : x ∈ R.domain c) :
    (representative (pairLifts P R)).value a b c x =
      (restrictTwo R (representative P)).value a b c x := by
  apply Subtype.ext
  rw [restrictTwo_value, representative_val _ a b c x ha hb hc,
    representative_val P _ _ _ x (R.subset a ha) (R.subset b hb) (R.subset c hc)]
  rfl

/-- The class of the refined physical defect is precisely the restriction of the original class. -/
theorem restrictClass_representative (R : Refinement D.domain κ) (P : PairLifts D) :
    restrictClass R (classOf (representative P)) = classOf (representative (pairLifts P R)) := by
  rw [restrictClass_classOf]
  exact classOf_eq_of_eqOn (fun a b c x ha hb hc =>
    (representative_on_refinement P R a b c x ha hb hc).symm)

/-- Independent choices of normalized pair lifts on the two covers compute the same restricted obstruction. -/
theorem restrictClass_eq_of_pairLifts (R : Refinement D.domain κ)
    (P : PairLifts D) (Q : PairLifts (lorentzData D R)) :
    restrictClass R (classOf (representative P)) = classOf (representative Q) :=
  (restrictClass_representative R P).trans (classOf_independent _ Q)

/-- The obstruction attached to the refined Lorentz data equals the restricted original obstruction for any witnesses of pair-lift availability. -/
theorem obstruction_natural (R : Refinement D.domain κ)
    (h : Nonempty (PairLifts D)) (k : Nonempty (PairLifts (lorentzData D R))) :
    restrictClass R (obstruction D h) = obstruction (lorentzData D R) k :=
  restrictClass_eq_of_pairLifts R (Classical.choice h) (Classical.choice k)

/-- Neutrality after this specified restriction detects existence of a genuine Spin lift on exactly the refined opens. -/
theorem restrict_neutral_iff_lift (R : Refinement D.domain κ) (P : PairLifts D) :
    restrictClass R (classOf (representative P)) = neutralClass I R.domain n ↔
      HasSpinCocycleLift (lorentzData D R) := by
  rw [restrictClass_representative]
  exact classOf_neutral_iff_lift _

/-- On the same refined opens, independently chosen pair lifts over either parent assignment yield equal physical obstruction classes. -/
theorem classOf_parent_choice (R : Refinement D.domain κ) (q : κ → ι)
    (hq : ∀ a, (R.domain a : Set B) ⊆ D.domain (q a)) (P : PairLifts D)
    (Q : PairLifts (lorentzData D R))
    (T : PairLifts (lorentzData D (SignRefinementPrism.reparent R q hq))) :
    classOf (representative Q) = classOf (representative T) :=
  (restrictClass_eq_of_pairLifts R P Q).symm.trans
    ((SignRefinementPrism.restrictClass_reparent R q hq _).trans
      (restrictClass_eq_of_pairLifts _ P T))

/-- For Lorentz data with normalized pair lifts, Spin lifting on the refined cover is independent of the containing parent chart assigned to each refined open. -/
theorem lift_iff_reparent (R : Refinement D.domain κ) (q : κ → ι)
    (hq : ∀ a, (R.domain a : Set B) ⊆ D.domain (q a)) (P : PairLifts D) :
    HasSpinCocycleLift (lorentzData D R) ↔
      HasSpinCocycleLift (lorentzData D (SignRefinementPrism.reparent R q hq)) := by
  rw [← restrict_neutral_iff_lift R P, ← restrict_neutral_iff_lift _ P,
    SignRefinementPrism.restrictClass_reparent R q hq]
  exact Iff.rfl

end FoliationQM.SpinObstructionRestriction
