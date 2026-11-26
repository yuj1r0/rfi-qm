module
public import FoliationQM.SmoothSpinRelativeClass
public import FoliationQM.PuncturedPlaneGeometricSpin

/-!
# Comparing the two punctured-plane Spin structures after joint adaptation

For the global Spin-frame component of v13 `prop:takabayasi`, consider the
identity lift and its punctured-plane sign twist as smooth lifts with
their own source charts. Their relative class can be computed afresh on
the constructed common adapted cover and restricted to any finer cover.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PuncturedPlaneRelativeSpin
open SmoothSpinRelativeClass
open PuncturedPlaneGeometricSpin (smoothAtlas)

/-- The punctured-plane reference lift with its source charts indexed independently of the Lorentz atlas. -/
abbrev reference (n : WithTop ℕ∞) :=
  forgetAdaptation (smoothAtlas n) (PuncturedPlaneGeometricSpin.reference n)

/-- The punctured-plane sign-twisted lift with its own point-indexed source charts. -/
abbrev twisted (n : WithTop ℕ∞) :=
  forgetAdaptation (smoothAtlas n) (PuncturedPlaneGeometricSpin.twisted n)

/-- A physical isomorphism of the independently indexed punctured-plane lifts would intertwine the same original maps and actions as a physical isomorphism of the two adapted lifts. -/
theorem not_isomorphic (n : WithTop ℕ∞) : ¬ Nonempty (SmoothBetween (twisted n) (reference n)) :=
  PuncturedPlaneGeometricSpin.not_isomorphic n

/-- The degree-one sign class computed on the new common adapted cover of the two punctured-plane lifts is nonneutral. -/
theorem relativeClass_ne_one (n : WithTop ℕ∞) :
    relativeClass (smoothAtlas n) (twisted n) (reference n) ≠ 1 :=
  fun h => not_isomorphic n ((nonempty_iff_relative_unit (smoothAtlas n) _ _).mpr h)

/-- Restriction to any further open refinement of the common adapted cover preserves the nonneutral computed relative class. -/
theorem refined_relativeClass_ne_one {κ : Type*} (n : WithTop ℕ∞)
    (R : CliffordSpinCoverRefinement.Refinement
      (JointSpinAdaptation.common (smoothAtlas n) (twisted n) (reference n)).domain κ) :
    SpinHOneRestriction.restrictHom R (relativeClass (smoothAtlas n) (twisted n) (reference n)) ≠ 1 :=
  fun h => not_isomorphic n ((nonempty_iff_refined_relative_unit (smoothAtlas n) _ _ R).mpr h)

/-- Independent choice of source charts retains two distinct physical Spin isomorphism classes over the punctured-plane Lorentz target. -/
theorem physicalClass_ne (n : WithTop ℕ∞) : physicalClass (twisted n) ≠ physicalClass (reference n) :=
  fun h => relativeClass_ne_one n ((physicalClass_eq_iff (smoothAtlas n) _ _).mp h)

end FoliationQM.PuncturedPlaneRelativeSpin
