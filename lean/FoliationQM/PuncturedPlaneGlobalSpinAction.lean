module
public import FoliationQM.SmoothSpinHOneTorsor
public import FoliationQM.PuncturedPlaneGlobalDisplacement

/-!
# The global sign interchanges the two exhibited punctured-plane lifts

For the Spin-frame component of v13 `prop:takabayasi`, the nontrivial
three-chart sign acts on physical Spin classes over the same Lorentz
bundle on the punctured plane. It exchanges the two constructed
classes. It fixes no physical lift class of that target.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PuncturedPlaneGlobalSpinAction
open SmoothSpinHOneTorsor SmoothSpinRelativeClass PuncturedPlaneRelativeSpin
open PuncturedPlaneGeometricSpin (smoothAtlas)
open PuncturedPlaneGlobalSign (sign)

/-- Twisting the reference physical class by the global negative edge produces the second lift. -/
theorem act_reference (n : WithTop ℕ∞) : act (smoothAtlas n) (sign n) (physicalClass (reference n)) =
    physicalClass (twisted n) :=
  (act_eq_iff _ _ _ _).mpr (PuncturedPlaneGlobalDisplacement.displacement_eq_sign n)

/-- The same negative-edge sign returns the twisted physical class to the reference. -/
theorem act_twisted (n : WithTop ℕ∞) : act (smoothAtlas n) (sign n) (physicalClass (twisted n)) =
    physicalClass (reference n) := by
  rw [← act_reference n, ← act_mul, SpinHOneUniversal.global_square, act_one]

/-- This global sign has no fixed physical class anywhere in the punctured-plane target. -/
theorem act_ne_self (n : WithTop ℕ∞) (p : PhysicalClass PuncturedPlaneSignCover.model
    (PuncturedPlaneSignCover.model.prod CliffordSpinLorentzSmooth.lorentzModel)
    (PuncturedPlaneGeometricSpin.atlas n) n) : act (smoothAtlas n) (sign n) p ≠ p := by
  intro h
  exact PuncturedPlaneGlobalSign.sign_ne_one n ((act_eq_self_iff (smoothAtlas n) _ p).mp h)

end FoliationQM.PuncturedPlaneGlobalSpinAction
