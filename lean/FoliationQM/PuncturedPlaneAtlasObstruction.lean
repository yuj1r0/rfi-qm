module
public import FoliationQM.PresentedSpinCriterion
public import FoliationQM.PuncturedPlaneRelativeSpin

/-!
# The intrinsic obstruction on the punctured-plane frame bundle

For the geometric frame component of v13 `prop:takabayasi`, the three
half-plane charts have identity Lorentz transitions and hence constant
joint paths on their actual intersections. They give a presentation of
the original geometric target. Its reference smooth Spin lift forces the
intrinsic bundle class to vanish. The reference and twisted physical
classes stay distinct after changing charts for the same geometric action.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PuncturedPlaneAtlasObstruction
open LorentzMatrixGroup PuncturedPlaneSignCover PrincipalAtlasCrossGauge
open PuncturedPlaneGeometricSpin (principalData atlas smoothAtlas)
open SmoothSpinRelativeClass PresentedLorentzBundle

/-- The original geometric target's projection from the total space of the identity cocycle. -/
abbrev projection (n : WithTop ℕ∞) := (PrincipalCocycleBundle.core (principalData n)).proj

/-- The extracted geometric group transition equals the Lorentz identity on every actual pair. -/
theorem transition_one (n : WithTop ℕ∞) (i j : Fin 3) (x : Plane)
    (hi : x ∈ (data (atlas n)).domain i) (hj : x ∈ (data (atlas n)).domain j) :
    (data (atlas n)).transition i j x = 1 :=
  (PrincipalCocycleBundle.geometricData_transition (principalData n) i j x hi hj).trans
    (map_one CliffordSpinLorentz.lorentzHom)

/-- Constant identity paths form a genuine normalized joint family for the geometric charts. -/
def paths (n : WithTop ℕ∞) : PathTransitionData.Family (data (atlas n)) where
  homotopy _ _ := ContinuousMap.const _ 1
  source _ _ _ := rfl
  target i j x := (transition_one n i j x x.property.1 x.property.2).symm
  diagonal _ _ _ := rfl

/-- Each path is the Lorentz identity at every time on its actual chart intersection. -/
theorem paths_apply (n : WithTop ℕ∞) (i j : Fin 3) (t : unitInterval)
    (x : PathTransitionData.pairOverlap (data (atlas n)) i j) :
    (paths n).homotopy i j (t, x) = 1 := rfl

/-- The three actual half-plane charts supply a presentation witness on this original bundle. -/
theorem witness (n : WithTop ℕ∞) : HasPresentation (projection n) (atlas n).right :=
  has_of_atlas (atlas n) rfl (paths n)

/-- The canonical all-cover bundle obstruction for the exhibited punctured-plane target. -/
def bundleClass (n : WithTop ℕ∞) : ModTwoAllCover.GlobalH2 Plane :=
  letI : LocallyPathConnectedSpace Plane := punctured.isOpen.locallyPathConnectedSpace
  PresentedLorentzBundle.obstruction (witness n)

/-- The actual reference smooth Spin lift proves that the constructed degree-two class vanishes. -/
theorem bundleClass_zero (n : WithTop ℕ∞) : bundleClass n = 0 := by
  let : LocallyPathConnectedSpace Plane := punctured.isOpen.locallyPathConnectedSpace
  exact (PresentedSpinCriterion.nonempty_iff (smoothAtlas n) (witness n)).mp
    ⟨PuncturedPlaneRelativeSpin.reference n⟩

/-- Transport to any target atlas with the same geometric action keeps the two
explicit physical Spin classes distinct on the original total space. -/
theorem distinct_rechart {κ : Type*} (n : WithTop ℕ∞)
    (C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) (projection n) κ)
    (hr : (atlas n).right = C.right) :
    SpinLiftAtlasChange.classEquiv hr (physicalClass (PuncturedPlaneRelativeSpin.twisted n)) ≠
      SpinLiftAtlasChange.classEquiv hr (physicalClass (PuncturedPlaneRelativeSpin.reference n)) :=
  fun h => PuncturedPlaneRelativeSpin.physicalClass_ne n ((SpinLiftAtlasChange.classEquiv hr).injective h)

/-- The same projected right-action space has zero obstruction and two different
physical Spin classes when expressed through any other geometric atlas. -/
theorem zero_and_distinct {κ : Type*} (n : WithTop ℕ∞)
    (C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) (projection n) κ)
    (hr : (atlas n).right = C.right) :
    bundleClass n = 0 ∧ ∃ p q : PhysicalClass model (model.prod CliffordSpinLorentzSmooth.lorentzModel) C n,
      p ≠ q := ⟨bundleClass_zero n, _, _, distinct_rechart n C hr⟩

end FoliationQM.PuncturedPlaneAtlasObstruction
