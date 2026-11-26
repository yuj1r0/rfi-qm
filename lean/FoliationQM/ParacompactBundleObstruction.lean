module
public import FoliationQM.ParacompactLorentzPresentation

/-!
# The native mod-two obstruction of an ordinary principal Lorentz atlas

For the geometric frame component of v13 `prop:takabayasi`, paracompactness
and normality construct a presentation from any actual atlas. On a locally
path connected base, its intrinsic Čech class is uniquely determined by
evaluation on the refined chart transitions. This supplies a class without
an independently chosen presentation or a Spin lift.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ParacompactBundleObstruction
open LorentzMatrixGroup PrincipalAtlasCrossGauge PresentedLorentzBundle
open RefinedGeometricPrincipalAtlas CliffordSpinCoverRefinement PathTransitionData
open ParacompactLorentzPresentation

variable {B T ι κ : Type*} [TopologicalSpace B] [TopologicalSpace T]
  [ParacompactSpace B] [NormalSpace B] [LocallyPathConnectedSpace B] {proj : T → B}
  (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)

/-- The native degree-two class obtained from the actual atlas on its original total space. -/
def obstruction : ModTwoAllCover.GlobalH2 B :=
  PresentedLorentzBundle.obstruction (hasPresentation A)

/-- Any other presentation witness for the same projection and right action gives this class. -/
theorem eq_presented (h : HasPresentation proj A.right) :
    obstruction A = PresentedLorentzBundle.obstruction h := rfl

/-- Any normalized joint path family on another atlas of the same projected action computes the class. -/
theorem eq_family (C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj κ)
    (hr : C.right = A.right) (P : Family (data C)) :
    obstruction A = GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character P :=
  PresentedLorentzBundle.obstruction_eq (hasPresentation A) C hr P

/-- Compute the class on the actual anchored refinement constructed from the given atlas. -/
theorem eq_constructed :
    obstruction A = GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character
      (ParacompactLorentzPresentation.family A) :=
  eq_family A (ParacompactLorentzPresentation.atlas A) rfl _

/-- Every normalized family on every refinement of the original trivializations computes the same value. -/
theorem eq_on_refinement (R : Refinement (domains A) κ) (P : Family (data (restrictedAtlas A R))) :
    obstruction A = GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character P :=
  eq_family A (restrictedAtlas A R) rfl P

/-- Atlas indices and trivializations may change while the projection and right action stay fixed. -/
theorem eq_of_right_eq (C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj κ)
    (hr : A.right = C.right) : obstruction A = obstruction C :=
  (eq_family A (ParacompactLorentzPresentation.atlas C) hr.symm
    (ParacompactLorentzPresentation.family C)).trans (eq_constructed C).symm

/-- Values on anchored refinements of the given chart cover uniquely characterize the native class. -/
theorem existsUnique_anchored_value :
    ∃! c : ModTwoAllCover.GlobalH2 B, ∀ (R : Refinement (domains A) B),
      (∀ x, x ∈ R.domain x) → ∀ P : Family (data (restrictedAtlas A R)),
        c = GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character P := by
  refine ⟨obstruction A, fun R _ P => eq_on_refinement A R P, ?_⟩
  intro c hc
  exact (hc (refinement A) (mem_refinement A) (ParacompactLorentzPresentation.family A)).trans
    (eq_constructed A).symm

end FoliationQM.ParacompactBundleObstruction
