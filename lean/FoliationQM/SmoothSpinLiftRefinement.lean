module
public import FoliationQM.GeometricSpinRefinement
public import FoliationQM.SignCommonRefinement

/-!
# An open refinement extracted from a smooth geometric Spin map

Source scope: the geometric Spin-frame component of v13 `prop:takabayasi`.
The original source and target may use different sets of charts. The
adapted neighborhoods of a smooth equivariant map give an actual
refinement of the target Lorentz cocycle on which a Spin lift exists.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SmoothSpinLiftRefinement
open CliffordSpinMap CliffordSpinLorentzSmooth LorentzMatrixGroup
open CliffordSpinCoverRefinement CliffordSpinCocycleCorrection

variable {E EQ EP H HQ HP B Q P ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace H] [TopologicalSpace HQ] [TopologicalSpace HP]
  [TopologicalSpace B] [ChartedSpace H B] [TopologicalSpace Q] [ChartedSpace HQ Q]
  [TopologicalSpace P] [ChartedSpace HP P]
  {I : ModelWithCorners ℝ E H} {KQ : ModelWithCorners ℝ EQ HQ} {KP : ModelWithCorners ℝ EP HP}
  {spinProj : Q → B} {frameProj : P → B} {n : WithTop ℕ∞}
  {S : GeometricPrincipalAtlas.Data (G := Spin) spinProj ι}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj κ}
  (F : GeometricSpinLift.Map S L)
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

/-- The adapted neighborhood indexed by two old charts and a local Spin inverse lies in its designated target chart. -/
def refinementOfMap : Refinement (AdaptedGeometricSpinLift.lorentzData LM).domain (ι × κ × Spin) where
  parent k := k.2.1
  domain k := ⟨GeometricSpinAdaptedCharts.domain F n k.1 k.2.1 k.2.2,
    GeometricSpinAdaptedCharts.isOpen_domain F n k.1 k.2.1 k.2.2⟩
  covers x := by
    obtain ⟨i, j, s, hx⟩ := GeometricSpinAdaptedCharts.domains_cover F n x
    exact ⟨(i, j, s), hx⟩
  subset _ _ hx := hx.1.2

/-- The Lorentz cocycle extracted from the adapted charts is the restriction of the original target transitions along that refinement. -/
theorem extracted_lorentzData :
    AdaptedGeometricSpinLift.lorentzData (GeometricSpinAdaptedCharts.refinedLorentzSmoothAtlas F n LM) =
      lorentzData (AdaptedGeometricSpinLift.lorentzData LM) (refinementOfMap F LM) := rfl

/-- Every independently smooth equivariant geometric Spin map gives an actual cocycle lift on the explicitly constructed refinement of its target atlas. -/
theorem lift_on_refinement (SM : GeometricPrincipalSmoothAtlas.Data I spinModel KQ S n)
    (hF : ContMDiff KQ KP n F) :
    HasSpinCocycleLift (lorentzData (AdaptedGeometricSpinLift.lorentzData LM)
      (refinementOfMap F LM)) := by
  rw [← extracted_lorentzData]
  exact GeometricSpinAdaptedCharts.hasSpinCocycleLift_refined F n SM LM hF

/-- A smooth equivariant geometric map supplies a base-point-indexed refinement with a genuine cocycle lift, for arbitrary original chart index types. -/
theorem exists_refinement_of_map (SM : GeometricPrincipalSmoothAtlas.Data I spinModel KQ S n)
    (hF : ContMDiff KQ KP n F) :
    ∃ R : Refinement (AdaptedGeometricSpinLift.lorentzData LM).domain B,
      HasSpinCocycleLift (lorentzData (AdaptedGeometricSpinLift.lorentzData LM) R) := by
  let R := refinementOfMap F LM
  let T := SignCommonRefinement.pointCover R.domain R.covers
  refine ⟨SpinRefinementComposition.compose R T, ?_⟩
  rw [← SpinRefinementComposition.lorentzData_compose R T]
  exact SpinRefinementComposition.hasSpinCocycleLift T (lift_on_refinement F LM SM hF)

end FoliationQM.SmoothSpinLiftRefinement
