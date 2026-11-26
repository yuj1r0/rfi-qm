module
public import FoliationQM.AdaptedGeometricSpinLift
public import FoliationQM.GeometricSpinAdaptedCharts

/-!
# Actual Spin cocycles on the explicit geometric refinement

Source scope: the geometric Spin-structure bridge underlying v13
`prop:takabayasi`. An existing smooth physical equivariant geometric map
between independent principal atlases has the previously constructed
explicit adapted refinement. Its proved domain and unit-section equations
give genuine adaptation, and actual geometric extraction then supplies a
same-cover Clifford Spin cocycle lift of the refined Lorentz transitions.
Neither adaptation on the original cover nor a global coefficient lift is
assumed. Both original total topologies and smooth structures are retained.
-/

@[expose] public section
open scoped Manifold
namespace FoliationQM.GeometricSpinAdaptedCharts
open CliffordSpinMap CliffordSpinLorentzSmooth LorentzMatrixGroup

variable {EB EQ EP HB HQ HP B Q P : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HB] [TopologicalSpace HQ] [TopologicalSpace HP]
  [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace Q] [ChartedSpace HQ Q]
  [TopologicalSpace P] [ChartedSpace HP P]
  {I : ModelWithCorners ℝ EB HB} {KQ : ModelWithCorners ℝ EQ HQ}
  {KP : ModelWithCorners ℝ EP HP}
  {spinProj : Q → B} {frameProj : P → B} {ι κ : Type*}
  {S : GeometricPrincipalAtlas.Data (G := Spin) spinProj ι}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj κ}
  (F : GeometricSpinLift.Map S L) (n : WithTop ℕ∞)
  (SF : GeometricPrincipalSmoothAtlas.Data I spinModel KQ S n)
  (LF : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
  (hF : ContMDiff KQ KP n F)

include SF LF hF

/-- The original geometric map on the explicit refined atlases is genuinely adapted, by the independently proved equal domains and actual canonical-unit compatibility. -/
theorem refinedAdapted :
    AdaptedGeometricSpinLift.Adapted (refinedMap F n SF LF hF) where
  domain_eq := refined_domain_eq F n SF LF hF
  unit := refined_unit F n SF LF hF

/-- Every existing smooth geometric Spin lift yields a genuine Clifford Spin cocycle lift on its explicit adapted refinement, without requiring adaptation to either original chart cover. -/
theorem hasSpinCocycleLift_refined :
    CliffordSpinCocycleCorrection.HasSpinCocycleLift
      (AdaptedGeometricSpinLift.lorentzData (refinedLorentzSmoothAtlas F n LF)) :=
  (refinedAdapted F n SF LF hF).hasSpinCocycleLift
    (refinedSpinSmoothAtlas F n SF LF hF) (refinedLorentzSmoothAtlas F n LF)

end FoliationQM.GeometricSpinAdaptedCharts
