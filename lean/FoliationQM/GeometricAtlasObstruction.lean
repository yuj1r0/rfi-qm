module
public import FoliationQM.LorentzGaugeRefinement
public import FoliationQM.PrincipalAtlasJointGauge
public import FoliationQM.ContractibleLorentzObstruction

/-!
# Comparing the intrinsic obstruction across actual geometric frame atlases

For the geometric frame component of v13 `prop:takabayasi`, take two
atlases of the same principal Lorentz total space with its given
projection and right action. Their genuine coordinate changes and
the local paths in Lorentz charts compare the obstruction computed
from either joint transition family. Cover indices may differ.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GeometricAtlasObstruction
open LorentzMatrixGroup GlobalIntrinsicPathObstruction PathTransitionData
open PrincipalAtlasCrossGauge

variable {B T ι κ : Type*} [TopologicalSpace B] [TopologicalSpace T]
  [LocallyPathConnectedSpace B] {proj : T → B}
  (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
  (C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj κ)

/-- The two original geometric atlases compute the same intrinsic class
when they describe the same right action on the same projected total space. -/
theorem obstruction_eq (hr : A.right = C.right) (P : Family (data A)) (Q : Family (data C)) :
    obstruction LorentzPathCoefficient.character P = obstruction LorentzPathCoefficient.character Q := by
  let R := PrincipalAtlasJointGauge.left A C
  let S := PrincipalAtlasJointGauge.right A C
  apply (restrict _ P R).symm.trans
  apply Eq.trans _ (restrict _ Q S)
  exact LorentzGaugeRefinement.obstruction_eq _ (IntrinsicPathRestriction.family P R)
    (IntrinsicPathRestriction.family Q S) (PrincipalAtlasJointGauge.gauge A C) rfl
    (fun i j x hi hj => (PrincipalAtlasJointGauge.transition_conjugate A C hr i j x hi hj).symm)

/-- On two covers with contractible nonempty pairs the comparison uses the
transition families constructed directly from their separate overlap topologies. -/
theorem constructed_eq (hr : A.right = C.right)
    (hA : ContractibleTransitionPaths.PairContractible (data A))
    (hC : ContractibleTransitionPaths.PairContractible (data C)) :
    obstruction LorentzPathCoefficient.character (ContractibleTransitionPaths.family (data A) hA) =
      obstruction LorentzPathCoefficient.character (ContractibleTransitionPaths.family (data C) hC) :=
  obstruction_eq A C hr _ _

section Smooth
open CliffordSpinLorentzSmooth
variable {E H ET HT : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [ChartedSpace H B] [ChartedSpace HT T] {I : ModelWithCorners ℝ E H} {K : ModelWithCorners ℝ ET HT}
  {n m : WithTop ℕ∞}
  (AM : GeometricPrincipalSmoothAtlas.Data I lorentzModel K A n)
  (CM : GeometricPrincipalSmoothAtlas.Data I lorentzModel K C m)

/-- Independently smooth atlases and their original Lorentz families give
equal intrinsic global classes, even at different differentiability orders. -/
theorem smooth_eq (hr : A.right = C.right)
    (P : LorentzTransitionPaths.Family (AdaptedGeometricSpinLift.lorentzData AM))
    (Q : LorentzTransitionPaths.Family (AdaptedGeometricSpinLift.lorentzData CM)) :
    LorentzIntrinsicObstruction.obstruction P = LorentzIntrinsicObstruction.obstruction Q :=
  obstruction_eq A C hr (LorentzIntrinsicObstruction.family P) (LorentzIntrinsicObstruction.family Q)

/-- Under the explicit pair-contractibility hypotheses, each smooth atlas
constructs the same class from its own transitions. -/
theorem smooth_constructed_eq (hr : A.right = C.right)
    (hA : ContractibleLorentzObstruction.PairContractible (AdaptedGeometricSpinLift.lorentzData AM))
    (hC : ContractibleLorentzObstruction.PairContractible (AdaptedGeometricSpinLift.lorentzData CM)) :
    ContractibleLorentzObstruction.obstruction (AdaptedGeometricSpinLift.lorentzData AM) hA =
      ContractibleLorentzObstruction.obstruction (AdaptedGeometricSpinLift.lorentzData CM) hC :=
  constructed_eq A C hr hA hC

/-- The normalized physical Spin pair-lift obstructions computed in the
two original atlases agree through the intrinsic comparison. -/
theorem physical_eq (hr : A.right = C.right)
    (P : LorentzTransitionPaths.Family (AdaptedGeometricSpinLift.lorentzData AM))
    (Q : LorentzTransitionPaths.Family (AdaptedGeometricSpinLift.lorentzData CM))
    (S : CliffordSpinTransitionLifts.PairLifts (AdaptedGeometricSpinLift.lorentzData AM))
    (U : CliffordSpinTransitionLifts.PairLifts (AdaptedGeometricSpinLift.lorentzData CM)) :
    ModTwoSpinObstruction.obstruction S = ModTwoSpinObstruction.obstruction U :=
  (LorentzIntrinsicObstruction.obstruction_eq_of_pairLifts P S).symm.trans
    ((smooth_eq A C AM CM hr P Q).trans (LorentzIntrinsicObstruction.obstruction_eq_of_pairLifts Q U))

end Smooth
end FoliationQM.GeometricAtlasObstruction
