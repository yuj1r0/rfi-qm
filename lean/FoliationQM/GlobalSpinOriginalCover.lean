module
public import FoliationQM.GlobalSpinPresentationFormula
public import FoliationQM.AdaptedSpinCoverRestriction

/-!
# Computing global displacement from an original adapted Lorentz cover

For the geometric Spin-frame component of v13 `prop:takabayasi`, two
lifts originally adapted to the target can be compared directly on its
original, arbitrarily indexed charts. This computes their displacement
in the quotient of independently charted physical Spin structures.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalSpinOriginalCover
open CliffordSpinLorentzSmooth LorentzMatrixGroup RefinedGeometricPrincipalAtlas
open SpinSignHOne SpinLiftIsomorphism SpinLiftSignDifference SmoothSpinRelativeClass
open GeometricSpinObstruction JointSpinAdaptation SpinAllCoverHOne GlobalSpinDisplacement

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞} (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

/-- Forgetting the common adapted charts sends their fixed-cover ratio to the global physical displacement. -/
theorem displacement_forget (A T : GeometricSpinStructure.Lift I L n) :
    displacement LM (physicalClass (forgetAdaptation LM A)) (physicalClass (forgetAdaptation LM T)) =
    ofCover (domains L) L.covers (classOf (difference (transitions LM A) (transitions LM T))) := by
  let R := SignCommonRefinement.pointCover (domains L) L.covers
  let narrow (S : GeometricSpinStructure.Lift I L n) := AdaptedSpinCoverRestriction.restrict S R
  have same (S : GeometricSpinStructure.Lift I L n) :
      Nonempty (SmoothBetween (forgetAdaptation LM S) (ofRefined LM R (narrow S))) :=
    ⟨⟨Diffeomorph.refl _ _ _, fun _ _ => rfl, fun _ => rfl⟩⟩
  rw [displacement_physicalClass, relative_congr LM (same A) (same T),
    GlobalSpinPresentationFormula.relative_ofRefined LM R (fun _ => rfl)
      (SignCommonRefinement.pointCover_mem (domains L) L.covers)]
  exact (congrArg (ofCover R.domain R.covers)
    (AdaptedSpinCoverRestriction.difference_restrict LM A T R)).trans (ofCover_restrict L.covers R _)

end FoliationQM.GlobalSpinOriginalCover
