module
public import FoliationQM.SpinAllCoverHTwo
public import FoliationQM.GlobalSpinClassificationCriterion

/-!
# The physical Spin obstruction in degree two over all covers

For the geometric Spin-frame component of v13 `prop:takabayasi`,
normalized lifts of Lorentz transitions give a global degree-two sign
class. Its neutrality detects geometric Spin existence. The degree-one
classification can then be applied to the same physical target.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalSpinObstruction
open CliffordSpinCoverRefinement CliffordSpinTransitionLifts CliffordSpinCocycleCorrection
open SpinSignCohomology SpinSignDefectRepresentative SpinAllCoverHTwo
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction

variable {E H B ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The actual triple-overlap Spin defect, included in degree-two cohomology over all covers. -/
def obstruction (S : PairLifts D) : GlobalH2 I B n :=
  ofCover D.domain D.covers (classOf (representative S))

/-- Choosing different normalized pair lifts leaves the global obstruction unchanged. -/
theorem obstruction_independent (S T : PairLifts D) : obstruction S = obstruction T :=
  congrArg (ofCover D.domain D.covers) (SpinFixedCoverObstruction.classOf_independent S T)

/-- Any choices of pair lifts on a refined Lorentz cover compute the original global obstruction. -/
theorem obstruction_refine (S : PairLifts D) (R : Refinement D.domain κ)
    (T : PairLifts (lorentzData D R)) : obstruction T = obstruction S := by
  unfold obstruction
  rw [← SpinObstructionRestriction.restrictClass_eq_of_pairLifts R S T]
  exact ofCover_restrict D.covers R _

/-- A global obstruction is neutral exactly when a genuine Spin cocycle exists on some refinement. -/
theorem obstruction_one_iff (S : PairLifts D) : obstruction S = 1 ↔
    ∃ R : Refinement D.domain B, HasSpinCocycleLift (lorentzData D R) :=
  (ofCover_eq_one_iff D.domain D.covers _).trans
    (SignEventualObstruction.vanishes_iff_exists_refinement_lift S)

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n) [IsManifold I n B]

/-- The all-cover degree-two obstruction of the extracted Lorentz charts vanishes exactly when
the original physical target has a smooth geometric Spin lift. -/
theorem nonempty_iff (S : PairLifts (AdaptedGeometricSpinLift.lorentzData LM)) :
    Nonempty (SmoothLift I KP L n) ↔ obstruction S = 1 :=
  (nonempty_iff_refinement_lift LM).trans (obstruction_one_iff S).symm

/-- A neutral degree-two obstruction supplies the degree-one torsor of physical lift classes. -/
@[instance_reducible] def torsor_of_neutral
    (S : PairLifts (AdaptedGeometricSpinLift.lorentzData LM)) (h : obstruction S = 1) :
    Torsor (SpinAllCoverHOne.GlobalH1 I B n) (SmoothSpinRelativeClass.PhysicalClass I KP L n) :=
  SmoothSpinHOneTorsor.torsor LM ((nonempty_iff LM S).mpr h)

/-- Exactly one physical class exists when and only when the global obstruction is neutral
and the global degree-one sign group is trivial. -/
theorem unique_iff (S : PairLifts (AdaptedGeometricSpinLift.lorentzData LM)) :
    (∃! _p : SmoothSpinRelativeClass.PhysicalClass I KP L n, True) ↔
    obstruction S = 1 ∧ Subsingleton (SpinAllCoverHOne.GlobalH1 I B n) :=
  (GlobalSpinClassificationCriterion.unique_iff LM).trans (and_congr_left fun _ => nonempty_iff LM S)

end FoliationQM.GlobalSpinObstruction
