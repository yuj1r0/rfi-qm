module
public import FoliationQM.GlobalModTwoComparison
public import FoliationQM.GlobalSpinObstruction

/-!
# The physical Spin obstruction with independent mod-two coefficients

For the geometric Spin-frame component of v13 `prop:takabayasi`, express
the actual sign defect in the separately constructed additive degree-two
group. The proved coefficient comparison carries the geometric existence
criterion to vanishing of this mod-two class. This class is not designated
as the second Stiefel–Whitney class: the independent characteristic-class
construction and its comparison remain additional proof obligations.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ModTwoSpinObstruction
open CliffordSpinCoverRefinement CliffordSpinTransitionLifts CliffordSpinCocycleCorrection
open SpinSignCohomology SpinSignDefectRepresentative GlobalModTwoComparison
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction

variable {E H B ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The fixed-cover physical defect expressed in the independent mod-two coefficient group. -/
def fixedClass (S : PairLifts D) : ModTwoCohomology.H2 D.domain :=
  SpinModTwoComparison.classEquiv I D.domain n (Additive.ofMul (classOf (representative S)))

/-- The actual lifting obstruction, now a class in topology-only mod-two cohomology over all covers. -/
def obstruction (S : PairLifts D) : ModTwoAllCover.GlobalH2 B :=
  ModTwoAllCover.ofCover D.domain D.covers (fixedClass S)

/-- The independently defined coefficient comparison takes the global sign obstruction to this class. -/
theorem obstruction_eq (S : PairLifts D) :
    obstruction S = coefficientEquiv I n (Additive.ofMul (GlobalSpinObstruction.obstruction S)) :=
  (coefficientEquiv_ofCover I n D.domain D.covers _).symm

/-- The mod-two obstruction does not depend on the choice of normalized actual pair lifts. -/
theorem obstruction_independent (S T : PairLifts D) : obstruction S = obstruction T := by
  rw [obstruction_eq, obstruction_eq, GlobalSpinObstruction.obstruction_independent S T]

/-- Pair lifts on any refinement compute exactly the same global mod-two obstruction. -/
theorem obstruction_refine (S : PairLifts D) (R : Refinement D.domain κ)
    (T : PairLifts (lorentzData D R)) : obstruction T = obstruction S := by
  rw [obstruction_eq, obstruction_eq, GlobalSpinObstruction.obstruction_refine S R T]

/-- Vanishing in the independent mod-two group is equivalent to a genuine Spin cocycle on some refinement. -/
theorem obstruction_zero_iff (S : PairLifts D) : obstruction S = 0 ↔
    ∃ R : Refinement D.domain B, HasSpinCocycleLift (lorentzData D R) := by
  rw [obstruction_eq, coefficientEquiv_eq_zero_iff]
  exact GlobalSpinObstruction.obstruction_one_iff S

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n) [IsManifold I n B]

/-- The original smooth geometric Lorentz target has a Spin lift exactly when its mod-two obstruction vanishes. -/
theorem nonempty_iff (S : PairLifts (AdaptedGeometricSpinLift.lorentzData LM)) :
    Nonempty (SmoothLift I KP L n) ↔ obstruction S = 0 := by
  rw [obstruction_eq, coefficientEquiv_eq_zero_iff]
  exact GlobalSpinObstruction.nonempty_iff LM S

/-- Vanishing of the mod-two obstruction supplies the proved all-cover degree-one torsor of physical lift classes. -/
@[instance_reducible] def torsor_of_zero
    (S : PairLifts (AdaptedGeometricSpinLift.lorentzData LM)) (h : obstruction S = 0) :
    Torsor (SpinAllCoverHOne.GlobalH1 I B n) (SmoothSpinRelativeClass.PhysicalClass I KP L n) :=
  SmoothSpinHOneTorsor.torsor LM ((nonempty_iff LM S).mpr h)

/-- Uniqueness of the physical smooth Spin class is equivalent to mod-two obstruction zero and trivial degree one. -/
theorem unique_iff (S : PairLifts (AdaptedGeometricSpinLift.lorentzData LM)) :
    (∃! _p : SmoothSpinRelativeClass.PhysicalClass I KP L n, True) ↔
    obstruction S = 0 ∧ Subsingleton (SpinAllCoverHOne.GlobalH1 I B n) :=
  (GlobalSpinClassificationCriterion.unique_iff LM).trans (and_congr_left fun _ => nonempty_iff LM S)

end FoliationQM.ModTwoSpinObstruction
