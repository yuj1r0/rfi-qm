module
public import FoliationQM.TransitionLoopCocycle

/-!
# The global obstruction represented by Lorentz transition loops

For the geometric Spin-frame component of v13 `prop:takabayasi`, the
independently defined loop coefficients represent the same mod-two class
as the physical Spin defect. The class is independent of path families
and compatible with refinement. Vanishing of a class permits a pair
coboundary correction; it does not assert that every chosen triangular
loop is already nullhomotopic. The conventional w2 comparison is pending.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalTransitionLoopObstruction
open CliffordSpinCoverRefinement CliffordSpinCocycleCorrection
open LorentzTransitionPaths SpinTransitionPathLifts TransitionLoopCocycle
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction

variable {E H B ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The fixed-cover class of the actual transition-loop coefficients is independent of normalized continuous path families. -/
theorem class_independent (P Q : Family D) :
    ModTwoCohomology.classOf (cocycle P) = ModTwoCohomology.classOf (cocycle Q) := by
  rw [classOf_cocycle, classOf_cocycle]
  exact congrArg (fun c => SpinModTwoComparison.classEquiv I D.domain n (Additive.ofMul c))
    (SpinFixedCoverObstruction.classOf_independent (pairLifts P) (pairLifts Q))

/-- The fixed-cover loop class vanishes exactly when the given Lorentz cocycle admits a Spin cocycle on that cover. -/
theorem class_zero_iff (P : Family D) :
    ModTwoCohomology.classOf (cocycle P) = 0 ↔ HasSpinCocycleLift D := by
  rw [classOf_cocycle]
  change SpinModTwoComparison.classEquiv I D.domain n
    (Additive.ofMul (SpinSignCohomology.classOf (SpinSignDefectRepresentative.representative (pairLifts P)))) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff]
  exact SpinFixedCoverObstruction.classOf_neutral_iff_lift (pairLifts P)

/-- If all chosen triangles are nullhomotopic, their fixed-cover class is zero, without any pair correction. -/
theorem class_zero_of_null_triangles (P : Family D)
    (h : ∀ i j k x (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k),
      (triangle P i j k x hi hj hk).Homotopic (Path.refl 1)) :
    ModTwoCohomology.classOf (cocycle P) = 0 := by
  change ModTwoCohomology.classOf (cocycle P) = ModTwoCohomology.classOf (0 : ModTwoCohomology.TwoCocycle D.domain)
  apply ModTwoCohomology.classOf_eq_of_eqOn
  intro i j k x hi hj hk
  change (cocycle P).value i j k x = 0
  rw [cocycle_value P i j k x hi hj hk]
  exact (coefficient_zero_iff P i j k x hi hj hk).mpr (h i j k x hi hj hk)

/-- The global mod-two class represented by the actual triangular transition loops. -/
def obstruction (P : Family D) : ModTwoAllCover.GlobalH2 B :=
  ModTwoAllCover.ofCover D.domain D.covers (ModTwoCohomology.classOf (cocycle P))

/-- Transition-loop monodromy computes the original physical obstruction of the constructed Spin endpoints. -/
theorem obstruction_eq (P : Family D) :
    obstruction P = ModTwoSpinObstruction.obstruction (pairLifts P) :=
  congrArg (ModTwoAllCover.ofCover D.domain D.covers) (classOf_cocycle P)

/-- Changing the normalized continuous transition paths does not change the global obstruction. -/
theorem obstruction_independent (P Q : Family D) : obstruction P = obstruction Q :=
  congrArg (ModTwoAllCover.ofCover D.domain D.covers) (class_independent P Q)

/-- Any path family on an open refinement computes the original global obstruction. -/
theorem obstruction_refine (P : Family D) (R : Refinement D.domain κ)
    (Q : Family (lorentzData D R)) : obstruction Q = obstruction P := by
  rw [obstruction_eq, obstruction_eq]
  exact ModTwoSpinObstruction.obstruction_refine (pairLifts P) R (pairLifts Q)

/-- Global vanishing of the loop class is exactly existence of a genuine Spin cocycle after refinement. -/
theorem obstruction_zero_iff (P : Family D) : obstruction P = 0 ↔
    ∃ R : Refinement D.domain B, HasSpinCocycleLift (lorentzData D R) := by
  rw [obstruction_eq]
  exact ModTwoSpinObstruction.obstruction_zero_iff (pairLifts P)

variable {EP HP T : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  [TopologicalSpace T] [ChartedSpace HP T] {KT : ModelWithCorners ℝ EP HP}
  {proj : T → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KT L n) [IsManifold I n B]

/-- A physical smooth Spin lift exists precisely when the actual transition-loop obstruction vanishes. -/
theorem nonempty_iff (P : Family (AdaptedGeometricSpinLift.lorentzData LM)) :
    Nonempty (SmoothLift I KT L n) ↔ obstruction P = 0 := by
  rw [obstruction_eq]
  exact ModTwoSpinObstruction.nonempty_iff LM (pairLifts P)

/-- The loop class and the all-cover degree-one group give the exact unique-lift-class criterion. -/
theorem unique_iff (P : Family (AdaptedGeometricSpinLift.lorentzData LM)) :
    (∃! _p : SmoothSpinRelativeClass.PhysicalClass I KT L n, True) ↔
    obstruction P = 0 ∧ Subsingleton (SpinAllCoverHOne.GlobalH1 I B n) := by
  rw [obstruction_eq]
  exact ModTwoSpinObstruction.unique_iff LM (pairLifts P)

end FoliationQM.GlobalTransitionLoopObstruction
