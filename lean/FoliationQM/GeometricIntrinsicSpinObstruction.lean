module
public import FoliationQM.LorentzIntrinsicObstruction
public import FoliationQM.GlobalTransitionLoopObstruction

/-!
# Geometric Spin criteria from the independent intrinsic path class

For the geometric component of v13 `prop:takabayasi`, the proved actual
path-to-Spin comparison identifies the independently constructed native
Cech class with the physical obstruction. Its vanishing detects Spin
cocycles on a fixed cover, after refinement, and genuine smooth Spin
lifts of the original geometric target. The established all-cover H1
torsor and unique-class criterion follow. Joint transition paths and
local path connectedness remain explicit; conventional w2 is not asserted.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GeometricIntrinsicSpinObstruction
open LorentzTransitionPaths SpinTransitionPathLifts
open CliffordSpinCoverRefinement CliffordSpinCocycleCorrection
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  [LocallyPathConnectedSpace B] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- The independent fixed-cover class vanishes exactly when the original transitions have a genuine Spin cocycle on that cover. -/
theorem fixed_zero_iff (P : Family D) :
    LorentzIntrinsicObstruction.fixedClass P = 0 ↔ HasSpinCocycleLift D := by
  rw [LorentzIntrinsicObstruction.fixedClass_eq, ← TransitionLoopCocycle.classOf_cocycle P]
  exact GlobalTransitionLoopObstruction.class_zero_iff P

/-- The independent global class vanishes exactly when an actual Spin cocycle exists on a further open refinement. -/
theorem zero_iff_refinement (P : Family D) :
    LorentzIntrinsicObstruction.obstruction P = 0 ↔
      ∃ R : Refinement D.domain B, HasSpinCocycleLift (lorentzData D R) := by
  rw [LorentzIntrinsicObstruction.obstruction_eq]
  exact ModTwoSpinObstruction.obstruction_zero_iff (pairLifts P)

variable {EP HP T : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] [TopologicalSpace T] [ChartedSpace HP T]
  {KT : ModelWithCorners ℝ EP HP} {proj : T → B}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KT L n) [IsManifold I n B]

/-- The independent intrinsic class detects existence of a genuine smooth Spin lift of the original geometric Lorentz target. -/
theorem nonempty_iff (P : Family (AdaptedGeometricSpinLift.lorentzData LM)) :
    Nonempty (SmoothLift I KT L n) ↔ LorentzIntrinsicObstruction.obstruction P = 0 := by
  rw [LorentzIntrinsicObstruction.obstruction_eq]
  exact ModTwoSpinObstruction.nonempty_iff LM (pairLifts P)

/-- Vanishing of the independent class supplies the actual all-cover degree-one torsor of physical lift classes. -/
@[instance_reducible] def torsor_of_zero
    (P : Family (AdaptedGeometricSpinLift.lorentzData LM))
    (h : LorentzIntrinsicObstruction.obstruction P = 0) :
    Torsor (SpinAllCoverHOne.GlobalH1 I B n) (SmoothSpinRelativeClass.PhysicalClass I KT L n) :=
  SmoothSpinHOneTorsor.torsor LM ((nonempty_iff LM P).mpr h)

/-- The independent class and degree-one cohomology give the exact uniqueness criterion for physical smooth Spin lift classes. -/
theorem unique_iff (P : Family (AdaptedGeometricSpinLift.lorentzData LM)) :
    (∃! _p : SmoothSpinRelativeClass.PhysicalClass I KT L n, True) ↔
      LorentzIntrinsicObstruction.obstruction P = 0 ∧ Subsingleton (SpinAllCoverHOne.GlobalH1 I B n) := by
  rw [LorentzIntrinsicObstruction.obstruction_eq]
  exact ModTwoSpinObstruction.unique_iff LM (pairLifts P)

end FoliationQM.GeometricIntrinsicSpinObstruction
