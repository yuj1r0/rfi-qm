module
public import FoliationQM.PresentedBundlePullback
public import FoliationQM.PresentedSpinCriterion

/-!
# Smooth Spin lifts on a geometric pullback

For the geometric frame component of v13 `prop:takabayasi`, give the
actual fiber product smooth charts for its pulled right action. The
pullback of the original topological bundle class then detects the
existence and uniqueness of physical Spin lifts on this smooth target.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PullbackSpinCriterion
open LorentzMatrixGroup CliffordSpinLorentzSmooth PresentedLorentzBundle
open GeometricSpinObstruction GeometricPrincipalPullback

variable {X B T ι E H ET HT : Type*} [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace T]
  [LocallyPathConnectedSpace X] [LocallyPathConnectedSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [ChartedSpace H X]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  {I : ModelWithCorners ℝ E H} {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞} [IsManifold I n X]
  {proj : T → B} {act : T → ProperFutureLorentz → T} (f : C(X, B)) (h : HasPresentation proj act)
  [ChartedSpace HT (Total f proj)]
  {C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) (projection f proj) ι}
  (CM : GeometricPrincipalSmoothAtlas.Data I lorentzModel K C n) (hr : C.right = PresentedBundlePullback.right f h)

include CM hr in
/-- The original bundle's pulled class detects smooth lift existence in any compatible smooth atlas of the fiber product. -/
theorem nonempty_iff : Nonempty (SmoothLift I K C n) ↔ ModTwoGlobalPullback.pull f (obstruction h) = 0 := by
  have k : HasPresentation (projection f proj) C.right := hr.symm ▸ PresentedBundlePullback.hasPresentation f h
  rw [← PresentedBundlePullback.obstruction_of_right_eq f h k hr]
  exact PresentedSpinCriterion.nonempty_iff CM k

include CM hr in
/-- Vanishing before pullback suffices to construct a smooth Spin lift of the presented smooth pullback target. -/
theorem nonempty_of_zero (hz : obstruction h = 0) : Nonempty (SmoothLift I K C n) :=
  (nonempty_iff f h CM hr).mpr (by rw [hz, map_zero])

include CM hr in
/-- A smooth target over a constant base map has a physical Spin lift for every original presented class. -/
theorem nonempty_of_constant (b : B) (hf : ∀ x, f x = b) : Nonempty (SmoothLift I K C n) := by
  apply (nonempty_iff f h CM hr).mpr
  rw [show f = ContinuousMap.const X b from ContinuousMap.ext hf, ModTwoConstantPullback.pull_const]

/-- Vanishing after pullback gives the physical Spin classes their degree-one torsor over the new base. -/
@[instance_reducible] def torsor_of_zero (hz : ModTwoGlobalPullback.pull f (obstruction h) = 0) :
    Torsor (SpinAllCoverHOne.GlobalH1 I X n) (SmoothSpinRelativeClass.PhysicalClass I K C n) :=
  SmoothSpinHOneTorsor.torsor CM ((nonempty_iff f h CM hr).mpr hz)

include CM hr in
/-- Uniqueness uses the pulled degree-two class and degree one on the actual new base. -/
theorem unique_iff : (∃! _p : SmoothSpinRelativeClass.PhysicalClass I K C n, True) ↔
    ModTwoGlobalPullback.pull f (obstruction h) = 0 ∧ Subsingleton (SpinAllCoverHOne.GlobalH1 I X n) :=
  (GlobalSpinClassificationCriterion.unique_iff CM).trans (and_congr (nonempty_iff f h CM hr) Iff.rfl)

end FoliationQM.PullbackSpinCriterion
