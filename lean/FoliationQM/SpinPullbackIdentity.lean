module
public import FoliationQM.SpinPullbackTargetComparisons
public import FoliationQM.SpinPullbackClasses

/-!
# Identity base change on physical Spin classes

For the frame component of v13 `prop:takabayasi`, take the identity
fiber product on both Spin and Lorentz spaces. After the canonical
comparison of the Lorentz targets, dropping the redundant base coordinate
of each Spin point gives an actual physical isomorphism with the initial
lift. Thus identity pullback acts as the identity on physical classes.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackIdentity
open LorentzMatrixGroup CliffordSpinLorentzSmooth GeometricSpinObstruction SmoothSpinRelativeClass
open SmoothPullbackChartedSpace GeometricPrincipalPullback

variable {B T ι EB ET HB HT : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace B] [ChartedSpace HB B] [TopologicalSpace T] [ChartedSpace HT T]
  {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞}
  [IsManifold IB n B] {p : T → B} {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι}
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K A n)

/-- The identity comparison of the Spin sources intertwines both physical maps to the original Lorentz target. -/
def iso (S : SmoothLift IB K A n) :
    letI := chartedSpace HB LorentzManifold.Model (.id B) A
    SmoothBetween ((SpinPullbackTargetComparisons.identityIso LM).change
      (GeometricSpinPullback.lift (.id B) contMDiff_id LM S)) S := by
  let := chartedSpace HB LorentzManifold.Model (.id B) A
  exact { diffeo := SmoothPullbackComparisons.identity S.smoothAtlas
          equivariant := fun _ _ => rfl
          over := fun _ => rfl }

/-- This physical comparison sends a pair to its original Spin point. -/
theorem iso_apply (S : SmoothLift IB K A n) (s : Total (.id B) S.proj) :
    (iso LM S).diffeo s = s.val.2 := rfl

/-- On all physical classes, identity pullback followed by target identification returns the original class. -/
theorem class_id (c : PhysicalClass IB K A n) :
    letI := chartedSpace HB LorentzManifold.Model (.id B) A
    (SpinPullbackTargetComparisons.identityIso LM).classEquiv
      (SpinPullbackClasses.classMap (.id B) contMDiff_id LM c) = c := by
  let := chartedSpace HB LorentzManifold.Model (.id B) A
  exact Quotient.inductionOn c (fun S => Quotient.sound ⟨iso LM S⟩)

/-- Before identifying the targets, pullback by the identity already gives a bijection of physical classes. -/
theorem classMap_bijective : Function.Bijective (SpinPullbackClasses.classMap (.id B) contMDiff_id LM) := by
  let := chartedSpace HB LorentzManifold.Model (.id B) A
  let e := (SpinPullbackTargetComparisons.identityIso LM).classEquiv (I := IB)
  have h (c : PhysicalClass IB K A n) : SpinPullbackClasses.classMap (.id B) contMDiff_id LM c = e.symm c :=
    e.injective ((class_id LM c).trans (e.apply_symm_apply c).symm)
  rw [show SpinPullbackClasses.classMap (.id B) contMDiff_id LM = e.symm from funext h]
  exact e.symm.bijective

end FoliationQM.SpinPullbackIdentity
