module
public import FoliationQM.SpinPullbackAdaptation
public import FoliationQM.SpinPullbackRefinedPresentation

/-!
# Smooth pullback of the global relative Spin sign

For the Spin-frame component of v13 `prop:takabayasi`, two independently
charted lifts have a common adapted cover. Computing their sign on that
cover and pulling it back gives the geometric relative sign of their
actual pulled lifts. The same formula holds on physical isomorphism classes.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackDisplacement
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction
open SmoothSpinRelativeClass JointSpinAdaptation GlobalSpinDisplacement
open SmoothPrincipalPullback SmoothPullbackChartedSpace

universe u
variable {X B : Type u} {T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB}
  {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞} {proj : T → B}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  [IsManifold IX n X] (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)

/-- The global relative sign of arbitrary smooth physical lifts commutes with smooth pullback. -/
theorem relative_pullback (S U : SmoothLift IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model f L
    relative (smoothAtlas f hf LM) (GeometricSpinPullback.lift f hf LM S) (GeometricSpinPullback.lift f hf LM U) =
      SpinHOneGlobalPullback.pull f hf (relative LM S U) := by
  let := chartedSpace HX LorentzManifold.Model f L
  let R := common LM S U
  have hp (i) : R.parent i = targetChart L i := rfl
  have hs := common_subset_left LM S U
  have hu := common_subset_right LM S U
  refine (relative_congr (smoothAtlas f hf LM)
    ⟨SpinPullbackAdaptation.pullIso LM S R hp hs f hf⟩
    ⟨SpinPullbackAdaptation.pullIso LM U R hp hu f hf⟩).trans ?_
  refine (SpinPullbackRefinedPresentation.relative_pullback f hf LM R (mem_common LM S U) hp
    (leftLift LM S U) (rightLift LM S U)).trans ?_
  exact congrArg (SpinHOneGlobalPullback.pull f hf)
    (relative_congr LM ⟨SpinPullbackAdaptation.adaptationIso LM S R hp hs⟩
      ⟨SpinPullbackAdaptation.adaptationIso LM U R hp hu⟩).symm

/-- Pulling back the displacement between any two physical classes gives the displacement
between their images under the actual class map. -/
theorem displacement_pullback (p q : PhysicalClass IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model f L
    displacement (smoothAtlas f hf LM) (SpinPullbackClasses.classMap f hf LM p)
        (SpinPullbackClasses.classMap f hf LM q) =
      SpinHOneGlobalPullback.pull f hf (displacement LM p q) := by
  let := chartedSpace HX LorentzManifold.Model f L
  exact Quotient.inductionOn₂ p q (relative_pullback f hf LM)

/-- The two pulled smooth lifts are physically isomorphic precisely when pullback
takes their original relative sign to the group identity. -/
theorem nonempty_iff (S U : SmoothLift IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model f L
    Nonempty (SmoothBetween (GeometricSpinPullback.lift f hf LM S) (GeometricSpinPullback.lift f hf LM U)) ↔
      SpinHOneGlobalPullback.pull f hf (relative LM S U) = 1 := by
  let := chartedSpace HX LorentzManifold.Model f L
  rw [nonempty_iff_relative_one (smoothAtlas f hf LM), relative_pullback f hf LM]

end FoliationQM.SpinPullbackDisplacement
