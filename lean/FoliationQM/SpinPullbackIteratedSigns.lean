module
public import FoliationQM.SpinPullbackDisplacement

/-!
# Relative Spin signs under identity and repeated pullback

For the frame component of v13 `prop:takabayasi`, successive smooth base
changes and the composite construct different Lorentz fiber products.
Their physical relative signs nevertheless agree in the same all-cover
H¹ group on the last base. Neither a reference lift nor a choice of
normalized transition paths enters this comparison.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackIteratedSigns
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction
open GeometricPrincipalPullback SmoothPullbackChartedSpace SmoothPrincipalPullback
open GlobalSpinDisplacement SmoothSpinRelativeClass

universe u
variable {B X Y : Type u} {T ι EX EB EY ET HX HB HY HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace Y] [ChartedSpace HY Y] [TopologicalSpace T] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB}
  {IY : ModelWithCorners ℝ EY HY} {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞}
  {proj : T → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)

/-- Pulling two lifts back over the identity computes their original global relative sign. -/
theorem relative_id [IsManifold IB n B] (S U : SmoothLift IB K L n) :
    letI := chartedSpace HB LorentzManifold.Model (.id B) L
    relative (smoothAtlas (.id B) (contMDiff_id (I := IB)) LM)
      (GeometricSpinPullback.lift (.id B) contMDiff_id LM S)
      (GeometricSpinPullback.lift (.id B) contMDiff_id LM U) = relative LM S U := by
  let := chartedSpace HB LorentzManifold.Model (.id B) L
  exact (SpinPullbackDisplacement.relative_pullback (.id B) contMDiff_id LM S U).trans
    (SpinHOneGlobalPullback.pull_id _)

variable [IsManifold IX n X] [IsManifold IY n Y]
  (f : C(X, B)) (hf : ContMDiff IX IB n f) (g : C(Y, X)) (hg : ContMDiff IY IX n g)

/-- The relative sign of the two successive geometric pullbacks is the composite pullback of the original sign. -/
theorem relative_twice (S U : SmoothLift IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model f L
    letI := chartedSpace HY LorentzManifold.Model g (atlas f L)
    let FM := smoothAtlas f hf LM
    relative (smoothAtlas g hg FM)
      (GeometricSpinPullback.lift g hg FM (GeometricSpinPullback.lift f hf LM S))
      (GeometricSpinPullback.lift g hg FM (GeometricSpinPullback.lift f hf LM U)) =
        SpinHOneGlobalPullback.pull (f.comp g) (hf.comp hg) (relative LM S U) := by
  let := chartedSpace HX LorentzManifold.Model f L
  let := chartedSpace HY LorentzManifold.Model g (atlas f L)
  exact (SpinPullbackDisplacement.relative_pullback g hg (smoothAtlas f hf LM)
    (GeometricSpinPullback.lift f hf LM S) (GeometricSpinPullback.lift f hf LM U)).trans
    ((congrArg (SpinHOneGlobalPullback.pull g hg)
      (SpinPullbackDisplacement.relative_pullback f hf LM S U)).trans
      (SpinHOneGlobalPullback.pull_comp f hf g hg _))

/-- The successive and direct geometric constructions give the same relative sign on the last base. -/
theorem relative_twice_eq_direct (S U : SmoothLift IB K L n) :
    letI := chartedSpace HX LorentzManifold.Model f L
    letI := chartedSpace HY LorentzManifold.Model g (atlas f L)
    letI := chartedSpace HY LorentzManifold.Model (f.comp g) L
    let FM := smoothAtlas f hf LM
    relative (smoothAtlas g hg FM)
      (GeometricSpinPullback.lift g hg FM (GeometricSpinPullback.lift f hf LM S))
      (GeometricSpinPullback.lift g hg FM (GeometricSpinPullback.lift f hf LM U)) =
        relative (smoothAtlas (f.comp g) (hf.comp hg) LM)
          (GeometricSpinPullback.lift (f.comp g) (hf.comp hg) LM S)
          (GeometricSpinPullback.lift (f.comp g) (hf.comp hg) LM U) := by
  let := chartedSpace HX LorentzManifold.Model f L
  let := chartedSpace HY LorentzManifold.Model g (atlas f L)
  let := chartedSpace HY LorentzManifold.Model (f.comp g) L
  exact (relative_twice LM f hf g hg S U).trans
    (SpinPullbackDisplacement.relative_pullback (f.comp g) (hf.comp hg) LM S U).symm

end FoliationQM.SpinPullbackIteratedSigns
