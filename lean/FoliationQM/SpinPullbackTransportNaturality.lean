module
public import FoliationQM.SpinPullbackTargetComparisons
public import FoliationQM.SpinPullbackClasses

/-!
# Pullback commutes with a smooth isomorphism of Lorentz targets

For the geometric frame component of v13 `prop:takabayasi`, composing a
physical map with an equivariant Lorentz diffeomorphism and pulling it
back gives the same physical class as first pulling back and then
transporting to the new pulled target. Both constructions act on the
same original Spin point.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackTransportNaturality
open LorentzMatrixGroup CliffordSpinLorentzSmooth GeometricSpinObstruction SmoothSpinRelativeClass
open GeometricPrincipalPullback SmoothPullbackChartedSpace SpinTargetTransport

universe u
variable {X B : Type u} {T U ι κ EX EB ET EU HX HB HT HU : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [NormedAddCommGroup EU] [NormedSpace ℝ EU] [TopologicalSpace HU]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T] [TopologicalSpace U] [ChartedSpace HU U]
  {p : T → B} {q : U → B} {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι}
  {D : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) q κ}
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB}
  {K : ModelWithCorners ℝ ET HT} {J : ModelWithCorners ℝ EU HU} {n : WithTop ℕ∞}
  [IsManifold IX n X] (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K A n)
  (NM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel J D n) (e : Iso K J A D n)

/-- The identity on the pulled Spin carrier is a physical isomorphism between the two orders of construction. -/
def iso (S : SmoothLift IB K A n) :
    letI := chartedSpace HX LorentzManifold.Model f A
    letI := chartedSpace HX LorentzManifold.Model f D
    SmoothBetween
      ((SpinPullbackTargetComparisons.pullIso f hf LM NM e).change (GeometricSpinPullback.lift f hf LM S))
      (GeometricSpinPullback.lift f hf NM (e.change S)) := by
  let := chartedSpace HX LorentzManifold.Model f A
  let := chartedSpace HX LorentzManifold.Model f D
  exact { diffeo := Diffeomorph.refl _ _ _
          equivariant := fun _ _ => rfl
          over := fun _ => rfl }

/-- The comparison acts as the identity on every original Spin point with its new base coordinate. -/
theorem iso_apply (S : SmoothLift IB K A n) (s : Total f S.proj) : (iso f hf LM NM e S).diffeo s = s := rfl

/-- The physical class square commutes for every smooth equivariant isomorphism of the Lorentz targets. -/
theorem class_square (c : PhysicalClass IB K A n) :
    letI := chartedSpace HX LorentzManifold.Model f A
    letI := chartedSpace HX LorentzManifold.Model f D
    (SpinPullbackTargetComparisons.pullIso f hf LM NM e).classEquiv (SpinPullbackClasses.classMap f hf LM c) =
      SpinPullbackClasses.classMap f hf NM (e.classEquiv c) := by
  let := chartedSpace HX LorentzManifold.Model f A
  let := chartedSpace HX LorentzManifold.Model f D
  exact Quotient.inductionOn c (fun S => Quotient.sound ⟨iso f hf LM NM e S⟩)

/-- Transport between targets preserves and reflects equality of pulled physical classes. -/
theorem class_eq_iff (c d : PhysicalClass IB K A n) :
    SpinPullbackClasses.classMap f hf NM (e.classEquiv c) = SpinPullbackClasses.classMap f hf NM (e.classEquiv d) ↔
      SpinPullbackClasses.classMap f hf LM c = SpinPullbackClasses.classMap f hf LM d := by
  let := chartedSpace HX LorentzManifold.Model f A
  let := chartedSpace HX LorentzManifold.Model f D
  rw [← class_square f hf LM NM e c, ← class_square f hf LM NM e d]
  exact (SpinPullbackTargetComparisons.pullIso f hf LM NM e).classEquiv.injective.eq_iff

end FoliationQM.SpinPullbackTransportNaturality
