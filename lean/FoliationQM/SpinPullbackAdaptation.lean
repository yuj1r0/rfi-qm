module
public import FoliationQM.SpinPullbackClasses
public import FoliationQM.GlobalSpinDisplacement

/-!
# Physical pullback is independent of the chosen adapted presentation

For the Spin-frame component of v13 `prop:takabayasi`, changing the
principal charts of a smooth lift to a smaller adapted cover preserves
its original smooth carrier, right action and physical map. The identity
physical isomorphism therefore pulls back to the identity on actual
fiber-product points. This prepares comparison of transition signs for
independently charted original lifts.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackAdaptation
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction
open SmoothSpinRelativeClass JointSpinAdaptation CliffordSpinCoverRefinement
open RefinedGeometricPrincipalAtlas GeometricPrincipalPullback

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
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)
  (S : SmoothLift IB K L n) (R : Refinement (domains L) B)
  (hp : ∀ i, R.parent i = targetChart L i)
  (hs : ∀ i, (R.domain i : Set B) ⊆ neighborhood LM S i)

/-- Adaptation preserves the entire original physical structure by the identity diffeomorphism. -/
def adaptationIso : SmoothBetween S (ofRefined LM R (adaptOn LM S R hp hs)) where
  diffeo := Diffeomorph.refl _ _ _
  equivariant _ _ := rfl
  over _ := rfl

/-- The identity presentation isomorphism acts literally as the identity on the source. -/
theorem adaptationIso_apply (s : S.Carrier) :
    (adaptationIso LM S R hp hs).diffeo s = s := rfl

/-- The adapted presentation represents the same physical class. -/
theorem physicalClass_adaptOn :
    physicalClass S = physicalClass (ofRefined LM R (adaptOn LM S R hp hs)) :=
  Quotient.sound ⟨adaptationIso LM S R hp hs⟩

variable [IsManifold IX n X] (f : C(X, B)) (hf : ContMDiff IX IB n f)

/-- Changing the original adapted cover gives a genuine physical isomorphism of the two pulled lifts. -/
def pullIso :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    SmoothBetween (GeometricSpinPullback.lift f hf LM S)
      (GeometricSpinPullback.lift f hf LM (ofRefined LM R (adaptOn LM S R hp hs))) :=
  SpinPullbackClasses.iso f hf LM (adaptationIso LM S R hp hs)

/-- The pulled presentation isomorphism retains both original coordinates of every actual fiber-product point. -/
theorem pullIso_apply (z : Total f S.proj) :
    ((pullIso LM S R hp hs f hf).diffeo z).val = z.val := rfl

/-- The inverse physical presentation comparison also retains both coordinates. -/
theorem pullIso_symm_apply (z : Total f S.proj) :
    ((pullIso LM S R hp hs f hf).diffeo.symm z).val = z.val := rfl

/-- The two actual pulled presentations have the same physical class. -/
theorem pulledClass_adaptOn :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    physicalClass (GeometricSpinPullback.lift f hf LM S) =
      physicalClass (GeometricSpinPullback.lift f hf LM (ofRefined LM R (adaptOn LM S R hp hs))) :=
  Quotient.sound ⟨pullIso LM S R hp hs f hf⟩

end FoliationQM.SpinPullbackAdaptation
