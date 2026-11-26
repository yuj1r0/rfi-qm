module
public import FoliationQM.SpinPullbackIdentity
public import FoliationQM.SpinPullbackComposition

/-!
# Recovering a physical Spin class along a smooth section

For the frame component of v13 `prop:takabayasi`, a smooth right inverse
to the base map gives a left inverse on physical Spin classes. Pull back
along the section and then identify the two successive Lorentz targets.
This also reflects physical isomorphism of any two specified lifts.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackDescent
open LorentzMatrixGroup CliffordSpinLorentzSmooth GeometricSpinObstruction SmoothSpinRelativeClass
open GeometricPrincipalPullback SmoothPullbackChartedSpace SmoothPrincipalPullback

universe u
variable {X B : Type u} {T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T] {p : T → B} {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι}
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} [IsManifold IB n B] [IsManifold IX n X]
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K A n)

/-- Identify the physical target of an identity-valued base change with the original target. -/
def identifyId (k : C(B, B)) (he : k = .id B) :
    ConstructedPullbackSpinCriterion.Classes IB n k A ≃ PhysicalClass IB K A n := by
  subst k
  let := chartedSpace HB LorentzManifold.Model (.id B) A
  exact (SpinPullbackTargetComparisons.identityIso LM).classEquiv

/-- This identification cancels pullback along the identity-valued map. -/
theorem identifyId_pull (k : C(B, B)) (hk : ContMDiff IB IB n k) (he : k = .id B) (c : PhysicalClass IB K A n) :
    identifyId LM k he (SpinPullbackClasses.classMap k hk LM c) = c := by
  subst k
  exact SpinPullbackIdentity.class_id LM c

variable (f : C(X, B)) (s : C(B, X)) (hf : ContMDiff IX IB n f) (hs : ContMDiff IB IX n s)
  (hr : Function.RightInverse s f)

/-- Pull back along the section, flatten the targets, and identify the original Lorentz target. -/
def recover : ConstructedPullbackSpinCriterion.Classes IX n f A → PhysicalClass IB K A n :=
  letI := chartedSpace HX LorentzManifold.Model f A
  letI := chartedSpace HB LorentzManifold.Model s (atlas f A)
  letI := chartedSpace HB LorentzManifold.Model (f.comp s) A
  fun c => identifyId LM (f.comp s) (ContinuousMap.ext hr)
    ((SpinPullbackTargetComparisons.composeIso f s hf hs LM).classEquiv
      (SpinPullbackClasses.classMap s hs (smoothAtlas f hf LM) c))

/-- The section recovers every original class after smooth pullback. -/
theorem recover_leftInverse :
    Function.LeftInverse (recover LM f s hf hs hr) (SpinPullbackClasses.classMap f hf LM) := by
  let := chartedSpace HX LorentzManifold.Model f A
  let := chartedSpace HB LorentzManifold.Model s (atlas f A)
  let := chartedSpace HB LorentzManifold.Model (f.comp s) A
  intro c
  unfold recover
  rw [SpinPullbackComposition.classMap_comp_apply]
  exact identifyId_pull LM (f.comp s) (hf.comp hs) (ContinuousMap.ext hr) c

include s hs hr in
/-- A smooth right inverse makes pullback injective on all physical Spin classes. -/
theorem classMap_injective : Function.Injective (SpinPullbackClasses.classMap f hf LM) :=
  (recover_leftInverse LM f s hf hs hr).injective

include s hs hr in
/-- Two specified smooth lifts become physically isomorphic after split base change exactly when they were isomorphic originally. -/
theorem iso_iff (S V : SmoothLift IB K A n) :
    letI := chartedSpace HX LorentzManifold.Model f A
    Nonempty (SmoothBetween (GeometricSpinPullback.lift f hf LM S) (GeometricSpinPullback.lift f hf LM V)) ↔
      Nonempty (SmoothBetween S V) := by
  let := chartedSpace HX LorentzManifold.Model f A
  constructor
  · intro h
    have eq : SpinPullbackClasses.classMap f hf LM (physicalClass S) =
        SpinPullbackClasses.classMap f hf LM (physicalClass V) := Quotient.sound h
    exact Quotient.exact (classMap_injective LM f s hf hs hr eq)
  · rintro ⟨e⟩
    exact ⟨SpinPullbackClasses.iso f hf LM e⟩

end FoliationQM.SpinPullbackDescent
