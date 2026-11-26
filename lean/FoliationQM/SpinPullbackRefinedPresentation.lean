module
public import FoliationQM.AnchoredAdaptedSpinPullback
public import FoliationQM.GlobalSpinPresentationFormula

/-!
# Physical comparison with the anchored pulled presentation

For the Spin-frame component of v13 `prop:takabayasi`, the original
adapted presentation and its anchored pullback use exactly the same
constructed smooth Spin fiber product. The identity physical
isomorphism identifies their global relative sign with the smooth
pullback of the original relative sign.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackRefinedPresentation
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
  [IsManifold IX n X] (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)
  (R : Refinement (domains L) B) (hm : ∀ b, b ∈ R.domain b)

/-- The two presentations of the actual pulled smooth lift are physically identical. -/
def iso (S : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    SmoothBetween (GeometricSpinPullback.lift f hf LM (ofRefined LM R S))
      (ofRefined (SmoothPrincipalPullback.smoothAtlas f hf LM)
        (AnchoredPullbackRefinement.refinement f R hm) (AnchoredAdaptedSpinPullback.lift f hf R hm S)) := by
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
  exact { diffeo := Diffeomorph.refl _ _ _, equivariant := fun _ _ => rfl, over := fun _ => rfl }

/-- The physical isomorphism fixes both coordinates of every pulled Spin point. -/
theorem iso_apply (S : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) (z : Total f S.proj) :
    (iso f hf LM R hm S).diffeo z = z := rfl

/-- The inverse presentation isomorphism also fixes every actual Spin point. -/
theorem iso_symm_apply (S : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) (z : Total f S.proj) :
    (iso f hf LM R hm S).diffeo.symm z = z := rfl

/-- The refined and anchored constructions represent the same pulled physical class. -/
theorem physicalClass_eq (S : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    physicalClass (GeometricSpinPullback.lift f hf LM (ofRefined LM R S)) =
      physicalClass (ofRefined (SmoothPrincipalPullback.smoothAtlas f hf LM)
        (AnchoredPullbackRefinement.refinement f R hm) (AnchoredAdaptedSpinPullback.lift f hf R hm S)) :=
  Quotient.sound ⟨iso f hf LM R hm S⟩

include hm in
/-- For supplied aligned adapted presentations, the actual global physical relative sign
commutes with smooth pullback. -/
theorem relative_pullback (hp : ∀ b, R.parent b = targetChart L b)
    (S U : GeometricSpinStructure.Lift IB (restrictedAtlas L R) n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
    GlobalSpinDisplacement.relative (SmoothPrincipalPullback.smoothAtlas f hf LM)
      (GeometricSpinPullback.lift f hf LM (ofRefined LM R S))
      (GeometricSpinPullback.lift f hf LM (ofRefined LM R U)) =
        SpinHOneGlobalPullback.pull f hf (GlobalSpinDisplacement.relative LM
          (ofRefined LM R S) (ofRefined LM R U)) := by
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
  rw [GlobalSpinDisplacement.relative_congr (SmoothPrincipalPullback.smoothAtlas f hf LM) ⟨iso f hf LM R hm S⟩ ⟨iso f hf LM R hm U⟩,
    GlobalSpinPresentationFormula.relative_ofRefined (SmoothPrincipalPullback.smoothAtlas f hf LM)
      (AnchoredPullbackRefinement.refinement f R hm)
      (AnchoredPullbackRefinement.aligned f L R hm hp)
      (AnchoredPullbackRefinement.mem_refinement f R hm)
      (AnchoredAdaptedSpinPullback.lift f hf R hm S) (AnchoredAdaptedSpinPullback.lift f hf R hm U),
    GlobalSpinPresentationFormula.relative_ofRefined LM R hp hm]
  exact AnchoredAdaptedSpinPullback.difference_global f hf R hm LM S U

end FoliationQM.SpinPullbackRefinedPresentation
