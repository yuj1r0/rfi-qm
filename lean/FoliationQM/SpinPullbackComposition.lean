module
public import FoliationQM.SpinPullbackTargetComparisons
public import FoliationQM.SpinPullbackClasses

/-!
# Composition of pullbacks of smooth physical Spin lifts

For the frame component of v13 `prop:takabayasi`, successively pulling back
a physical lift gives a Spin bundle over a nested fiber product. Flattening
both the Spin and Lorentz coordinates compares it to the pullback along the
composite base map. This comparison gives equality on physical classes after
transport to the common Lorentz target.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackComposition
open GeometricPrincipalPullback SmoothPullbackChartedSpace SmoothPrincipalPullback
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction SmoothSpinRelativeClass

universe u
variable {Y X B : Type u} {T ι EY EX EB ET HY HX HB HT : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace Y] [ChartedSpace HY Y] [TopologicalSpace X] [ChartedSpace HX X]
  [TopologicalSpace B] [ChartedSpace HB B] [TopologicalSpace T] [ChartedSpace HT T]
  {IY : ModelWithCorners ℝ EY HY} {IX : ModelWithCorners ℝ EX HX}
  {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} [IsManifold IX n X] [IsManifold IY n Y]
  {proj : T → B} {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  (f : C(X, B)) (g : C(Y, X)) (hf : ContMDiff IX IB n f) (hg : ContMDiff IY IX n g)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K A n)

/-- Flattening the Spin space gives a physical isomorphism over the flattened Lorentz target. -/
def iso (S : SmoothLift IB K A n) :
    letI := chartedSpace HX LorentzManifold.Model f A
    letI := chartedSpace HY LorentzManifold.Model g (atlas f A)
    letI := chartedSpace HY LorentzManifold.Model (f.comp g) A
    SmoothBetween ((SpinPullbackTargetComparisons.composeIso f g hf hg LM).change
      (GeometricSpinPullback.lift g hg (smoothAtlas f hf LM) (GeometricSpinPullback.lift f hf LM S)))
      (GeometricSpinPullback.lift (f.comp g) (hf.comp hg) LM S) := by
  let := chartedSpace HX LorentzManifold.Model f A
  let := chartedSpace HY LorentzManifold.Model g (atlas f A)
  let := chartedSpace HY LorentzManifold.Model (f.comp g) A
  exact
    { diffeo := SmoothPullbackComparisons.compose f g hf hg S.smoothAtlas
      equivariant _ _ := rfl
      over _ := rfl }

/-- The forward physical comparison keeps the final base point and the original Spin frame. -/
theorem iso_apply (S : SmoothLift IB K A n) (z : Total g (projection f S.proj)) :
    ((iso f g hf hg LM S).diffeo z).val = (z.val.1, z.val.2.val.2) := rfl

/-- The inverse restores the intermediate base coordinate fixed by the second base map. -/
theorem iso_symm_apply (S : SmoothLift IB K A n) (z : Total (f.comp g) S.proj) :
    ((iso f g hf hg LM S).diffeo.symm z).val =
      (z.val.1, ⟨(g z.val.1, z.val.2), z.property⟩) := rfl

/-- Flattening intertwines both pullbacks of any physical isomorphism of the original lifts. -/
theorem iso_naturality {S U : SmoothLift IB K A n} (e : SmoothBetween S U)
    (z : Total g (projection f S.proj)) :
    letI := chartedSpace HX LorentzManifold.Model f A
    (iso f g hf hg LM U).diffeo
        ((SpinPullbackClasses.iso g hg (smoothAtlas f hf LM) (SpinPullbackClasses.iso f hf LM e)).diffeo z) =
      (SpinPullbackClasses.iso (f.comp g) (hf.comp hg) LM e).diffeo ((iso f g hf hg LM S).diffeo z) := rfl

/-- For each physical class the two successive pullbacks, transported by Lorentz
flattening, agree with the pullback along the composite base map. -/
theorem classMap_comp_apply (c : PhysicalClass IB K A n) :
    letI := chartedSpace HX LorentzManifold.Model f A
    letI := chartedSpace HY LorentzManifold.Model g (atlas f A)
    letI := chartedSpace HY LorentzManifold.Model (f.comp g) A
    (SpinPullbackTargetComparisons.composeIso f g hf hg LM).classEquiv
        (SpinPullbackClasses.classMap g hg (smoothAtlas f hf LM) (SpinPullbackClasses.classMap f hf LM c)) =
      SpinPullbackClasses.classMap (f.comp g) (hf.comp hg) LM c := by
  let := chartedSpace HX LorentzManifold.Model f A
  let := chartedSpace HY LorentzManifold.Model g (atlas f A)
  let := chartedSpace HY LorentzManifold.Model (f.comp g) A
  exact Quotient.inductionOn c (fun S => Quotient.sound ⟨iso f g hf hg LM S⟩)

/-- Composition holds as an equality of functions on physical Spin classes, with the
canonical comparison of Lorentz targets included. -/
theorem classMap_comp :
    letI := chartedSpace HX LorentzManifold.Model f A
    letI := chartedSpace HY LorentzManifold.Model g (atlas f A)
    letI := chartedSpace HY LorentzManifold.Model (f.comp g) A
    (SpinPullbackTargetComparisons.composeIso f g hf hg LM).classEquiv ∘
        SpinPullbackClasses.classMap g hg (smoothAtlas f hf LM) ∘ SpinPullbackClasses.classMap f hf LM =
      SpinPullbackClasses.classMap (f.comp g) (hf.comp hg) LM :=
  funext (classMap_comp_apply f g hf hg LM)

end FoliationQM.SpinPullbackComposition
