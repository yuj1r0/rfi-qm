module
public import FoliationQM.CocyclePullback
public import FoliationQM.CocycleGaugeFamilies

/-!
# Actual smooth local-family pullback

Source: base-map naturality in the supplied-cocycle interpretation of
v13 `prop:takabayasi`. A compatible smooth local polar or represented-spinor
family pulls back by genuine bundled precomposition on the actual preimage
open chart domains. Its compatibility follows from the original independent
transition relation at the image point.

Actual local realization and inverse reconstruction commute with these maps.
The previously glued positive and original spinor invariant densities pull
back by ordinary composition with the supplied base map. Identity, successive
pullback, and local matrix frame-change squares are exact for the actual
cocycle and open-domain constructions. No invertibility or surjectivity of
the base map, global individual representative, or smooth chart-index
selection is assumed or asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CocyclePullbackFamilies
open DiracMatrices PolarSignQuotient SourcePolarProductQuotient
open CocyclePolarFields CocyclePullback

variable {E H E' H' B B' ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace B] [ChartedSpace H B]
  [TopologicalSpace B'] [ChartedSpace H' B'] {n : WithTop ℕ∞}
  (D : PolarTransitionCocycle.Data I B ι n) (f : C^n⟮J, B'; I, B⟯)

/-- Genuine pullback of a compatible smooth polar family is bundled precomposition on each actual preimage open domain; compatibility follows from the original actual transition relation. -/
def polarFamilyPullback (u : SmoothPolarFamily D) : SmoothPolarFamily (pullback D f) :=
  ⟨fun i => (u.val i).comp (localBaseMap D f i), by
    intro i j x hi hj
    exact u.property i j (f x) hi hj⟩

/-- Genuine pullback of a compatible smooth regular-spinor family uses the same actual local base maps and represented transition relation. -/
def spinorFamilyPullback (u : SmoothSpinorFamily D) : SmoothSpinorFamily (pullback D f) :=
  ⟨fun i => (u.val i).comp (localBaseMap D f i), by
    intro i j x hi hj
    exact u.property i j (f x) hi hj⟩

/-- Pulled polar coordinates evaluate at the actual base image in the original open chart. -/
theorem polarFamilyPullback_apply (u : SmoothPolarFamily D) (i : ι)
    (x : (pullback D f).domain i) :
    (polarFamilyPullback D f u).val i x = u.val i (localBaseMap D f i x) := rfl

/-- Pulled represented-spinor coordinates evaluate at the actual base image in the original chart. -/
theorem spinorFamilyPullback_apply (u : SmoothSpinorFamily D) (i : ι)
    (x : (pullback D f).domain i) :
    (spinorFamilyPullback D f u).val i x = u.val i (localBaseMap D f i x) := rfl

/-- Actual local-family polar realization commutes with pullback along an arbitrary bundled smooth base map. -/
theorem realization_commutes (u : SmoothPolarFamily D) :
    realizationEquiv (pullback D f) (polarFamilyPullback D f u) =
      spinorFamilyPullback D f (realizationEquiv D u) := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Actual inverse polar reconstruction commutes with pullback of compatible represented-spinor families. -/
theorem reconstruction_commutes (u : SmoothSpinorFamily D) :
    (realizationEquiv (pullback D f)).symm (spinorFamilyPullback D f u) =
      polarFamilyPullback D f ((realizationEquiv D).symm u) := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The globally glued positive density of a pulled family is exactly the original glued density composed with the actual base map. -/
theorem polarDensity_pullback (u : SmoothPolarFamily D) :
    CocycleDensityGluing.polarDensity (pullback D f) (polarFamilyPullback D f u) =
      CocycleDensityGluing.polarDensity D u ∘ f := rfl

/-- The globally glued actual spinor invariant density pulls back by composition with the same base map. -/
theorem spinorDensity_pullback (u : SmoothSpinorFamily D) :
    CocycleDensityGluing.spinorDensity (pullback D f) (spinorFamilyPullback D f u) =
      CocycleDensityGluing.spinorDensity D u ∘ f := rfl

/-- Pullback by the actual identity base map returns the same compatible polar family. -/
theorem polarFamilyPullback_id (u : SmoothPolarFamily D) :
    polarFamilyPullback D (ContMDiffMap.id : C^n⟮I, B; I, B⟯) u = u := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Pullback by the actual identity base map returns the same compatible represented-spinor family. -/
theorem spinorFamilyPullback_id (u : SmoothSpinorFamily D) :
    spinorFamilyPullback D (ContMDiffMap.id : C^n⟮I, B; I, B⟯) u = u := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  rfl

variable {E'' H'' B'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace B''] [ChartedSpace H'' B'']
  (g : C^n⟮K, B''; J, B'⟯)

/-- Successive actual polar-family pullbacks equal pullback along the genuine composed smooth base map. -/
theorem polarFamilyPullback_comp (u : SmoothPolarFamily D) :
    polarFamilyPullback (pullback D f) g (polarFamilyPullback D f u) =
      polarFamilyPullback D (f.comp g) u := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Successive actual represented-spinor pullbacks equal pullback along the composed smooth base map. -/
theorem spinorFamilyPullback_comp (u : SmoothSpinorFamily D) :
    spinorFamilyPullback (pullback D f) g (spinorFamilyPullback D f u) =
      spinorFamilyPullback D (f.comp g) u := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Pulling back an actual local matrix frame change and changing a polar family commutes exactly with changing that family first and then pulling it back. -/
theorem polar_gauge_commutes (h : CocycleGaugeTransform.FrameChange D)
    (u : SmoothPolarFamily D) :
    polarFamilyPullback (CocycleGaugeTransform.transformed D h) f
      (CocycleGaugeFamilies.polarFamilyEquiv D h u) =
    CocycleGaugeFamilies.polarFamilyEquiv (pullback D f) (pullbackFrameChange D f h)
      (polarFamilyPullback D f u) := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Pullback and actual represented local frame change commute for compatible spinor families with their genuinely transformed cocycles. -/
theorem spinor_gauge_commutes (h : CocycleGaugeTransform.FrameChange D)
    (u : SmoothSpinorFamily D) :
    spinorFamilyPullback (CocycleGaugeTransform.transformed D h) f
      (CocycleGaugeFamilies.spinorFamilyEquiv D h u) =
    CocycleGaugeFamilies.spinorFamilyEquiv (pullback D f) (pullbackFrameChange D f h)
      (spinorFamilyPullback D f u) := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  rfl

end FoliationQM.CocyclePullbackFamilies
