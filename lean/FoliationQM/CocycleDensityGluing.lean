module
public import FoliationQM.CocyclePolarFields

/-!
# Global smooth invariant density from compatible local polar fields

Source: the supplied-transition interpretation of v13 `prop:takabayasi`
and the positive invariant density in its polar decomposition. The input
is a compatible family of genuine smooth local fields on the actual
open domains of an independently supplied matrix transition cocycle.
The already proved matrix action leaves the positive density unchanged,
so local density coordinates agree on all overlaps.

A covering index defines a global positive-density value pointwise.
Exact agreement with every local chart is proved before any regularity
claim. The restriction of that global map to each open domain is then
exactly the local smooth density projection; the actual manifold
locality theorem gives global smoothness. No continuity or smoothness
of the selected index is assumed.

The global field is unique even among arbitrary positive-density maps
agreeing with the local values. Actual inverse polar realization gives
the corresponding construction for compatible regular-spinor families,
whose real scalar values are exactly their original bilinear invariant
densities. The resulting bundled smooth density is unique and commutes
with actual local realization. These statements glue an invariant scalar;
they do not select a global angle, frame representative, spacetime Spin
structure, or classification of arbitrary twisted bundles.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.CocycleDensityGluing
open PolarAmplitudeTopology PolarTransitionCocycle CocyclePolarFields

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  (D : PolarTransitionCocycle.Data I B ι n)

/-- The actual positive density obtained from any covering chart of a compatible local polar family. The chosen index is used only pointwise. -/
def polarDensity (f : SmoothPolarFamily D) (x : B) : PositiveDensity :=
  (f.val (indexAt D x) ⟨x, mem_domain_indexAt D x⟩).1

/-- The global positive density agrees with the actual local positive density in every chart containing the point. -/
theorem polarDensity_eq_local (f : SmoothPolarFamily D) (i : ι) (x : B)
    (hi : x ∈ D.domain i) :
    polarDensity D f x = (f.val i ⟨x, hi⟩).1 := by
  exact (polar_density_overlap D f (indexAt D x) i x (mem_domain_indexAt D x) hi).symm

/-- The glued positive density is genuinely globally smooth: on each actual open chart it is the first projection of the local smooth polar field. -/
theorem contMDiff_polarDensity (f : SmoothPolarFamily D) :
    ContMDiff I 𝓘(ℝ, ℝ) n (polarDensity D f) := by
  intro x
  obtain ⟨i, hi⟩ := D.covers x
  have he : (fun y : D.domain i => polarDensity D f y) =
      (fun y : D.domain i => (f.val i y).1) := by
    funext y
    exact polarDensity_eq_local D f i y y.property
  have hs : ContMDiff I 𝓘(ℝ, ℝ) n (fun y : D.domain i => polarDensity D f y) := by
    rw [he]
    exact (f.val i).contMDiff.fst
  exact contMDiffAt_subtype_iff.mp (hs ⟨x, hi⟩)

/-- Any globally defined positive-density map agreeing with every local chart is the constructed global density; no regularity premise on the competing map is needed. -/
theorem polarDensity_unique (f : SmoothPolarFamily D) (r : B → PositiveDensity)
    (hr : ∀ i (x : D.domain i), r x = (f.val i x).1) :
    r = polarDensity D f := by
  funext x
  obtain ⟨i, hi⟩ := D.covers x
  exact (hr i ⟨x, hi⟩).trans (polarDensity_eq_local D f i x hi).symm

/-- The actual globally glued density as a bundled smooth positive-density field. -/
def polarDensityField (f : SmoothPolarFamily D) :
    C^n⟮I, B; 𝓘(ℝ, ℝ), PositiveDensity⟯ :=
  ⟨polarDensity D f, contMDiff_polarDensity D f⟩

/-- A compatible smooth local polar family has exactly one global smooth positive-density field agreeing on all its charts. -/
theorem existsUnique_polarDensityField (f : SmoothPolarFamily D) :
    ∃! r : C^n⟮I, B; 𝓘(ℝ, ℝ), PositiveDensity⟯,
      ∀ i (x : D.domain i), r x = (f.val i x).1 := by
  refine ⟨polarDensityField D f, ?_, ?_⟩
  · intro i x
    exact polarDensity_eq_local D f i x x.property
  · intro r hr
    apply ContMDiffMap.ext
    intro x
    exact congrFun (polarDensity_unique D f r hr) x

/-- The positive invariant density of a compatible local regular-spinor family is obtained by genuine local inverse polar realization followed by the proved density gluing. -/
def spinorDensity (f : SmoothSpinorFamily D) : B → PositiveDensity :=
  polarDensity D ((realizationEquiv D).symm f)

/-- The global spinor density agrees with the positive density recovered from every actual local spinor. -/
theorem spinorDensity_eq_local (f : SmoothSpinorFamily D) (i : ι) (x : B)
    (hi : x ∈ D.domain i) :
    spinorDensity D f x = DensityFrameFields.density (f.val i ⟨x, hi⟩) := by
  rw [spinorDensity, polarDensity_eq_local D _ i x hi]
  rfl

/-- The real value of the glued spinor density is exactly the actual scalar/pseudoscalar invariant density of each local spinor, rather than an assumed overlap scalar. -/
theorem spinorDensity_value_eq_local (f : SmoothSpinorFamily D) (i : ι) (x : B)
    (hi : x ∈ D.domain i) :
    (spinorDensity D f x : ℝ) =
      SpinorRegularity.invariantDensity (f.val i ⟨x, hi⟩).val := by
  rw [spinorDensity_eq_local D f i x hi,
    DensityFrameFields.density_value_eq_invariantDensity]

/-- The actual glued invariant density of a compatible local regular-spinor family is globally smooth into the natural positive-density manifold. -/
theorem contMDiff_spinorDensity (f : SmoothSpinorFamily D) :
    ContMDiff I 𝓘(ℝ, ℝ) n (spinorDensity D f) :=
  contMDiff_polarDensity D ((realizationEquiv D).symm f)

/-- The actual real-valued global invariant density is smooth as an ordinary scalar-valued manifold function. -/
theorem contMDiff_spinorDensity_value (f : SmoothSpinorFamily D) :
    ContMDiff I 𝓘(ℝ, ℝ) n (fun x => (spinorDensity D f x : ℝ)) :=
  (PolarScalarManifolds.contMDiff_density_value n).comp (contMDiff_spinorDensity D f)

/-- The globally glued actual spinor invariant density as a bundled smooth positive-density field. -/
def spinorDensityField (f : SmoothSpinorFamily D) :
    C^n⟮I, B; 𝓘(ℝ, ℝ), PositiveDensity⟯ :=
  ⟨spinorDensity D f, contMDiff_spinorDensity D f⟩

/-- A positive-density map whose real value is the actual local spinor invariant in every chart is uniquely the glued density. -/
theorem spinorDensity_unique (f : SmoothSpinorFamily D) (r : B → PositiveDensity)
    (hr : ∀ i (x : D.domain i),
      (r x : ℝ) = SpinorRegularity.invariantDensity (f.val i x).val) :
    r = spinorDensity D f := by
  funext x
  obtain ⟨i, hi⟩ := D.covers x
  apply Subtype.ext
  exact (hr i ⟨x, hi⟩).trans (spinorDensity_value_eq_local D f i x hi).symm

/-- A compatible local regular-spinor family has exactly one global smooth positive-density field whose values equal the genuine local bilinear invariant densities. -/
theorem existsUnique_spinorDensityField (f : SmoothSpinorFamily D) :
    ∃! r : C^n⟮I, B; 𝓘(ℝ, ℝ), PositiveDensity⟯,
      ∀ i (x : D.domain i),
        (r x : ℝ) = SpinorRegularity.invariantDensity (f.val i x).val := by
  refine ⟨spinorDensityField D f, ?_, ?_⟩
  · intro i x
    exact spinorDensity_value_eq_local D f i x x.property
  · intro r hr
    apply ContMDiffMap.ext
    intro x
    exact congrFun (spinorDensity_unique D f r hr) x

/-- Realizing a compatible local polar family and gluing its actual spinor invariants gives the same global density as directly gluing its polar density coordinates. -/
theorem spinorDensity_realization (f : SmoothPolarFamily D) :
    spinorDensity D (realizationEquiv D f) = polarDensity D f := by
  simp only [spinorDensity, Equiv.symm_apply_apply]

end FoliationQM.CocycleDensityGluing
