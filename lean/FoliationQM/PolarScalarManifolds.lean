module
public import FoliationQM.PolarAmplitudeTopology
public import FoliationQM.PolarManifoldCharts
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Intrinsic open scalar factors of the polar source

Source: v13 `prop:takabayasi`. Positive real density and nonzero complex
amplitude retain their ordinary subtype topologies. Their inclusion charts
make them real manifolds of dimensions one and two. Smoothness into these
factors is equivalent to smoothness of the actual scalar coordinate, for
arbitrary manifold sources and arbitrary subsets. Positive square root and
logarithm are smooth on the density manifold, and complex reciprocal is
smooth on the nonzero-amplitude manifold. No global angle is selected.
-/

@[expose] public section
noncomputable section
open scoped Manifold
open Set Topology
namespace FoliationQM.PolarScalarManifolds
open PolarAmplitudeTopology

/-- Positive density is inhabited by the actual unit density. -/
instance instNonemptyPositiveDensity : Nonempty PositiveDensity := ⟨⟨1, by norm_num⟩⟩

/-- Nonzero complex amplitude is inhabited by the actual unit amplitude. -/
instance instNonemptyNonzeroComplex : Nonempty NonzeroComplex := ⟨⟨1, one_ne_zero⟩⟩

/-- The actual density inclusion is an open embedding in its natural subtype topology. -/
theorem isOpenEmbedding_density : IsOpenEmbedding (Subtype.val : PositiveDensity → ℝ) :=
  isOpen_Ioi.isOpenEmbedding_subtypeVal

/-- The actual amplitude inclusion is an open embedding in its natural subtype topology. -/
theorem isOpenEmbedding_amplitude : IsOpenEmbedding (Subtype.val : NonzeroComplex → ℂ) :=
  (isOpen_ne_fun continuous_id continuous_const).isOpenEmbedding_subtypeVal

/-- The positive-density atlas uses the actual real inclusion chart. -/
instance instChartedSpacePositiveDensity : ChartedSpace ℝ PositiveDensity :=
  isOpenEmbedding_density.singletonChartedSpace

/-- The nonzero-amplitude atlas uses the actual complex inclusion chart. -/
instance instChartedSpaceNonzeroComplex : ChartedSpace ℂ NonzeroComplex :=
  isOpenEmbedding_amplitude.singletonChartedSpace

/-- Positive density is a real manifold to every differentiability order. -/
instance instIsManifoldPositiveDensity (n : WithTop ℕ∞) : IsManifold 𝓘(ℝ, ℝ) n PositiveDensity :=
  isOpenEmbedding_density.isManifold_singleton

/-- Nonzero complex amplitude is a real manifold to every differentiability order. -/
instance instIsManifoldNonzeroComplex (n : WithTop ℕ∞) : IsManifold 𝓘(ℝ, ℂ) n NonzeroComplex :=
  isOpenEmbedding_amplitude.isManifold_singleton

/-- The positive-density model has one real degree of freedom. -/
theorem density_model_finrank : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ

/-- The nonzero-complex-amplitude model has two real degrees of freedom. -/
theorem amplitude_model_finrank : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex

/-- The actual density inclusion is manifold-smooth to every order. -/
theorem contMDiff_density_value (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n (Subtype.val : PositiveDensity → ℝ) :=
  contMDiff_isOpenEmbedding isOpenEmbedding_density

/-- The actual amplitude inclusion is manifold-smooth to every order. -/
theorem contMDiff_amplitude_value (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (Subtype.val : NonzeroComplex → ℂ) :=
  contMDiff_isOpenEmbedding isOpenEmbedding_amplitude

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {s : Set M} {x : M}

/-- Within any subset, a density field is manifold-smooth exactly when its actual real value is. -/
theorem contMDiffWithinAt_density_iff {f : M → PositiveDensity} :
    ContMDiffWithinAt I 𝓘(ℝ, ℝ) n f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, ℝ) n (fun y => (f y).val) s x :=
  PolarManifoldCharts.contMDiffWithinAt_iff_comp isOpenEmbedding_density

/-- At a point, density-field smoothness is exactly smoothness of the actual real coordinate. -/
theorem contMDiffAt_density_iff {f : M → PositiveDensity} :
    ContMDiffAt I 𝓘(ℝ, ℝ) n f x ↔ ContMDiffAt I 𝓘(ℝ, ℝ) n (fun y => (f y).val) x :=
  PolarManifoldCharts.contMDiffAt_iff_comp isOpenEmbedding_density

/-- Global density-field smoothness is exactly smoothness of the actual real coordinate. -/
theorem contMDiff_density_iff {f : M → PositiveDensity} :
    ContMDiff I 𝓘(ℝ, ℝ) n f ↔ ContMDiff I 𝓘(ℝ, ℝ) n (fun y => (f y).val) :=
  PolarManifoldCharts.contMDiff_iff_comp isOpenEmbedding_density

/-- On any subset, density-field smoothness is exactly smoothness of the actual real coordinate. -/
theorem contMDiffOn_density_iff {f : M → PositiveDensity} :
    ContMDiffOn I 𝓘(ℝ, ℝ) n f s ↔ ContMDiffOn I 𝓘(ℝ, ℝ) n (fun y => (f y).val) s :=
  PolarManifoldCharts.contMDiffOn_iff_comp isOpenEmbedding_density

/-- Within any subset, amplitude-field smoothness is exactly smoothness of the actual complex coordinate. -/
theorem contMDiffWithinAt_amplitude_iff {f : M → NonzeroComplex} :
    ContMDiffWithinAt I 𝓘(ℝ, ℂ) n f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, ℂ) n (fun y => (f y).val) s x :=
  PolarManifoldCharts.contMDiffWithinAt_iff_comp isOpenEmbedding_amplitude

/-- At a point, amplitude-field smoothness is exactly smoothness of the actual complex coordinate. -/
theorem contMDiffAt_amplitude_iff {f : M → NonzeroComplex} :
    ContMDiffAt I 𝓘(ℝ, ℂ) n f x ↔ ContMDiffAt I 𝓘(ℝ, ℂ) n (fun y => (f y).val) x :=
  PolarManifoldCharts.contMDiffAt_iff_comp isOpenEmbedding_amplitude

/-- Global amplitude-field smoothness is exactly smoothness of the actual complex coordinate. -/
theorem contMDiff_amplitude_iff {f : M → NonzeroComplex} :
    ContMDiff I 𝓘(ℝ, ℂ) n f ↔ ContMDiff I 𝓘(ℝ, ℂ) n (fun y => (f y).val) :=
  PolarManifoldCharts.contMDiff_iff_comp isOpenEmbedding_amplitude

/-- On any subset, amplitude-field smoothness is exactly smoothness of the actual complex coordinate. -/
theorem contMDiffOn_amplitude_iff {f : M → NonzeroComplex} :
    ContMDiffOn I 𝓘(ℝ, ℂ) n f s ↔ ContMDiffOn I 𝓘(ℝ, ℂ) n (fun y => (f y).val) s :=
  PolarManifoldCharts.contMDiffOn_iff_comp isOpenEmbedding_amplitude

/-- The positive square root is smooth on the intrinsic positive-density manifold. -/
theorem contMDiff_density_sqrt (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n (fun rho : PositiveDensity => Real.sqrt rho.val) := by
  intro rho
  exact (Real.contDiffAt_sqrt (ne_of_gt rho.property)).contMDiffAt.comp rho
    (contMDiff_density_value n).contMDiffAt

/-- The real logarithm is smooth on the intrinsic positive-density manifold. -/
theorem contMDiff_density_log (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n (fun rho : PositiveDensity => Real.log rho.val) := by
  intro rho
  exact (Real.contDiffAt_log.mpr (ne_of_gt rho.property)).contMDiffAt.comp rho
    (contMDiff_density_value n).contMDiffAt

/-- Actual complex reciprocal is smooth on the intrinsic nonzero-amplitude manifold. -/
theorem contMDiff_amplitude_inv (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (fun t : NonzeroComplex => t.val⁻¹) := by
  intro t
  exact (contDiffAt_id.inv t.property).contMDiffAt.comp t
    (contMDiff_amplitude_value n).contMDiffAt

end FoliationQM.PolarScalarManifolds
