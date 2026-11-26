module
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Explicit singleton-chart smoothness comparisons

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`, analytic
infrastructure for the existing natural regular-spinor and polar-quotient
topologies. An open embedding into a real normed space supplies a literal
single chart. Smoothness into that chart is equivalent to smoothness of
the actual embedding composition. The reverse implication uses the actual
partial inverse, smooth on the embedding's open range. These comparisons
apply to arbitrary source manifolds, with ordinary real calculus versions
for normed source spaces. No topology is redefined here.
-/

@[expose] public section
noncomputable section
open Function Set Topology
open scoped Manifold ContDiff
namespace FoliationQM.PolarManifoldCharts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {N : Type*} [TopologicalSpace N] [Nonempty N]
  {e : N → V} (h : IsOpenEmbedding e)
  {n : WithTop ℕ∞} {f : M → N} {s : Set M} {x : M}

/-- Within-set manifold smoothness in the actual singleton chart is exactly smoothness after its open embedding, for any source manifold. -/
theorem contMDiffWithinAt_iff_comp :
    let := h.singletonChartedSpace
    ContMDiffWithinAt I 𝓘(ℝ, V) n f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, V) n (e ∘ f) s x := by
  let := h.singletonChartedSpace
  constructor
  · intro hf
    exact (contMDiff_isOpenEmbedding (I := 𝓘(ℝ, V)) h).contMDiffAt.comp_contMDiffWithinAt x hf
  · intro hf
    have hi := (contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℝ, V)) (n := n) h)
      (e (f x)) (mem_range_self (f x))
    have hc := hi.comp x hf (fun y _ => mem_range_self (f y))
    have he : (h.toOpenPartialHomeomorph e).symm ∘ (e ∘ f) = f := by
      funext y
      exact h.toOpenPartialHomeomorph_left_inv e
    simpa only [he] using hc

/-- Pointwise manifold smoothness in the actual singleton chart is exactly smoothness after its open embedding. -/
theorem contMDiffAt_iff_comp :
    let := h.singletonChartedSpace
    ContMDiffAt I 𝓘(ℝ, V) n f x ↔
      ContMDiffAt I 𝓘(ℝ, V) n (e ∘ f) x := by
  let := h.singletonChartedSpace
  exact contMDiffWithinAt_iff_comp h (s := univ)

/-- Manifold smoothness on any set in the actual singleton chart is exactly smoothness after its open embedding. -/
theorem contMDiffOn_iff_comp :
    let := h.singletonChartedSpace
    ContMDiffOn I 𝓘(ℝ, V) n f s ↔
      ContMDiffOn I 𝓘(ℝ, V) n (e ∘ f) s := by
  let := h.singletonChartedSpace
  exact forall_congr' fun y => forall_congr' fun _ => contMDiffWithinAt_iff_comp h (x := y)

/-- Global manifold smoothness in the actual singleton chart is exactly smoothness after its open embedding. -/
theorem contMDiff_iff_comp :
    let := h.singletonChartedSpace
    ContMDiff I 𝓘(ℝ, V) n f ↔ ContMDiff I 𝓘(ℝ, V) n (e ∘ f) := by
  let := h.singletonChartedSpace
  exact forall_congr' fun y => contMDiffAt_iff_comp h (x := y)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {g : F → N} {t : Set F} {z : F}

/-- For a real normed source, within-set smoothness into the actual singleton chart agrees with ordinary real smoothness of its coordinate embedding. -/
theorem contMDiffWithinAt_iff_contDiffWithinAt :
    let := h.singletonChartedSpace
    ContMDiffWithinAt 𝓘(ℝ, F) 𝓘(ℝ, V) n g t z ↔
      ContDiffWithinAt ℝ n (e ∘ g) t z := by
  let := h.singletonChartedSpace
  exact (contMDiffWithinAt_iff_comp h).trans _root_.contMDiffWithinAt_iff_contDiffWithinAt

/-- For a real normed source, pointwise smoothness into the actual singleton chart agrees with ordinary real smoothness of its coordinate embedding. -/
theorem contMDiffAt_iff_contDiffAt :
    let := h.singletonChartedSpace
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, V) n g z ↔ ContDiffAt ℝ n (e ∘ g) z := by
  let := h.singletonChartedSpace
  exact (contMDiffAt_iff_comp h).trans _root_.contMDiffAt_iff_contDiffAt

/-- For a real normed source, smoothness on any set into the actual singleton chart agrees with ordinary real smoothness of its coordinate embedding. -/
theorem contMDiffOn_iff_contDiffOn :
    let := h.singletonChartedSpace
    ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, V) n g t ↔ ContDiffOn ℝ n (e ∘ g) t := by
  let := h.singletonChartedSpace
  exact (contMDiffOn_iff_comp h).trans _root_.contMDiffOn_iff_contDiffOn

/-- For a real normed source, global smoothness into the actual singleton chart agrees with ordinary real smoothness of its coordinate embedding. -/
theorem contMDiff_iff_contDiff :
    let := h.singletonChartedSpace
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, V) n g ↔ ContDiff ℝ n (e ∘ g) := by
  let := h.singletonChartedSpace
  exact (contMDiff_iff_comp h).trans _root_.contMDiff_iff_contDiff

end FoliationQM.PolarManifoldCharts
