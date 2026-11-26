module
public import FoliationQM.LocalPolarFields
public import FoliationQM.PolarManifoldCharts
public import FoliationQM.RegularPolarHomeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
/-!
# The natural eight-dimensional regular-spinor manifold

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. Strict invariant
regularity defines an actual open subset of the real eight-dimensional
spinor vector space. Its existing subtype topology carries the literal
inclusion chart. The chart range is exactly the strict regular domain,
and self-transitions give a manifold to every differentiability order.
Manifold smoothness into this space agrees with actual ambient real
calculus, including arbitrary within-set domains. No topology or
regularity condition is replaced by an unrelated construction.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold ContDiff
open Topology
namespace FoliationQM.RegularSpinorManifold
open DiracMatrices PolarSignQuotient
/-- The actual unit-amplitude identity-matrix datum supplies a strictly regular spinor. -/
instance instNonemptyRegularSpinor : Nonempty RegularSpinor :=
  ⟨realize ⟨1,1,one_ne_zero,by simp⟩⟩
/-- The actual inclusion of strictly regular spinors is an open embedding for its existing subtype topology. -/
theorem isOpenEmbedding_value : IsOpenEmbedding (Subtype.val : RegularSpinor → Spinor) :=
  LocalPolarFields.regularDomain_isOpen.isOpenEmbedding_subtypeVal
/-- Strictly regular spinors carry the literal ambient inclusion chart with their natural topology. -/
instance instChartedSpaceRegularSpinor : ChartedSpace Spinor RegularSpinor :=
  isOpenEmbedding_value.singletonChartedSpace
/-- The actual inclusion atlas is a real manifold to every differentiability order. -/
instance instIsManifoldRegularSpinor (n : ℕ∞ω) : IsManifold 𝓘(ℝ,Spinor) n RegularSpinor :=
  isOpenEmbedding_value.isManifold_singleton
/-- Every chosen regular-spinor chart evaluates to the actual underlying spinor. -/
theorem chartAt_value (p q : RegularSpinor) : chartAt Spinor p q = q.val := rfl
/-- The actual regular-spinor inclusion chart is defined on the whole regular subtype. -/
theorem chartAt_source (p : RegularSpinor) : (chartAt Spinor p).source = Set.univ := rfl
/-- The actual inclusion chart has precisely the strict invariant-regular spinor domain as its target. -/
theorem chartAt_target (p : RegularSpinor) :
    (chartAt Spinor p).target = {psi | SpinorRegularity.Regular psi} := by
  change (isOpenEmbedding_value.toOpenPartialHomeomorph (Subtype.val : RegularSpinor → Spinor)).target = _
  rw [isOpenEmbedding_value.toOpenPartialHomeomorph_target]
  exact Subtype.range_val
/-- The actual spinor model space has real dimension eight. -/
theorem model_finrank : Module.finrank ℝ Spinor = 8 := by
  simp [Spinor,Module.finrank_pi_fintype,Complex.finrank_real_complex]
/-- The actual ambient inclusion is manifold-smooth to every order. -/
theorem contMDiff_value (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ,Spinor) 𝓘(ℝ,Spinor) n (Subtype.val : RegularSpinor → Spinor) :=
  contMDiff_isOpenEmbedding isOpenEmbedding_value
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ∞ω} {f : E → RegularSpinor} {s : Set E} {x : E}
/-- Within any source set, manifold smoothness into regular spinors is exactly actual ambient real smoothness. -/
theorem contMDiffWithinAt_iff_value :
    ContMDiffWithinAt 𝓘(ℝ,E) 𝓘(ℝ,Spinor) n f s x ↔
      ContDiffWithinAt ℝ n (fun y => (f y).val) s x :=
  PolarManifoldCharts.contMDiffWithinAt_iff_contDiffWithinAt isOpenEmbedding_value
/-- Pointwise manifold smoothness into regular spinors is exactly actual ambient real smoothness. -/
theorem contMDiffAt_iff_value :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,Spinor) n f x ↔
      ContDiffAt ℝ n (fun y => (f y).val) x :=
  PolarManifoldCharts.contMDiffAt_iff_contDiffAt isOpenEmbedding_value
/-- Manifold smoothness on any source set is exactly actual ambient real smoothness of the underlying spinor field. -/
theorem contMDiffOn_iff_value :
    ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,Spinor) n f s ↔
      ContDiffOn ℝ n (fun y => (f y).val) s :=
  PolarManifoldCharts.contMDiffOn_iff_contDiffOn isOpenEmbedding_value
/-- Global manifold smoothness into regular spinors is exactly actual ambient real smoothness. -/
theorem contMDiff_iff_value :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,Spinor) n f ↔
      ContDiff ℝ n (fun y => (f y).val) :=
  PolarManifoldCharts.contMDiff_iff_contDiff isOpenEmbedding_value
end FoliationQM.RegularSpinorManifold
