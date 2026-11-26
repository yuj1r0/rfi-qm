module

public import FoliationQM.AdaptedChartWeakDerivative
public import FoliationQM.EmbeddedNodalCoordinates

/-!
# Local weak derivatives across an embedded nodal surface

Source: v13 `thm:wallstrom` Part(c), the distributional-derivative argument
following `eq:log_cutoff_l2_bound`, component kinds C and D. Every point of a
smoothly embedded surface in coordinate four-space has an open neighbourhood
such that, for smooth compact tests supported there, a field which is square
integrable with square-integrable classical directional derivative, and
differentiable only off the surface, satisfies the weak directional-derivative
identity across the surface. The neighbourhood is the source of the derived
adapted chart; no chart, nullity or cutoff estimate is a hypothesis.

This is local near each surface point and in ambient coordinates. Tests with
arbitrary compact support, Hilbert Sobolev membership and the wave equation
are separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.EmbeddedNodalWeakDerivative

open MeasureTheory Set Manifold RealLorentzFrame
open scoped ContDiff Topology Manifold

variable {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- Near each point of an embedded surface, off-surface differentiability with
square-integrable field and derivative gives the weak directional-derivative
identity for all smooth compact tests supported in a fixed open neighbourhood. -/
theorem exists_nhds_weak_directional_identity {f : S → Covector}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (s : S) :
    ∃ W : Set Covector, IsOpen W ∧ f s ∈ W ∧
      ∀ {φ ψ : Covector → ℂ} {U : Set Covector}, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ U → tsupport φ ⊆ W → MemLp ψ 2 (volume.restrict U) →
        (∀ x ∈ U \ range f, DifferentiableAt ℝ ψ x) → ∀ v : Covector,
        MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict U) →
        Integrable (fun x => star (fderiv ℝ φ x v) * ψ x) volume ∧
        Integrable (fun x => star (φ x) * fderiv ℝ ψ x v) volume ∧
        (∫ x, star (fderiv ℝ φ x v) * ψ x) = -(∫ x, star (φ x) * fderiv ℝ ψ x v) := by
  obtain ⟨e, hs, he, haxis⟩ := EmbeddedNodalCoordinates.exists_adapted_chart hf s
  refine ⟨e.source, e.open_source, hs, ?_⟩
  intro φ ψ U hφ hc hU hW hψ hdiff v hD
  exact AdaptedChartWeakDerivative.weak_directional_identity
    (contMDiffOn_of_mem_maximalAtlas he).contDiffOn
    (contMDiffOn_symm_of_mem_maximalAtlas he).contDiffOn hφ hc hU hW hψ
    (fun x hx hn => hdiff x ⟨hx.1, fun hr => hn ((haxis x hx.2).mp hr)⟩) v hD

end FoliationQM.EmbeddedNodalWeakDerivative
