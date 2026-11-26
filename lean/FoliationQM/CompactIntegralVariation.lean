module

public import FoliationQM.DressedVelocity
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Differentiating action integrals with compactly supported variations

Source: v13 `thm:kahler`, analytic support for the ordinary density/phase
variation. A derivative that is jointly continuous near parameter zero and
vanishes outside one compact spacetime set has a locally uniform integrable
bound. Thus differentiation under the actual Lebesgue integral follows from
compactness and the pointwise derivative, rather than an assumed interchange.
The spacetime domain here is the whole flat four-coordinate space.
-/
@[expose] public section

namespace FoliationQM.CompactIntegralVariation

open MeasureTheory Filter Set
open scoped Topology

private theorem continuous_slice {F : ℝ → Covector → ℝ} {s : Set ℝ}
    (hF : ContinuousOn (fun q : ℝ × Covector => F q.1 q.2) (s ×ˢ univ))
    {t : ℝ} (ht : t ∈ s) : Continuous (F t) := by
  apply continuousOn_univ.mp
  exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun x _ => ⟨ht, mem_univ x⟩)

/-- Joint continuity and one fixed compact support provide an integrable bound
for all derivative densities throughout a neighborhood of parameter zero. -/
theorem exists_integrable_bound {G : ℝ → Covector → ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 (0 : ℝ))
    (hG : ContinuousOn (fun q : ℝ × Covector => G q.1 q.2) (s ×ˢ univ))
    {K : Set Covector} (hK : IsCompact K)
    (hsupp : ∀ t ∈ s, ∀ x ∉ K, G t x = 0) :
    ∃ u ∈ 𝓝 (0 : ℝ), u ⊆ s ∧ ∃ B : Covector → ℝ,
      Integrable B ∧ ∀ t ∈ u, ∀ x, ‖G t x‖ ≤ B x := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  let u := Metric.closedBall (0 : ℝ) (ε / 2)
  have hu : u ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hεs
  have huc : IsCompact u := isCompact_closedBall _ _
  have hprod : u ×ˢ K ⊆ s ×ˢ (univ : Set Covector) := by
    intro q hq
    exact ⟨hu hq.1, mem_univ _⟩
  obtain ⟨C, hC⟩ := (huc.prod hK).exists_bound_of_continuousOn (hG.mono hprod)
  let B : Covector → ℝ := K.indicator (fun _ => max C 0)
  have hB : Integrable B := by
    exact (integrable_indicator_iff hK.measurableSet).mpr
      (continuous_const.continuousOn.integrableOn_compact hK)
  refine ⟨u, Metric.closedBall_mem_nhds _ (by positivity), hu, B, hB, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · exact (hC (t, x) ⟨ht, hx⟩).trans (by simp [B, hx])
  · simp [B, hx, hsupp t (hu ht) x hx]

/-- A jointly continuous actual derivative with common compact support may be
integrated to obtain the derivative of the genuine action integral. Only the
unperturbed density is assumed integrable; the domination is proved. -/
theorem hasDerivAt_integral_of_compact_support
    {F F' : ℝ → Covector → ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 (0 : ℝ))
    (hF : ContinuousOn (fun q : ℝ × Covector => F q.1 q.2) (s ×ˢ univ))
    (hF' : ContinuousOn (fun q : ℝ × Covector => F' q.1 q.2) (s ×ˢ univ))
    {K : Set Covector} (hK : IsCompact K)
    (hsupp : ∀ t ∈ s, ∀ x ∉ K, F' t x = 0)
    (hderiv : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => F r x) (F' t x) t)
    (hbase : Integrable (F 0)) :
    Integrable (F' 0) ∧
      HasDerivAt (fun t => ∫ x, F t x) (∫ x, F' 0 x) 0 := by
  obtain ⟨u, hu, hus, B, hB, hbound⟩ := exists_integrable_bound hs hF' hK hsupp
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := B) hu
  · filter_upwards [hs] with t ht
    exact (continuous_slice hF ht).aestronglyMeasurable
  · exact hbase
  · exact (continuous_slice hF' (mem_of_mem_nhds hs)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x t ht => hbound t ht x)
  · exact hB
  · exact Filter.Eventually.of_forall (fun x t ht => hderiv t (hus ht) x)

/-- If each perturbed density equals the base density outside a fixed compact
set, continuity and base integrability imply actual perturbed integrability. -/
theorem integrable_of_eq_outside_compact
    {F : ℝ → Covector → ℝ} {s : Set ℝ}
    (hF : ContinuousOn (fun q : ℝ × Covector => F q.1 q.2) (s ×ˢ univ))
    (hzero : (0 : ℝ) ∈ s) {K : Set Covector} (hK : IsCompact K)
    (hsupp : ∀ t ∈ s, ∀ x ∉ K, F t x = F 0 x)
    (hbase : Integrable (F 0)) {t : ℝ} (ht : t ∈ s) : Integrable (F t) := by
  have hcont : Continuous (fun x => F t x - F 0 x) :=
    (continuous_slice hF ht).sub (continuous_slice hF hzero)
  have hs : Function.support (fun x => F t x - F 0 x) ⊆ K := by
    intro x hx
    by_contra hn
    exact hx (by simp [hsupp t ht x hn])
  have hd : Integrable (fun x => F t x - F 0 x) :=
    (integrableOn_iff_integrable_of_support_subset hs).mp
      (hcont.continuousOn.integrableOn_compact hK)
  have heq : (fun x => F t x - F 0 x) + F 0 = F t := by
    funext x
    exact sub_add_cancel (F t x) (F 0 x)
  rw [← heq]
  exact hd.add hbase

end FoliationQM.CompactIntegralVariation
