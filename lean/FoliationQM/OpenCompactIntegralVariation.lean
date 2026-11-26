module

public import FoliationQM.CompactIntegralVariation

/-!
# Differentiating integrals on an open spacetime domain

Source: v13 `thm:kahler`, local analytic support for action variation.
Joint continuity is required only over the open spacetime domain. A common
compact derivative support contained in that domain supplies the integrable
bound for differentiation of the actual restricted Lebesgue integral.
No regularity or integrability is imposed outside the domain.
-/
@[expose] public section

namespace FoliationQM.OpenCompactIntegralVariation

open MeasureTheory Filter Set
open scoped Topology

private theorem continuousOn_slice {F : ℝ → Covector → ℝ}
    {s : Set ℝ} {U : Set Covector}
    (hF : ContinuousOn (fun q : ℝ × Covector => F q.1 q.2) (s ×ˢ U))
    {t : ℝ} (ht : t ∈ s) : ContinuousOn (F t) U := by
  exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hx => ⟨ht, hx⟩)

/-- Local joint continuity and one compact support inside the domain give a
uniform integrable bound for derivative densities near parameter zero. -/
theorem exists_integrable_bound {G : ℝ → Covector → ℝ}
    {s : Set ℝ} {U : Set Covector} (hs : s ∈ 𝓝 (0 : ℝ))
    (hG : ContinuousOn (fun q : ℝ × Covector => G q.1 q.2) (s ×ˢ U))
    {K : Set Covector} (hK : IsCompact K) (hKU : K ⊆ U)
    (hsupp : ∀ t ∈ s, ∀ x ∈ U, x ∉ K → G t x = 0) :
    ∃ u ∈ 𝓝 (0 : ℝ), u ⊆ s ∧ ∃ B : Covector → ℝ,
      Integrable B ∧ ∀ t ∈ u, ∀ x ∈ U, ‖G t x‖ ≤ B x := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  let u := Metric.closedBall (0 : ℝ) (ε / 2)
  have hu : u ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hεs
  have huc : IsCompact u := isCompact_closedBall _ _
  have hprod : u ×ˢ K ⊆ s ×ˢ U := by
    intro q hq
    exact ⟨hu hq.1, hKU hq.2⟩
  obtain ⟨C, hC⟩ := (huc.prod hK).exists_bound_of_continuousOn (hG.mono hprod)
  let B : Covector → ℝ := K.indicator (fun _ => max C 0)
  have hB : Integrable B := by
    exact (integrable_indicator_iff hK.measurableSet).mpr
      (continuous_const.continuousOn.integrableOn_compact hK)
  refine ⟨u, Metric.closedBall_mem_nhds _ (by positivity), hu, B, hB, ?_⟩
  intro t ht x hxU
  by_cases hx : x ∈ K
  · exact (hC (t, x) ⟨ht, hx⟩).trans (by simp [B, hx])
  · simp [B, hx, hsupp t (hu ht) x hxU hx]

/-- Differentiation under the actual integral restricted to an open domain.
The common compact support proves domination; neither regularity outside the
domain nor a preassigned integrable derivative bound is assumed. -/
theorem hasDerivAt_integral_of_compact_support
    {F F' : ℝ → Covector → ℝ} {s : Set ℝ} {U : Set Covector}
    (hU : IsOpen U) (hs : s ∈ 𝓝 (0 : ℝ))
    (hF : ContinuousOn (fun q : ℝ × Covector => F q.1 q.2) (s ×ˢ U))
    (hF' : ContinuousOn (fun q : ℝ × Covector => F' q.1 q.2) (s ×ˢ U))
    {K : Set Covector} (hK : IsCompact K) (hKU : K ⊆ U)
    (hsupp : ∀ t ∈ s, ∀ x ∈ U, x ∉ K → F' t x = 0)
    (hderiv : ∀ t ∈ s, ∀ x ∈ U, HasDerivAt (fun r => F r x) (F' t x) t)
    (hbase : IntegrableOn (F 0) U) :
    IntegrableOn (F' 0) U ∧
      HasDerivAt (fun t => ∫ x in U, F t x) (∫ x in U, F' 0 x) 0 := by
  obtain ⟨u, hu, hus, B, hB, hbound⟩ := exists_integrable_bound hs hF' hK hKU hsupp
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := B) hu
  · filter_upwards [hs] with t ht
    exact (continuousOn_slice hF ht).aestronglyMeasurable hU.measurableSet
  · exact hbase
  · exact (continuousOn_slice hF' (mem_of_mem_nhds hs)).aestronglyMeasurable
      hU.measurableSet
  · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact fun t ht => hbound t ht x hx
  · exact hB.restrict
  · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact fun t ht => hderiv t (hus ht) x hx

/-- When the density changes only on a compact subset of the domain, local
continuity and base integrability imply actual perturbed integrability. -/
theorem integrable_of_eq_outside_compact
    {F : ℝ → Covector → ℝ} {s : Set ℝ} {U : Set Covector}
    (hU : IsOpen U)
    (hF : ContinuousOn (fun q : ℝ × Covector => F q.1 q.2) (s ×ˢ U))
    (hzero : (0 : ℝ) ∈ s) {K : Set Covector} (hK : IsCompact K) (hKU : K ⊆ U)
    (hsupp : ∀ t ∈ s, ∀ x ∈ U, x ∉ K → F t x = F 0 x)
    (hbase : IntegrableOn (F 0) U) {t : ℝ} (ht : t ∈ s) :
    IntegrableOn (F t) U := by
  have hcont : ContinuousOn (fun x => F t x - F 0 x) K :=
    ((continuousOn_slice hF ht).sub (continuousOn_slice hF hzero)).mono hKU
  have hd : Integrable (K.indicator (fun x => F t x - F 0 x)) :=
    (integrable_indicator_iff hK.measurableSet).mpr (hcont.integrableOn_compact hK)
  have heq : EqOn (K.indicator (fun x => F t x - F 0 x))
      (fun x => F t x - F 0 x) U := by
    intro x hxU
    by_cases hx : x ∈ K
    · simp [hx]
    · simp [hx, hsupp t ht x hxU hx]
  have hdiff : IntegrableOn (fun x => F t x - F 0 x) U :=
    hd.integrableOn.congr_fun heq hU.measurableSet
  have hadd : (fun x => F t x - F 0 x) + F 0 = F t := by
    funext x
    exact sub_add_cancel (F t x) (F 0 x)
  rw [← hadd]
  exact hdiff.add hbase

end FoliationQM.OpenCompactIntegralVariation
