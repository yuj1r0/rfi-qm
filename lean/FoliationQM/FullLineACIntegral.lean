module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Tactic.Ring

/-!
# Actual whole-line FTC and boundary decay for locally AC integrable functions

Sources: v13 thm:uncertainty, eq:cramer_rao and eq:p_var_decomp,
analytic component kinds C and D. Local absolute continuity supplies finite-
interval FTC with the actual almost-everywhere derivative. Genuine L¹
integrability of both the function and its derivative then forces both
endpoint limits to zero and the whole-line derivative integral to vanish.
Neither the boundary limits nor the final integral cancellation is an input.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.FullLineACIntegral
open MeasureTheory Filter Set
open scoped Topology

variable {f g : ℝ → ℝ}

/-- Local absolute continuity and the actual AE derivative give finite-interval FTC. -/
theorem interval_integral_eq_sub
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt f (g x) x) (a b : ℝ) :
    (∫ x in a..b, g x) = f b - f a := by
  calc
    (∫ x in a..b, g x) = ∫ x in a..b, deriv f x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hd] with x hx _
      exact hx.deriv.symm
    _ = f b - f a := (hAC a b).integral_deriv_eq_sub

/-- Genuine integrability of a locally AC function and its AE derivative forces its right limit to zero. -/
theorem tendsto_zero_atTop
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt f (g x) x)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    Tendsto f atTop (𝓝 0) := by
  have hp := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hg.integrableOn
    (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)
  have hl : Tendsto f atTop (𝓝 (f 0 + ∫ x in Ioi (0 : ℝ), g x)) := by
    convert (tendsto_const_nhds.add hp) using 1
    funext x
    rw [interval_integral_eq_sub hAC hd, id_eq]
    ring
  have hi : IntegrableAtFilter f atTop volume :=
    ⟨Ioi (0 : ℝ), Ioi_mem_atTop 0, hf.integrableOn⟩
  have hz : f 0 + ∫ x in Ioi (0 : ℝ), g x = 0 := by
    apply hi.eq_zero_of_tendsto ?_ hl
    intro s hs
    obtain ⟨b, hb⟩ := mem_atTop_sets.mp hs
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb
  rwa [hz] at hl

/-- The same actual AC and L¹ hypotheses force the left limit to zero. -/
theorem tendsto_zero_atBot
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt f (g x) x)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    Tendsto f atBot (𝓝 0) := by
  have hp := intervalIntegral_tendsto_integral_Iic (0 : ℝ) hg.integrableOn
    (tendsto_id : Tendsto (fun x : ℝ => x) atBot atBot)
  have hl : Tendsto f atBot (𝓝 (f 0 - ∫ x in Iic (0 : ℝ), g x)) := by
    convert (tendsto_const_nhds.sub hp) using 1
    funext x
    rw [interval_integral_eq_sub hAC hd, id_eq]
    ring
  have hi : IntegrableAtFilter f atBot volume :=
    ⟨Iic (0 : ℝ), Iic_mem_atBot 0, hf.integrableOn⟩
  have hz : f 0 - ∫ x in Iic (0 : ℝ), g x = 0 := by
    apply hi.eq_zero_of_tendsto ?_ hl
    intro s hs
    obtain ⟨b, hb⟩ := mem_atBot_sets.mp hs
    rw [← top_le_iff, ← Real.volume_Iic (a := b)]
    exact measure_mono hb
  rwa [hz] at hl

/-- The actual whole-line derivative integral vanishes by FTC and the proved zero endpoint limits. -/
theorem integral_eq_zero
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt f (g x) x)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x, g x) = 0 := by
  have hi := intervalIntegral_tendsto_integral hg tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)
  have hz : Tendsto (fun t : ℝ => ∫ x in -t..t, g x) atTop (𝓝 0) := by
    simpa only [interval_integral_eq_sub hAC hd, sub_zero, Function.comp_apply] using!
      (tendsto_zero_atTop hAC hd hf hg).sub
        ((tendsto_zero_atBot hAC hd hf hg).comp tendsto_neg_atTop_atBot)
  exact tendsto_nhds_unique hi hz

end FoliationQM.FullLineACIntegral
