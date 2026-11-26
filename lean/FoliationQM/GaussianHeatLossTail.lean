module

public import FoliationQM.GaussianRadialHeatLoss

/-!
# Exponential lower bound for the radial proper-time loss

In the initial positive-frequency Gaussian of v13 Theorem 5.8(ii), the
ratio of normal coefficient to amplitude loses a positive proper-time
contribution as the squared spatial radius grows. Restricting that contribution
to 1 ≤ t ≤ 2 gives a quantitative lower bound for every massive packet.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianHeatLossTail

open Set MeasureTheory Filter GaussianHeatProfile GaussianProperTimeMultiplier
open GaussianRadialHeatLoss

/-- The integral of the positive temporal weight over the fixed proper-time
interval [1,2]. It is independent of the spatial radius. -/
def windowWeight (μ a : ℝ) : ℝ :=
  ∫ t in Icc (1 : ℝ) 2, kernel μ t * massRatio a t

private theorem window_integrable (μ : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => kernel μ t * massRatio a t) (Icc (1 : ℝ) 2) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  intro t ht
  have hpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hat : 0 < a+t := add_pos ha hpos
  apply ContinuousAt.continuousWithinAt
  unfold kernel massRatio GaussianSpatialFourier.mass
  fun_prop (disch := first | positivity | exact Or.inl hpos.ne')

/-- Every positive-width Gaussian supplies strictly positive temporal weight
on the fixed interval [1,2]. -/
theorem windowWeight_pos (μ : ℝ) {a : ℝ} (ha : 0 < a) : 0 < windowWeight μ a := by
  let f := fun t => kernel μ t * massRatio a t
  have hpos (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) : 0 < f t := by
    have ht' : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    exact mul_pos (kernel_pos μ ht') (massRatio_pos ha ht')
  have hn : 0 ≤ᵐ[volume.restrict (Icc (1:ℝ) 2)] f := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht using (hpos t ht).le
  have hs : Function.support f ∩ Icc (1 : ℝ) 2 = Icc 1 2 :=
    inter_eq_right.mpr fun t ht => (hpos t ht).ne'
  change 0 < ∫ t in Icc (1 : ℝ) 2, f t
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn (window_integrable μ ha), hs, Real.volume_Icc]
  norm_num

/-- The entire proper-time loss at squared radius u≥0 is at least a positive
constant times exp(growthRate(a,1)u)−1. The restricted window controls all u. -/
theorem exp_lower_bound {μ a u : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hu : 0 ≤ u) :
    windowWeight μ a * (Real.exp (growthRate a 1*u)-1) ≤
      ∫ t in Ioi (0 : ℝ), kernel μ t * lossFactor a t u := by
  let f := fun t => kernel μ t * lossFactor a t u
  let B := Real.exp (growthRate a 1*u)-1
  have hsub : Icc (1 : ℝ) 2 ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le zero_lt_one ht.1
  have hi : IntegrableOn f (Ioi 0) := integrable_loss hμ ha hu
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] f := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact mul_nonneg (kernel_pos μ ht).le (lossFactor_nonneg ha ht hu)
  calc
    _ = ∫ t in Icc (1 : ℝ) 2, (kernel μ t * massRatio a t) * B := by
      rw [integral_mul_const]
      rfl
    _ ≤ ∫ t in Icc (1 : ℝ) 2, f t := by
      apply setIntegral_mono_on ((window_integrable μ ha).mul_const B) (hi.mono_set hsub) measurableSet_Icc
      intro t ht
      have ht' := hsub ht
      have hE : B ≤ Real.exp (growthRate a t*u)-1 :=
        sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          (growthRate_mono ha zero_le_one ht.1) hu)) 1
      change _ ≤ kernel μ t * (massRatio a t * _)
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hE (mul_nonneg (kernel_pos μ ht').le (massRatio_pos ha ht').le)
    _ ≤ _ := setIntegral_mono_set hi hn (ae_of_all _ hsub)

/-- Along every sequence or continuous parameter tending to infinite squared
radius, the integrated radial loss tends to positive infinity. -/
theorem tendsto_integral_loss_atTop {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    Tendsto (fun u : ℝ => ∫ t in Ioi (0 : ℝ), kernel μ t * lossFactor a t u) atTop atTop := by
  have he : Tendsto (fun u : ℝ => Real.exp (growthRate a 1*u)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (growthRate_pos ha zero_lt_one))
  have hs : Tendsto (fun u : ℝ => Real.exp (growthRate a 1*u)-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) he
  apply tendsto_atTop_mono' atTop ?_ (hs.const_mul_atTop (windowWeight_pos μ ha))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu using exp_lower_bound hμ ha hu

end FoliationQM.GaussianHeatLossTail
