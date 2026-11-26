module

public import FoliationQM.ObserverNormalizedShape

/-!
# Stability under uniform changes of the observer factor

V13 Remark 5.2 (line 520) compares densities after separate normalization.
On one measured slice, a factor within δ < 1 of unity yields an explicit
relative mass error and an L¹ estimate for the two unit-mass shapes. These
estimates require no differential regularity, even at zero-density sites.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverShapeStability

open MeasureTheory Filter ObserverNormalizedShape
open scoped Topology

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {ρ g : E → ℝ} {δ : ℝ}

/-- A measured density with uniformly bounded positive observer factor is integrable. -/
theorem integrable_observed (hρ : Integrable ρ μ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hg : AEMeasurable g μ) (hδ : δ < 1) (hclose : ∀ᵐ x ∂μ, |g x-1| ≤ δ) :
    Integrable (fun x => g x * ρ x) μ := by
  apply (hρ.const_mul (1+δ)).mono' (hg.mul hρ.aemeasurable).aestronglyMeasurable
  filter_upwards [hp, hclose] with x hx hi
  obtain ⟨hl, hu⟩ := abs_le.mp hi
  have hgp : 0 ≤ g x := by linarith
  change ‖g x*ρ x‖ ≤ (1+δ)*ρ x
  simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgp hx)]
  exact mul_le_mul_of_nonneg_right (by linarith) hx

/-- The observer's actual finite mass lies between the intrinsic mass multiplied
by 1−δ and by 1+δ. -/
theorem mass_bounds (hρ : Integrable ρ μ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hg : AEMeasurable g μ) (hδ : δ < 1) (hclose : ∀ᵐ x ∂μ, |g x-1| ≤ δ) :
    (1-δ)*mass μ ρ ≤ mass μ (fun x => g x*ρ x) ∧
      mass μ (fun x => g x*ρ x) ≤ (1+δ)*mass μ ρ := by
  have hi := integrable_observed hρ hp hg hδ hclose
  rw [← mass_const_mul μ ρ (1-δ), ← mass_const_mul μ ρ (1+δ)]
  constructor
  · apply integral_mono_ae (hρ.const_mul _) hi
    filter_upwards [hp, hclose] with x hx he
    exact mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp he).1]) hx
  · apply integral_mono_ae hi (hρ.const_mul _)
    filter_upwards [hp, hclose] with x hx he
    exact mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp he).2]) hx

/-- Absolute discrepancy between the two masses is at most δ times the intrinsic mass. -/
theorem mass_error (hρ : Integrable ρ μ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hg : AEMeasurable g μ) (hδ : δ < 1) (hclose : ∀ᵐ x ∂μ, |g x-1| ≤ δ) :
    |mass μ (fun x => g x*ρ x) - mass μ ρ| ≤ δ*mass μ ρ := by
  obtain ⟨hl,hu⟩ := mass_bounds hρ hp hg hδ hclose
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The Bochner integral of the absolute difference of the two separately normalized shapes
is at most 2δ/(1−δ) for a nonnegative density of positive finite mass. -/
theorem shape_l1_bound (hρ : Integrable ρ μ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hm : 0 < mass μ ρ) (hg : AEMeasurable g μ) (hδ₀ : 0 ≤ δ) (hδ : δ < 1)
    (hclose : ∀ᵐ x ∂μ, |g x-1| ≤ δ) :
    (∫ x, |shape μ (fun y => g y*ρ y) x - shape μ ρ x| ∂μ) ≤ 2*δ/(1-δ) := by
  let M := mass μ ρ
  let N := mass μ (fun x => g x*ρ x)
  change 0 < M at hm
  obtain ⟨hlo, hhi⟩ := mass_bounds hρ hp hg hδ hclose
  change (1-δ)*M ≤ N at hlo
  change N ≤ (1+δ)*M at hhi
  have hd : 0 < 1-δ := sub_pos.mpr hδ
  have hN : 0 < N := (mul_pos hd hm).trans_le hlo
  have hi := integrable_observed hρ hp hg hδ hclose
  have hS : Integrable (shape μ ρ) μ := hρ.div_const _
  have hT : Integrable (shape μ (fun x => g x*ρ x)) μ := hi.div_const _
  calc
    _ ≤ ∫ x, (2*δ/(1-δ)) * shape μ ρ x ∂μ := by
      apply integral_mono_ae (hT.sub hS).abs (hS.const_mul _)
      filter_upwards [hp, hclose] with x hx he
      have hl : 1-δ ≤ g x := by linarith [(abs_le.mp he).1]
      have hu : g x ≤ 1+δ := by linarith [(abs_le.mp he).2]
      have hab : |g x*M-N| ≤ 2*δ*M := by
        apply abs_le.mpr
        constructor
        · linarith [mul_le_mul_of_nonneg_right hl hm.le]
        · linarith [mul_le_mul_of_nonneg_right hu hm.le]
      have hratio : |g x*M-N|/N ≤ (2*δ)/(1-δ) := by
        refine ((div_le_div_iff₀ hN hd).2 ?_)
        calc
          _ ≤ (2*δ*M)*(1-δ) := mul_le_mul_of_nonneg_right hab hd.le
          _ = (2*δ)*((1-δ)*M) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
      change |g x * ρ x / N - ρ x / M| ≤ (2*δ/(1-δ))*(ρ x/M)
      rw [show g x*ρ x/N - ρ x/M = (g x*M-N)/N*(ρ x/M) by field_simp [hm.ne', hN.ne'],
        abs_mul, abs_div, abs_of_pos hN, abs_of_nonneg (div_nonneg hx hm.le)]
      exact mul_le_mul_of_nonneg_right hratio (div_nonneg hx hm.le)
    _ = _ := by rw [integral_const_mul, integral_shape μ ρ hρ hm, mul_one]

/-- If the spatially uniform almost-everywhere errors tend to zero along a parameter
filter, the actual L¹ distance of the normalized shapes tends to zero along that filter. -/
theorem shape_l1_tendsto {I : Type*} (l : Filter I) (G : I → E → ℝ) (d : I → ℝ)
    (hρ : Integrable ρ μ) (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x) (hm : 0 < mass μ ρ)
    (hd : Tendsto d l (𝓝 0))
    (hfamily : ∀ᶠ i in l, AEMeasurable (G i) μ ∧ 0 ≤ d i ∧
      ∀ᵐ x ∂μ, |G i x-1| ≤ d i) :
    Tendsto (fun i => ∫ x, |shape μ (fun y => G i y*ρ y) x - shape μ ρ x| ∂μ) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _) _
  · have ht := (hd.const_mul 2).div (tendsto_const_nhds.sub hd) (show (1 : ℝ)-0 ≠ 0 by norm_num)
    simpa only [mul_zero, zero_div, Pi.div_def] using ht
  · filter_upwards [hfamily, hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hi hu
    exact shape_l1_bound hρ hp hm hi.1 hi.2.1 hu hi.2.2

end FoliationQM.ObserverShapeStability
