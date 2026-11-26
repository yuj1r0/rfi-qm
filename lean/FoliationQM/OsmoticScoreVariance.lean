module

public import FoliationQM.CenteredL2Variance

/-!
# Actual variance of a mean-zero osmotic score observable

For v13 `eq:p_var_decomp` and `thm:uncertainty`, this proves the real
probability-integral component (component kinds C and D): the observable
`-(hbar / 2) * score` has variance `hbar^2 / 4` times the actual score
second moment when the actual score mean is zero. Square integrability
and the score mean are explicit inputs. Density differentiation, nodes,
and quantum momentum quadratic forms remain separate analytic bridges.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.OsmoticScoreVariance

open MeasureTheory CenteredL2Variance

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The real osmotic observable associated with a supplied score. -/
def observable (hbar : ℝ) (score : α → ℝ) (x : α) : ℝ := -(hbar / 2) * score x

variable {score : α → ℝ}

/-- A square-integrable score gives a square-integrable osmotic observable. -/
theorem memLp_observable (hs : MemLp score 2 μ) (hbar : ℝ) :
    MemLp (observable hbar score) 2 μ :=
  hs.const_mul _

/-- The score second moment in the variance formula is genuinely integrable. -/
theorem integrable_score_sq (hs : MemLp score 2 μ) :
    Integrable (fun x => score x ^ 2) μ := hs.integrable_sq

/-- Zero actual score mean implies zero actual osmotic mean. -/
theorem mean_observable (hbar : ℝ) (hmean : mean μ score = 0) :
    mean μ (observable hbar score) = 0 := by
  change mean μ (fun x => -(hbar / 2) * score x) = 0
  rw [mean_const_mul, hmean, mul_zero]

variable [IsProbabilityMeasure μ]

/-- The observable has a genuine first moment. -/
theorem integrable_observable (hs : MemLp score 2 μ) (hbar : ℝ) :
    Integrable (observable hbar score) μ :=
  CenteredL2Variance.integrable μ (memLp_observable μ hs hbar)

/-- The actual centered osmotic variance equals the scaled score second moment. -/
theorem variance_observable (hs : MemLp score 2 μ) (hbar : ℝ) (hmean : mean μ score = 0) :
    variance μ (observable hbar score) =
      hbar ^ 2 / 4 * (∫ x, score x ^ 2 ∂μ) := by
  rw [variance_eq_integral_sq_sub_sq_mean μ (memLp_observable μ hs hbar),
    mean_observable μ hbar hmean]
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, observable, mul_pow]
  rw [integral_const_mul]
  congr 1
  ring

/-- With nonzero hbar and zero score mean, zero osmotic variance is equivalent
to the score vanishing almost everywhere. -/
theorem variance_eq_zero_iff (hs : MemLp score 2 μ) {hbar : ℝ} (hhbar : hbar ≠ 0)
    (hmean : mean μ score = 0) :
    variance μ (observable hbar score) = 0 ↔ ∀ᵐ x ∂μ, score x = 0 := by
  rw [CenteredL2Variance.variance_eq_zero_iff μ (memLp_observable μ hs hbar),
    mean_observable μ hbar hmean]
  have hc : -(hbar / 2) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hhbar (by norm_num))
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact (mul_eq_zero.mp hx).resolve_left hc
  · intro h
    filter_upwards [h] with x hx
    simp [observable, hx]

/-- For positive hbar, a nonzero score on a set of positive probability
is exactly the condition for positive osmotic variance. -/
theorem variance_pos_iff (hs : MemLp score 2 μ) {hbar : ℝ} (hhbar : 0 < hbar)
    (hmean : mean μ score = 0) :
    0 < variance μ (observable hbar score) ↔ ¬ (∀ᵐ x ∂μ, score x = 0) := by
  rw [← variance_eq_zero_iff μ hs hhbar.ne' hmean]
  exact lt_iff_le_and_ne.trans
    (by simp [CenteredL2Variance.variance_nonneg μ (observable hbar score), ne_comm])

end FoliationQM.OsmoticScoreVariance
