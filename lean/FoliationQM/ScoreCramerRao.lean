module

public import FoliationQM.CenteredL2Variance
public import FoliationQM.RealL2Pairing

/-!
# Sharp Cramér–Rao bounds from an actual score pairing

Sources: v13 eq:cramer_rao and thm:uncertainty. Kinds C and D.
These are genuine probability integrals of square-integrable real observables.
The centered score pairing is an explicit independent input. No Sobolev,
log-density derivative or quantum momentum identification is asserted here.
The exact residual square records the equality condition without assuming it.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ScoreCramerRao
open MeasureTheory Filter CenteredL2Variance

variable {α : Type*} [MeasurableSpace α]

/-- The actual affine-score residual uses the true centered observable and its variance. -/
def scoreResidual (μ : Measure α) (X score : α → ℝ) (x : α) : ℝ :=
  score x + centered μ X x / variance μ X

variable {μ : Measure α} [IsProbabilityMeasure μ] {X score : α → ℝ}

/-- The affine-score residual is genuinely square integrable. -/
theorem memLp_residual (hX : MemLp X 2 μ) (hs : MemLp score 2 μ) :
    MemLp (scoreResidual μ X score) 2 μ := by
  refine MemLp.ae_eq ?_ (hs.add ((memLp_centered μ hX).const_mul (variance μ X)⁻¹))
  exact Eventually.of_forall fun x => by
    simp only [Pi.add_apply, scoreResidual, div_eq_mul_inv]
    ring

/-- Its square is a genuine integrable real function. -/
theorem integrable_residual_sq (hX : MemLp X 2 μ) (hs : MemLp score 2 μ) :
    Integrable (fun x => scoreResidual μ X score x ^ 2) μ :=
  (memLp_residual hX hs).integrable_sq

/-- An actual centered pairing equal to minus one yields the Cramér–Rao product bound. -/
theorem cramer_rao (hX : MemLp X 2 μ) (hs : MemLp score 2 μ)
    (hpair : (∫ x, centered μ X x * score x ∂μ) = -1) :
    1 ≤ variance μ X * (∫ x, score x ^ 2 ∂μ) := by
  have h := RealL2Pairing.integral_mul_sq_le (memLp_centered μ hX) hs
  norm_num only [hpair, neg_sq, one_pow] at h
  exact h

/-- The nonzero score pairing forces strictly positive actual observable variance. -/
theorem variance_pos (hX : MemLp X 2 μ) (hs : MemLp score 2 μ)
    (hpair : (∫ x, centered μ X x * score x ∂μ) = -1) :
    0 < variance μ X := by
  apply RealL2Pairing.integral_sq_pos_of_pairing_ne_zero (memLp_centered μ hX) hs
  rw [hpair]
  norm_num

/-- Division by the variance is justified by the proved strict positivity. -/
theorem reciprocal_bound (hX : MemLp X 2 μ) (hs : MemLp score 2 μ)
    (hpair : (∫ x, centered μ X x * score x ∂μ) = -1) :
    1 / variance μ X ≤ ∫ x, score x ^ 2 ∂μ := by
  apply (div_le_iff₀ (variance_pos hX hs hpair)).mpr
  simpa only [mul_comm] using cramer_rao hX hs hpair

/-- The exact residual-square integral is the excess over the reciprocal variance. -/
theorem integral_residual_sq (hX : MemLp X 2 μ) (hs : MemLp score 2 μ)
    (hpair : (∫ x, centered μ X x * score x ∂μ) = -1) :
    (∫ x, scoreResidual μ X score x ^ 2 ∂μ) =
      (∫ x, score x ^ 2 ∂μ) - 1 / variance μ X := by
  have hV := (variance_pos hX hs hpair).ne'
  have hc : (∫ x, score x * centered μ X x ∂μ) = -1 := by
    simpa only [mul_comm] using hpair
  calc
    (∫ x, scoreResidual μ X score x ^ 2 ∂μ) =
        ∫ x, (score x + (variance μ X)⁻¹ * centered μ X x) ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [scoreResidual, div_eq_mul_inv]
        ring
    _ = (∫ x, score x ^ 2 ∂μ) + 2 * (variance μ X)⁻¹ * (-1) +
        ((variance μ X)⁻¹) ^ 2 * variance μ X := by
      rw [RealL2Pairing.integral_add_mul_sq hs (memLp_centered μ hX), hc]
      rfl
    _ = (∫ x, score x ^ 2 ∂μ) - 1 / variance μ X := by
      rw [show ((variance μ X)⁻¹) ^ 2 * variance μ X = (variance μ X)⁻¹ by
        rw [pow_two, mul_assoc, inv_mul_cancel₀ hV, mul_one]]
      simp only [one_div]
      ring

/-- The exact product gap is the positive variance times the genuine residual square. -/
theorem defect_eq_variance_mul_residual (hX : MemLp X 2 μ) (hs : MemLp score 2 μ)
    (hpair : (∫ x, centered μ X x * score x ∂μ) = -1) :
    variance μ X * (∫ x, score x ^ 2 ∂μ) - 1 =
      variance μ X * (∫ x, scoreResidual μ X score x ^ 2 ∂μ) := by
  rw [integral_residual_sq hX hs hpair, mul_sub, div_eq_mul_inv, one_mul,
    mul_inv_cancel₀ (variance_pos hX hs hpair).ne']

/-- Equality holds exactly when the score is the prescribed affine function almost everywhere. -/
theorem equality_iff (hX : MemLp X 2 μ) (hs : MemLp score 2 μ)
    (hpair : (∫ x, centered μ X x * score x ∂μ) = -1) :
    variance μ X * (∫ x, score x ^ 2 ∂μ) = 1 ↔
      ∀ᵐ x ∂μ, score x = -centered μ X x / variance μ X := by
  have hV := (variance_pos hX hs hpair).ne'
  have he : variance μ X * (∫ x, score x ^ 2 ∂μ) = 1 ↔
      (∫ x, scoreResidual μ X score x ^ 2 ∂μ) = 0 := by
    rw [integral_residual_sq hX hs hpair, sub_eq_zero]
    constructor
    · intro h
      apply (eq_div_iff hV).mpr
      simpa only [mul_comm] using h
    · intro h
      have h' : (∫ x, score x ^ 2 ∂μ) * variance μ X = 1 := (eq_div_iff hV).mp h
      simpa only [mul_comm] using h'
  rw [he, RealL2Pairing.integral_sq_eq_zero_iff (memLp_residual hX hs)]
  constructor
  · intro h
    filter_upwards [h] with x hx
    change score x + centered μ X x / variance μ X = 0 at hx
    simpa only [neg_div] using (add_eq_zero_iff_eq_neg.mp hx)
  · intro h
    filter_upwards [h] with x hx
    change score x + centered μ X x / variance μ X = 0
    rw [hx, neg_div, neg_add_cancel]

/-- Failure of the actual affine-score equality gives a strictly positive product gap. -/
theorem strict_gap_iff (hX : MemLp X 2 μ) (hs : MemLp score 2 μ)
    (hpair : (∫ x, centered μ X x * score x ∂μ) = -1) :
    1 < variance μ X * (∫ x, score x ^ 2 ∂μ) ↔
      ¬ (∀ᵐ x ∂μ, score x = -centered μ X x / variance μ X) := by
  constructor
  · intro hlt heq
    have h := (equality_iff hX hs hpair).mpr heq
    linarith
  · intro hne
    have hneq : variance μ X * (∫ x, score x ^ 2 ∂μ) ≠ 1 :=
      fun h => hne ((equality_iff hX hs hpair).mp h)
    exact lt_of_le_of_ne (cramer_rao hX hs hpair) hneq.symm

end FoliationQM.ScoreCramerRao
