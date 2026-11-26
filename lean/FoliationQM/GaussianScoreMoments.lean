module

public import FoliationQM.GaussianDensityScore
public import FoliationQM.ScoreCramerRao
public import FoliationQM.OsmoticScoreVariance

/-!
# Genuine Gaussian score moments and sharp Cramér–Rao equality

Sources: v13 `eq:cramer_rao`, `eq:p_var_decomp` and `thm:uncertainty`,
component kinds C and D. Mathlib's actual Gaussian probability measure
supplies the position moments. Its derived logarithmic density score
has genuine finite moments, centered pairing minus one, and sharp
Cramér–Rao equality. The Lebesgue-weighted moment results supply actual
integrability for the Gaussian wave construction. Positive variance is
explicit whenever the probability law is interpreted through its density.
These Gaussian witnesses leave the universal Sobolev and momentum bridges
as separate obligations.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianScoreMoments

open MeasureTheory ProbabilityTheory GaussianDensityScore
open scoped NNReal

/-- Position is genuinely square integrable under the actual Gaussian law. -/
theorem memLp_position (m : ℝ) (v : ℝ≥0) :
    MemLp (fun x : ℝ => x) 2 (gaussianReal m v) := by
  exact MemLp.ae_eq (Filter.Eventually.of_forall fun _ => rfl)
    (memLp_id_gaussianReal' (μ := m) (v := v) 2 (by norm_num))

/-- The actual position expectation equals the Gaussian mean parameter. -/
theorem mean_position (m : ℝ) (v : ℝ≥0) :
    CenteredL2Variance.mean (gaussianReal m v) (fun x : ℝ => x) = m :=
  integral_id_gaussianReal

/-- Actual centering subtracts the Gaussian mean. -/
theorem centered_position (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    CenteredL2Variance.centered (gaussianReal m v) (fun y : ℝ => y) x = x - m := by
  rw [CenteredL2Variance.centered, mean_position]

/-- The actual centered-square integral equals the Gaussian variance parameter. -/
theorem variance_position (m : ℝ) (v : ℝ≥0) :
    CenteredL2Variance.variance (gaussianReal m v) (fun x : ℝ => x) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := m) (v := v)
  rw [ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable] at h
  exact h

/-- The genuine uncentered second moment is variance plus squared mean. -/
theorem integral_position_sq (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal m v) = (v : ℝ) + m ^ 2 := by
  have h := CenteredL2Variance.variance_eq_integral_sq_sub_sq_mean
    (gaussianReal m v) (memLp_position m v)
  rw [variance_position, mean_position] at h
  linarith

private theorem score_eq_mul_centered (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    score m v x = (-1 / (v : ℝ)) *
      CenteredL2Variance.centered (gaussianReal m v) (fun y : ℝ => y) x := by
  rw [centered_position]
  simp only [score]
  ring

/-- The derived Gaussian log-score is genuinely square integrable. -/
theorem memLp_score (m : ℝ) (v : ℝ≥0) : MemLp (score m v) 2 (gaussianReal m v) := by
  have heq : score m v = fun x => (-1 / (v : ℝ)) *
      CenteredL2Variance.centered (gaussianReal m v) (fun y : ℝ => y) x :=
    funext (score_eq_mul_centered m v)
  rw [heq]
  exact (CenteredL2Variance.memLp_centered (gaussianReal m v) (memLp_position m v)).const_mul _

/-- Its actual expectation is zero. -/
theorem mean_score (m : ℝ) (v : ℝ≥0) :
    CenteredL2Variance.mean (gaussianReal m v) (score m v) = 0 := by
  unfold CenteredL2Variance.mean
  simp_rw [score_eq_mul_centered]
  rw [integral_const_mul,
    CenteredL2Variance.integral_centered (gaussianReal m v) (memLp_position m v), mul_zero]

/-- The actual score second moment is reciprocal variance for positive-width Gaussians. -/
theorem integral_score_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ x, score m v x ^ 2 ∂gaussianReal m v) = 1 / (v : ℝ) := by
  simp_rw [score_eq_mul_centered, mul_pow]
  rw [integral_const_mul]
  change (-1 / (v : ℝ)) ^ 2 *
    CenteredL2Variance.variance (gaussianReal m v) (fun x : ℝ => x) = _
  rw [variance_position]
  field_simp [NNReal.coe_ne_zero.mpr hv]

/-- The signed centered score pairing is genuinely integrable. -/
theorem integrable_centered_mul_score (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x =>
      CenteredL2Variance.centered (gaussianReal m v) (fun y : ℝ => y) x * score m v x)
      (gaussianReal m v) :=
  (CenteredL2Variance.memLp_centered (gaussianReal m v) (memLp_position m v)).integrable_mul
    (memLp_score m v)

/-- The actual Gaussian centered-score pairing is minus one. -/
theorem integral_centered_mul_score (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ x, CenteredL2Variance.centered (gaussianReal m v) (fun y : ℝ => y) x * score m v x
      ∂gaussianReal m v) = -1 := by
  have heq (x : ℝ) :
      CenteredL2Variance.centered (gaussianReal m v) (fun y : ℝ => y) x * score m v x =
        (-1 / (v : ℝ)) *
          CenteredL2Variance.centered (gaussianReal m v) (fun y : ℝ => y) x ^ 2 := by
    rw [score_eq_mul_centered]
    ring
  simp_rw [heq]
  rw [integral_const_mul]
  change (-1 / (v : ℝ)) *
    CenteredL2Variance.variance (gaussianReal m v) (fun x : ℝ => x) = -1
  rw [variance_position]
  field_simp [NNReal.coe_ne_zero.mpr hv]

/-- The actual Gaussian score realizes the equality case of the verified Cramér–Rao theorem. -/
theorem cramer_rao_saturation (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    CenteredL2Variance.variance (gaussianReal m v) (fun x : ℝ => x) *
      (∫ x, score m v x ^ 2 ∂gaussianReal m v) = 1 := by
  apply (ScoreCramerRao.equality_iff (memLp_position m v) (memLp_score m v)
    (integral_centered_mul_score m hv)).mpr
  exact Filter.Eventually.of_forall fun x => by
    rw [centered_position, variance_position]
    rfl

/-- The real osmotic observable has its exact Gaussian variance. -/
theorem osmotic_variance (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hbar : ℝ) :
    CenteredL2Variance.variance (gaussianReal m v)
      (OsmoticScoreVariance.observable hbar (score m v)) = hbar ^ 2 / (4 * (v : ℝ)) := by
  rw [OsmoticScoreVariance.variance_observable (gaussianReal m v)
    (memLp_score m v) hbar (mean_score m v), integral_score_sq m hv]
  ring

/-- The Lebesgue density-weighted position square is genuinely integrable. -/
theorem integrable_weighted_position_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x : ℝ => gaussianPDFReal m v x * x ^ 2) := by
  simpa only [smul_eq_mul] using
    (integrable_weighted_iff m hv).mp (memLp_position m v).integrable_sq

/-- The Lebesgue density-weighted score square is genuinely integrable. -/
theorem integrable_weighted_score_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => gaussianPDFReal m v x * score m v x ^ 2) := by
  simpa only [smul_eq_mul] using
    (integrable_weighted_iff m hv).mp (memLp_score m v).integrable_sq

/-- The density-weighted position second moment is the actual Gaussian second moment. -/
theorem integral_weighted_position_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ x : ℝ, gaussianPDFReal m v x * x ^ 2) = (v : ℝ) + m ^ 2 := by
  have h := integral_position_sq m v
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  exact h

/-- The density-weighted score second moment is the reciprocal variance. -/
theorem integral_weighted_score_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ x, gaussianPDFReal m v x * score m v x ^ 2) = 1 / (v : ℝ) := by
  have h := integral_score_sq m hv
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  exact h

end FoliationQM.GaussianScoreMoments
