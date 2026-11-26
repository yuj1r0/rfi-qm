module

public import FoliationQM.ClockProbeCubic
public import FoliationQM.FourthOrderTaylor

/-!
# Actual phase averaging of a fourth-order Taylor estimate

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`, and the
supplement's fourth-order refinement. Actual circle integrals remove the
cubic term and retain the quadratic trace. The final theorem derives the
remainder from actual C4 regularity and an actual fourth-derivative bound.
Application to the translated KL integral requires its separate weighted
spatial domination and boundary conditions.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ClockTaylorAverage

open ClockProbeLimit ClockProbeCovariance ClockProbeCubic Set
open scoped BigOperators

/-- The quadratic and cubic terms with the source Taylor coefficients. -/
def polynomial (H : Space →L[ℝ] Space →L[ℝ] ℝ)
    (T : Space [×3]→L[ℝ] ℝ) (a : Space) : ℝ := quadratic H a + cubic T a

/-- The finite Taylor polynomial is continuous. -/
theorem continuous_polynomial (H : Space →L[ℝ] Space →L[ℝ] ℝ)
    (T : Space [×3]→L[ℝ] ℝ) : Continuous (polynomial H T) :=
  (continuous_quadratic H).add (continuous_cubic T)

/-- The actual scaled quadratic phase average has the exact coordinate trace. -/
theorem average3_scaled_quadratic (ell ε : ℝ) (H : Space →L[ℝ] Space →L[ℝ] ℝ) :
    average3 (fun θ => quadratic H (ε • displacement ell θ)) =
      ε ^ 2 * ell ^ 2 / 4 * ∑ i : Fin 3, H (Pi.single i 1) (Pi.single i 1) := by
  simp_rw [quadratic_smul]
  rw [average3_const_mul, average3_quadratic]
  ring

/-- Genuine phase integration removes the cubic term of the finite Taylor polynomial. -/
theorem average3_polynomial (ell ε : ℝ) (H : Space →L[ℝ] Space →L[ℝ] ℝ)
    (T : Space [×3]→L[ℝ] ℝ) :
    average3 (fun θ => polynomial H T (ε • displacement ell θ)) =
      ε ^ 2 * ell ^ 2 / 4 * ∑ i : Fin 3, H (Pi.single i 1) (Pi.single i 1) := by
  have hq : Continuous (fun θ => quadratic H (ε • displacement ell θ)) := by
    simpa using! (continuous_quadratic H).comp ((continuous_displacement ell).const_smul ε)
  change average3 (fun θ => quadratic H (ε • displacement ell θ) +
    cubic T (ε • displacement ell θ)) = _
  rw [average3_add (iteratedIntegrable_of_continuous hq)
    (iteratedIntegrable_scaled_cubic ell ε T), average3_scaled_quadratic,
    average3_scaled_cubic, add_zero]

/-- A proved pointwise quartic error transfers through genuine phase averages.
This is an estimate-transfer lemma; no Taylor expansion is claimed by its hypotheses. -/
theorem norm_average3_sub_trace_le_of_remainder (ell ε : ℝ) (K : Space → ℝ)
    (H : Space →L[ℝ] Space →L[ℝ] ℝ) (T : Space [×3]→L[ℝ] ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hK : Continuous (fun θ => K (ε • displacement ell θ)))
    (hR : ∀ θ, ‖K (ε • displacement ell θ) -
      polynomial H T (ε • displacement ell θ)‖ ≤ C * ‖ε • displacement ell θ‖ ^ 4) :
    ‖average3 (fun θ => K (ε • displacement ell θ)) -
      ε ^ 2 * ell ^ 2 / 4 * ∑ i : Fin 3, H (Pi.single i 1) (Pi.single i 1)‖ ≤
      C * (ε ^ 4 * ell ^ 4) := by
  have hp : Continuous (fun θ => polynomial H T (ε • displacement ell θ)) := by
    simpa using! (continuous_polynomial H T).comp ((continuous_displacement ell).const_smul ε)
  rw [← average3_polynomial ell ε H T,
    ← average3_sub (iteratedIntegrable_of_continuous hK)
      (iteratedIntegrable_of_continuous hp)]
  apply norm_average3_le (by positivity)
  intro θ
  exact (hR θ).trans (mul_le_mul_of_nonneg_left
    (norm_scaled_displacement_pow_four_le ell ε θ) hC)

/-- Actual C4 regularity and a fourth-differential bound derive the averaged
quartic remainder, without a supplied Taylor expansion or odd-moment premise. -/
theorem norm_average3_sub_trace_le {K : Space → ℝ} (hK : ContDiff ℝ 4 K)
    (hzero : K 0 = 0) (hfirst : fderiv ℝ K 0 = 0) (ell ε : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hbound : ∀ θ t, t ∈ Icc (0 : ℝ) 1 →
      ‖iteratedFDeriv ℝ 4 K (t • (ε • displacement ell θ))‖ ≤ M) :
    ‖average3 (fun θ => K (ε • displacement ell θ)) -
      ε ^ 2 * ell ^ 2 / 4 * ∑ i : Fin 3,
        fderiv ℝ (fderiv ℝ K) 0 (Pi.single i 1) (Pi.single i 1)‖ ≤
      (M / 24) * (ε ^ 4 * ell ^ 4) := by
  apply norm_average3_sub_trace_le_of_remainder ell ε K
    (fderiv ℝ (fderiv ℝ K) 0) (iteratedFDeriv ℝ 3 K 0) (by positivity)
    (hK.continuous.comp ((continuous_displacement ell).const_smul ε))
  intro θ
  have ht := FourthOrderTaylor.norm_sub_cubic_le (g := K) 0
    (ε • displacement ell θ) (fun t _ => hK.contDiffAt)
    (fun t ht => by simpa only [zero_add] using hbound θ t ht)
  simpa only [FourthOrderTaylor.cubicPolynomial, zero_add, hzero, hfirst,
    zero_apply, zero_add, iteratedFDeriv_two_apply,
    polynomial, quadratic, cubic, div_mul_eq_mul_div] using ht

end FoliationQM.ClockTaylorAverage
