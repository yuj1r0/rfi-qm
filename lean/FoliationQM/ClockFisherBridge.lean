module

public import FoliationQM.ClockProbeCovariance
public import FoliationQM.FisherNormalization

/-!
# Actual probe covariance contracted with normalized spatial Fisher information

Sources: the second-to-third line of v13 `eq:kl_fisher_expansion` and the
normalization step in `thm:clock_sideband`. These are genuine covariance and
Fisher integrals, with density and diagonal Fisher integrability explicit.
No theorem here identifies the translated KL Hessian or its small-shift limit.
The spatial directions have a positive sum-of-squares contraction.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ClockFisherBridge

open MeasureTheory FisherNormalization ClockProbeCovariance
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- The matrix trace of genuinely integrable Fisher entries is the actual
positive spatial Fisher integral. -/
theorem trace_fisherMatrix (ρ : E → ℝ) (v : Fin 3 → E) (μ : Measure E)
    (hint : ∀ i, Integrable (matrixIntegrand ρ v i i) μ) :
    Matrix.trace (fisherMatrix ρ v μ) = fisherTrace ρ v μ := by
  exact (fisherTrace_eq_sum_diagonal ρ v μ hint).symm

/-- The actual Compton probe covariance contracts with an actual finite
spatial Fisher matrix to give the physical coefficient hbar squared over four. -/
theorem physical_fisher_contraction (p : MassiveParameters) (ρ : E → ℝ)
    (v : Fin 3 → E) (μ : Measure E)
    (hint : ∀ i, Integrable (matrixIntegrand ρ v i i) μ) :
    (p.m ^ 2 * p.c ^ 2 / 2) *
        (∑ i, ∑ j, covariance p.ellC i j * fisherMatrix ρ v μ i j) =
      p.hbar ^ 2 / 4 * fisherTrace ρ v μ := by
  calc
    _ = p.hbar ^ 2 / 4 * Matrix.trace (fisherMatrix ρ v μ) :=
      compton_fisher_coefficient p (fisherMatrix ρ v μ)
    _ = _ := by rw [trace_fisherMatrix ρ v μ hint]

/-- Combining actual score normalization with actual probe covariance yields
the unnormalized physical Fisher coefficient, before any KL-Hessian limit. -/
theorem normalized_physical_fisher_contraction (p : MassiveParameters)
    {ρ : E → ℝ} {Z : ℝ} (hρ : Differentiable ℝ ρ)
    (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z) (v : Fin 3 → E) (μ : Measure E)
    (hint : ∀ i, Integrable (matrixIntegrand ρ v i i) μ) :
    (Z * p.m ^ 2 * p.c ^ 2 / 2) *
        (∑ i, ∑ j, covariance p.ellC i j *
          fisherMatrix (normalizedDensity ρ Z) v μ i j) =
      p.hbar ^ 2 / 4 * fisherTrace ρ v μ := by
  have hn i := integrable_matrix_normalizedDensity hρ hpos hZ v μ i i (hint i)
  have ht := integrable_trace_of_diagonal ρ v μ hint
  calc
    _ = Z * ((p.m ^ 2 * p.c ^ 2 / 2) *
        (∑ i, ∑ j, covariance p.ellC i j *
          fisherMatrix (normalizedDensity ρ Z) v μ i j)) := by ring
    _ = Z * (p.hbar ^ 2 / 4 * fisherTrace (normalizedDensity ρ Z) v μ) := by
      rw [physical_fisher_contraction p _ v μ hn]
    _ = p.hbar ^ 2 / 4 * (Z * fisherTrace (normalizedDensity ρ Z) v μ) := by ring
    _ = _ := by rw [mass_mul_fisherTrace_normalizedDensity hρ hpos hZ v μ ht]

/-- With Z equal to the actual finite positive mass, the auxiliary density
has unit integral and its actual covariance-contracted Fisher matrix gives
the physical homogeneous functional. This does not assert a KL derivative. -/
theorem normalized_probability_and_fisher_coefficient (p : MassiveParameters)
    {ρ : E → ℝ} {Z : ℝ} (hρ : Differentiable ℝ ρ)
    (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z) (v : Fin 3 → E) (μ : Measure E)
    (hmassInt : Integrable ρ μ) (hmass : ∫ x, ρ x ∂μ = Z)
    (hint : ∀ i, Integrable (matrixIntegrand ρ v i i) μ) :
    (∫ x, normalizedDensity ρ Z x ∂μ) = 1 ∧
      (Z * p.m ^ 2 * p.c ^ 2 / 2) *
          (∑ i, ∑ j, covariance p.ellC i j *
            fisherMatrix (normalizedDensity ρ Z) v μ i j) =
        p.hbar ^ 2 / 4 * fisherTrace ρ v μ :=
  ⟨integral_normalizedDensity hmassInt hZ hmass,
    normalized_physical_fisher_contraction p hρ hpos hZ v μ hint⟩

end FoliationQM.ClockFisherBridge
