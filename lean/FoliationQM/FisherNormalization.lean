module

public import FoliationQM.PolarDifferential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Spatial score and Fisher normalization at a fixed observer time

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`, and the supplement's
normalized auxiliary-density construction. The positive normalization Z is
constant in the spatial variable. Actual real derivatives and actual integrals
give the score and homogeneous Fisher identities. Integrability is explicit;
no translated KL Hessian or time-dependent rescaling of the physical field is
asserted. The finite sum of squared spatial scores has positive signs only.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.FisherNormalization

open MeasureTheory
open scoped BigOperators

variable {E : Type*}

/-- Only the auxiliary probability density is divided by its spatial mass. -/
def normalizedDensity (ρ : E → ℝ) (Z : ℝ) (x : E) : ℝ := ρ x / Z

/-- Positive density and a positive spatial mass give a positive auxiliary density. -/
theorem normalizedDensity_pos (ρ : E → ℝ) {Z : ℝ} (hZ : 0 < Z) {x : E}
    (hρ : 0 < ρ x) : 0 < normalizedDensity ρ Z x := div_pos hρ hZ

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual spatial directional score, using the Fréchet derivative of log density. -/
def score (ρ : E → ℝ) (x v : E) : ℝ :=
  fderiv ℝ (fun y => Real.log (ρ y)) x v

/-- The actual score is the density derivative divided by positive density. -/
theorem score_eq {ρ : E → ℝ} {x : E} (hρ : DifferentiableAt ℝ ρ x)
    (hpos : 0 < ρ x) (v : E) : score ρ x v = fderiv ℝ ρ x v / ρ x :=
  PolarDifferential.fderiv_log_density_apply hρ hpos v

/-- Normalization by a spatial constant preserves actual differentiability. -/
theorem differentiableAt_normalizedDensity {ρ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (Z : ℝ) :
    DifferentiableAt ℝ (normalizedDensity ρ Z) x := by
  change DifferentiableAt ℝ (fun y => ρ y / Z) x
  simpa only [div_eq_mul_inv] using hρ.mul_const Z⁻¹

/-- The actual derivative of the normalized auxiliary density has its expected scale. -/
theorem fderiv_normalizedDensity {ρ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (Z : ℝ) (v : E) :
    fderiv ℝ (normalizedDensity ρ Z) x v = fderiv ℝ ρ x v / Z := by
  change fderiv ℝ (fun y => ρ y / Z) x v = fderiv ℝ ρ x v / Z
  simp only [div_eq_mul_inv, fderiv_mul_const hρ, smul_apply, smul_eq_mul]
  ring

/-- The spatial score is unchanged by normalizing only the auxiliary density. -/
theorem score_normalizedDensity {ρ : E → ℝ} {x : E} {Z : ℝ}
    (hρ : DifferentiableAt ℝ ρ x) (hpos : 0 < ρ x) (hZ : 0 < Z) (v : E) :
    score (normalizedDensity ρ Z) x v = score ρ x v := by
  rw [score_eq (differentiableAt_normalizedDensity hρ Z)
      (normalizedDensity_pos ρ hZ hpos), score_eq hρ hpos,
    fderiv_normalizedDensity hρ, normalizedDensity]
  field_simp

/-- The literal spatial Fisher-matrix integrand for supplied tangent directions. -/
def matrixIntegrand {n : ℕ} (ρ : E → ℝ) (v : Fin n → E) (i j : Fin n) (x : E) : ℝ :=
  ρ x * score ρ x (v i) * score ρ x (v j)

/-- The positive spatial Fisher trace integrand uses a sum of squares,
distinct from the signed Lorentzian action contraction. -/
def traceIntegrand {n : ℕ} (ρ : E → ℝ) (v : Fin n → E) (x : E) : ℝ :=
  ρ x * ∑ i, (score ρ x (v i)) ^ 2

/-- The spatial Fisher trace integrand is nonnegative for nonnegative density. -/
theorem traceIntegrand_nonneg {n : ℕ} (ρ : E → ℝ) (v : Fin n → E) {x : E}
    (hρ : 0 ≤ ρ x) : 0 ≤ traceIntegrand ρ v x := by
  exact mul_nonneg hρ (Finset.sum_nonneg (fun i _ => sq_nonneg _))

/-- The positive trace integrand is exactly the sum of the diagonal matrix entries. -/
theorem traceIntegrand_eq_sum {n : ℕ} (ρ : E → ℝ) (v : Fin n → E) (x : E) :
    traceIntegrand ρ v x = ∑ i, matrixIntegrand ρ v i i x := by
  simp only [traceIntegrand, matrixIntegrand, pow_two, Finset.mul_sum, mul_assoc]

/-- Actual score invariance gives the Fisher-matrix integrand normalization. -/
theorem matrixIntegrand_normalizedDensity {n : ℕ} {ρ : E → ℝ} {x : E} {Z : ℝ}
    (hρ : DifferentiableAt ℝ ρ x) (hpos : 0 < ρ x) (hZ : 0 < Z)
    (v : Fin n → E) (i j : Fin n) :
    matrixIntegrand (normalizedDensity ρ Z) v i j x = matrixIntegrand ρ v i j x / Z := by
  simp only [matrixIntegrand, score_normalizedDensity hρ hpos hZ, normalizedDensity]
  ring

/-- The spatial Fisher trace has the same exact pointwise normalization. -/
theorem traceIntegrand_normalizedDensity {n : ℕ} {ρ : E → ℝ} {x : E} {Z : ℝ}
    (hρ : DifferentiableAt ℝ ρ x) (hpos : 0 < ρ x) (hZ : 0 < Z) (v : Fin n → E) :
    traceIntegrand (normalizedDensity ρ Z) v x = traceIntegrand ρ v x / Z := by
  simp only [traceIntegrand, score_normalizedDensity hρ hpos hZ, normalizedDensity]
  ring

variable [MeasurableSpace E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A genuinely integrable density remains integrable after constant normalization. -/
theorem integrable_normalizedDensity {ρ : E → ℝ} {μ : Measure E}
    (hρ : Integrable ρ μ) (Z : ℝ) : Integrable (normalizedDensity ρ Z) μ := hρ.div_const Z

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- At a fixed observer time, dividing by the actual finite positive spatial
integral produces total probability mass one. -/
theorem integral_normalizedDensity {ρ : E → ℝ} {μ : Measure E} {Z : ℝ}
    (hρ : Integrable ρ μ) (hZ : 0 < Z) (hmass : ∫ x, ρ x ∂μ = Z) :
    (∫ x, normalizedDensity ρ Z x ∂μ) = 1 := by
  have _ := integrable_normalizedDensity hρ Z
  change (∫ x, ρ x / Z ∂μ) = 1
  rw [integral_div, hmass, div_self hZ.ne']

/-- The actual spatial Fisher matrix entry. Integrability is established
explicitly in each finite-Fisher application below. -/
def fisherMatrix {n : ℕ} (ρ : E → ℝ) (v : Fin n → E) (μ : Measure E)
    (i j : Fin n) : ℝ := ∫ x, matrixIntegrand ρ v i j x ∂μ

/-- The actual positive spatial Fisher trace integral. -/
def fisherTrace {n : ℕ} (ρ : E → ℝ) (v : Fin n → E) (μ : Measure E) : ℝ :=
  ∫ x, traceIntegrand ρ v x ∂μ

/-- Finite physical Fisher matrix entries give genuinely integrable auxiliary entries. -/
theorem integrable_matrix_normalizedDensity {n : ℕ} {ρ : E → ℝ} {Z : ℝ}
    (hρ : Differentiable ℝ ρ) (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z)
    (v : Fin n → E) (μ : Measure E) (i j : Fin n)
    (hint : Integrable (matrixIntegrand ρ v i j) μ) :
    Integrable (matrixIntegrand (normalizedDensity ρ Z) v i j) μ := by
  have he : matrixIntegrand (normalizedDensity ρ Z) v i j =
      fun x => matrixIntegrand ρ v i j x / Z := by
    funext x
    exact matrixIntegrand_normalizedDensity (hρ x) (hpos x) hZ v i j
  rw [he]
  exact hint.div_const Z

/-- The auxiliary Fisher matrix is exactly the physical homogeneous matrix divided by Z. -/
theorem fisherMatrix_normalizedDensity {n : ℕ} {ρ : E → ℝ} {Z : ℝ}
    (hρ : Differentiable ℝ ρ) (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z)
    (v : Fin n → E) (μ : Measure E) (i j : Fin n)
    (hint : Integrable (matrixIntegrand ρ v i j) μ) :
    fisherMatrix (normalizedDensity ρ Z) v μ i j = fisherMatrix ρ v μ i j / Z := by
  have _ := integrable_matrix_normalizedDensity hρ hpos hZ v μ i j hint
  simp only [fisherMatrix, matrixIntegrand_normalizedDensity (hρ _) (hpos _) hZ]
  exact integral_div Z _

/-- Finite physical Fisher trace gives a genuinely integrable auxiliary trace. -/
theorem integrable_trace_normalizedDensity {n : ℕ} {ρ : E → ℝ} {Z : ℝ}
    (hρ : Differentiable ℝ ρ) (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z)
    (v : Fin n → E) (μ : Measure E) (hint : Integrable (traceIntegrand ρ v) μ) :
    Integrable (traceIntegrand (normalizedDensity ρ Z) v) μ := by
  have he : traceIntegrand (normalizedDensity ρ Z) v =
      fun x => traceIntegrand ρ v x / Z := by
    funext x
    exact traceIntegrand_normalizedDensity (hρ x) (hpos x) hZ v
  rw [he]
  exact hint.div_const Z

/-- The integrated normalized Fisher trace scales by the reciprocal spatial mass. -/
theorem fisherTrace_normalizedDensity {n : ℕ} {ρ : E → ℝ} {Z : ℝ}
    (hρ : Differentiable ℝ ρ) (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z)
    (v : Fin n → E) (μ : Measure E) (hint : Integrable (traceIntegrand ρ v) μ) :
    fisherTrace (normalizedDensity ρ Z) v μ = fisherTrace ρ v μ / Z := by
  have _ := integrable_trace_normalizedDensity hρ hpos hZ v μ hint
  simp only [fisherTrace, traceIntegrand_normalizedDensity (hρ _) (hpos _) hZ]
  exact integral_div Z _

/-- Multiplying normalized spatial Fisher information by its positive normalization constant
recovers the physical homogeneous Fisher functional, without rescaling the field. -/
theorem mass_mul_fisherTrace_normalizedDensity {n : ℕ} {ρ : E → ℝ} {Z : ℝ}
    (hρ : Differentiable ℝ ρ) (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z)
    (v : Fin n → E) (μ : Measure E) (hint : Integrable (traceIntegrand ρ v) μ) :
    Z * fisherTrace (normalizedDensity ρ Z) v μ = fisherTrace ρ v μ := by
  rw [fisherTrace_normalizedDensity hρ hpos hZ v μ hint]
  field_simp

/-- Genuine integrability of each diagonal matrix entry supplies integrability
of the finite positive spatial Fisher trace. -/
theorem integrable_trace_of_diagonal {n : ℕ} (ρ : E → ℝ) (v : Fin n → E) (μ : Measure E)
    (hint : ∀ i, Integrable (matrixIntegrand ρ v i i) μ) :
    Integrable (traceIntegrand ρ v) μ := by
  have he : traceIntegrand ρ v = fun x => ∑ i, matrixIntegrand ρ v i i x := by
    funext x
    exact traceIntegrand_eq_sum ρ v x
  rw [he]
  exact integrable_finsetSum _ (fun i _ => hint i)

/-- The actual trace integral is the sum of the finite Fisher diagonal integrals. -/
theorem fisherTrace_eq_sum_diagonal {n : ℕ} (ρ : E → ℝ) (v : Fin n → E) (μ : Measure E)
    (hint : ∀ i, Integrable (matrixIntegrand ρ v i i) μ) :
    fisherTrace ρ v μ = ∑ i, fisherMatrix ρ v μ i i := by
  simp only [fisherTrace, traceIntegrand_eq_sum, fisherMatrix]
  exact integral_finsetSum _ (fun i _ => hint i)

/-- The integrated spatial Fisher trace is nonnegative, with no Lorentzian signs. -/
theorem fisherTrace_nonneg {n : ℕ} (ρ : E → ℝ) (v : Fin n → E) (μ : Measure E)
    (hpos : ∀ x, 0 ≤ ρ x) : 0 ≤ fisherTrace ρ v μ :=
  integral_nonneg (fun x => traceIntegrand_nonneg ρ v (hpos x))

end FoliationQM.FisherNormalization
