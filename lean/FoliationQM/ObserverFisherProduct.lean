module

public import FoliationQM.FisherNormalization

/-!
# Observer-factor product rule for the spatial Fisher integral

For v13 `rem:clock_unification_vs_stochastic` and supplement lines 298–310,
the measured slice density is the product of the invariant density and a
positive observer factor. Both logarithmic derivatives are actual Fréchet
derivatives. The integral theorem also establishes finiteness of the
observed Fisher trace from the finite expression on the right.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverFisherProduct

open MeasureTheory FisherNormalization
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {g ρ : E → ℝ} {x : E}

/-- In any direction, the logarithmic score of the measured density is the
sum of the invariant-density score and the observer-factor score. -/
theorem score_mul (hg : DifferentiableAt ℝ g x) (hr : DifferentiableAt ℝ ρ x)
    (hgp : 0 < g x) (hrp : 0 < ρ x) (v : E) :
    score (fun y => g y * ρ y) x v = score ρ x v + score g x v := by
  change score (g * ρ) x v = _
  rw [score_eq (hg.mul hr) (mul_pos hgp hrp), score_eq hr hrp, score_eq hg hgp,
    (hg.hasFDerivAt.mul hr.hasFDerivAt).fderiv]
  simp only [Pi.mul_apply, add_apply, smul_apply, smul_eq_mul]
  field_simp [hgp.ne', hrp.ne']

/-- The homogeneous Fisher trace integrand of the observed density keeps the
original weight and the squared sum of the two spatial scores. -/
theorem traceIntegrand_mul {n : ℕ} (v : Fin n → E)
    (hg : DifferentiableAt ℝ g x) (hr : DifferentiableAt ℝ ρ x)
    (hgp : 0 < g x) (hrp : 0 < ρ x) :
    traceIntegrand (fun y => g y * ρ y) v x =
      g x * ρ x * ∑ i, (score ρ x (v i) + score g x (v i)) ^ 2 := by
  simp only [traceIntegrand, score_mul hg hr hgp hrp]

variable [MeasurableSpace E]

/-- For a finite observed Fisher integrand, the integral product rule holds
on the given slice measure, including restriction to a spatial region.
Regularity and positivity are needed only almost everywhere there. -/
theorem fisherTrace_mul {n : ℕ} (v : Fin n → E) (μ : Measure E)
    (h : ∀ᵐ x ∂μ, DifferentiableAt ℝ g x ∧ DifferentiableAt ℝ ρ x ∧
      0 < g x ∧ 0 < ρ x)
    (hi : Integrable (fun x => g x * ρ x *
      ∑ i, (score ρ x (v i) + score g x (v i)) ^ 2) μ) :
    Integrable (traceIntegrand (fun y => g y * ρ y) v) μ ∧
      fisherTrace (fun y => g y * ρ y) v μ =
        ∫ x, g x * ρ x * ∑ i, (score ρ x (v i) + score g x (v i)) ^ 2 ∂μ := by
  have he : traceIntegrand (fun y => g y * ρ y) v =ᵐ[μ]
      fun x => g x * ρ x * ∑ i, (score ρ x (v i) + score g x (v i)) ^ 2 := by
    filter_upwards [h] with x hx
    exact traceIntegrand_mul v hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  exact ⟨hi.congr he.symm, integral_congr_ae he⟩

/-- With a constant positive observer factor and finite intrinsic Fisher
trace, the homogeneous functional scales by exactly that constant. -/
theorem fisherTrace_const_mul {n : ℕ} (v : Fin n → E) (μ : Measure E) {a : ℝ}
    (ha : 0 < a) (hr : ∀ᵐ x ∂μ, DifferentiableAt ℝ ρ x ∧ 0 < ρ x)
    (hi : Integrable (traceIntegrand ρ v) μ) :
    Integrable (traceIntegrand (fun x => a * ρ x) v) μ ∧
      fisherTrace (fun x => a * ρ x) v μ = a * fisherTrace ρ v μ := by
  have he : traceIntegrand (fun y => a * ρ y) v =ᵐ[μ] fun x => a * traceIntegrand ρ v x := by
    filter_upwards [hr] with x hx
    rw [traceIntegrand_mul (g := fun _ => a) v (differentiableAt_const _) hx.1 ha hx.2]
    simp [traceIntegrand, score, mul_assoc]
  exact ⟨(hi.const_mul a).congr he.symm, (integral_congr_ae he).trans (integral_const_mul _ _)⟩

end FoliationQM.ObserverFisherProduct
