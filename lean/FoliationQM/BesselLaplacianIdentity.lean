module

public import Mathlib.Analysis.Distribution.Sobolev

/-!
# The actual finite-dimensional order-two Bessel identity

Source: v13 `thm:wallstrom` Part (c), analytic prerequisites of kinds C and D.
On any finite-dimensional real Hilbert domain, the pinned Fourier normalization
gives B₂ = 1 - (2π)⁻² Δ on actual complex-valued or complex-vector-valued
tempered distributions. No positive-dimension, Sobolev-membership or L²
second-derivative hypothesis is needed. Applying this identity to the
constructed nodal extension remains a separate step.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.BesselLaplacianIdentity
open TemperedDistribution FourierTransform
open scoped SchwartzMap Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual order-two Bessel operator is identity minus the distributional
Laplacian with the pinned Fourier normalization, in every finite dimension. -/
theorem besselPotential_two_eq (f : 𝓢'(E, F)) :
    besselPotential E F 2 f =
      f - (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) • Δ f := by
  have h1 : (fun _ : E => (1 : ℂ)).HasTemperateGrowth := by fun_prop
  have hq : (fun x : E => Complex.ofReal (‖x‖ ^ 2)).HasTemperateGrowth := by fun_prop
  have hb : besselPotential E F 2 f =
      f + fourierMultiplierCLM F (fun x : E => Complex.ofReal (‖x‖ ^ 2)) f := by
    have hs : (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (2 / 2 : ℝ))) =
        (fun _ : E => (1 : ℂ)) + (fun x : E => Complex.ofReal (‖x‖ ^ 2)) := by
      funext x
      simp
    rw [besselPotential, hs, fourierMultiplierCLM_apply, smulLeftCLM_add h1 hq,
      add_apply, fourierInv_add, smulLeftCLM_const, one_smul,
      fourierInv_fourier_eq]
    rfl
  have hp : (2 * Real.pi) ^ 2 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hscale : Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹) *
      Complex.ofReal (-((2 * Real.pi) ^ 2)) = -1 := by
    rw [← Complex.ofReal_mul]
    norm_cast
    rw [mul_neg, inv_mul_cancel₀ hp]
    norm_num
  rw [hb, laplacian_eq_fourierMultiplierCLM,
    ← Complex.coe_smul (-((2 * Real.pi) ^ 2)), smul_smul, hscale,
    neg_one_smul, sub_neg_eq_add]

end FoliationQM.BesselLaplacianIdentity
