module

public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual one-dimensional order-two Bessel identity

Sources: v13 thm:uncertainty and eq:heisenberg, analytic components C/D.
The real-line distributional Laplacian is the repeated derivative in direction
one. The pinned Fourier normalization gives B₂ = 1 - (2π)⁻² D₁² on actual
tempered distributions. The explicit complex scalar is suitable for the
actual complex-linear Bessel operators. No Sobolev membership or square
integrability of a second derivative is assumed in these identities.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.BesselFirstOrderIdentity
open TemperedDistribution FourierTransform
open scoped SchwartzMap LineDeriv Laplacian

/-- The actual real-line distributional Laplacian is the repeated direction-one derivative. -/
theorem laplacian_eq_lineDeriv_sq (f : 𝓢'(ℝ, ℂ)) :
    Δ f = ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f) := by
  simpa using TemperedDistribution.laplacian_eq_sum (OrthonormalBasis.singleton Unit ℝ) f

/-- The actual order-two Bessel operator has the pinned Fourier factor and complex scalar. -/
theorem besselPotential_two_eq (f : 𝓢'(ℝ, ℂ)) :
    besselPotential ℝ ℂ 2 f =
      f - (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) •
        ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f) := by
  have h1 : (fun _ : ℝ => (1 : ℂ)).HasTemperateGrowth := by fun_prop
  have hq : (fun x : ℝ => Complex.ofReal (‖x‖ ^ 2)).HasTemperateGrowth := by fun_prop
  have hb : besselPotential ℝ ℂ 2 f =
      f + fourierMultiplierCLM ℂ (fun x : ℝ => Complex.ofReal (‖x‖ ^ 2)) f := by
    have hs : (fun x : ℝ => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (2 / 2 : ℝ))) =
        (fun _ : ℝ => (1 : ℂ)) + (fun x : ℝ => Complex.ofReal (‖x‖ ^ 2)) := by
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
  rw [hb, ← laplacian_eq_lineDeriv_sq f, laplacian_eq_fourierMultiplierCLM,
    ← Complex.coe_smul (-((2 * Real.pi) ^ 2)), smul_smul, hscale,
    neg_one_smul, sub_neg_eq_add]

end FoliationQM.BesselFirstOrderIdentity
