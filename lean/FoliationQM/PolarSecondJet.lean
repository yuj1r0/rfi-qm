module

public import FoliationQM.DressedVelocity

/-!
Pointwise second-jet algebra for v13 `thm:kahler` and
`eq:nonlinear_defect`. The real covectors and wave-operator values in this
module are independent jet inputs. Actual derivatives and their realization
are a separate bridge. The contraction uses coordinates with x⁰ = ct and
the (+---) inverse Minkowski metric. The phase is a local real lift.
-/
@[expose] public section

namespace FoliationQM.PolarSecondJet

/-- Second directional polar chain-rule expression, with unscaled phase. -/
noncomputable def polarSecondTangent (R Φ dR dΦ ddR ddΦ : ℝ) : ℂ :=
  phase Φ * ((ddR : ℂ) - (R : ℂ) * (dΦ : ℂ) ^ 2 +
    Complex.I * (2 * (dR : ℂ) * (dΦ : ℂ) + (R : ℂ) * (ddΦ : ℂ)))

/-- The physical action phase uses the fixed parameter hbar. -/
noncomputable def wave (p : MassiveParameters) (R S : ℝ) : ℂ :=
  (R : ℂ) * phase (S / p.hbar)

/-- Minkowski contraction of the second polar jet with phase S/hbar. -/
noncomputable def boxJet (p : MassiveParameters) (R S : ℝ) (dR dS : Covector)
    (boxR boxS : ℝ) : ℂ :=
  phase (S / p.hbar) *
    (((boxR - R * minkowski dS dS / p.hbar ^ 2 : ℝ) : ℂ) +
      Complex.I * (((2 * minkowski dR dS + R * boxS) / p.hbar : ℝ) : ℂ))

/-- Klein--Gordon residual in the flat (+---) convention. -/
noncomputable def kgResidual (p : MassiveParameters) (R S : ℝ) (dR dS : Covector)
    (boxR boxS : ℝ) : ℂ :=
  boxJet p R S dR dS boxR boxS +
    (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * wave p R S)

/-- Hamilton--Jacobi--Bohm residual on the positive-amplitude chart. -/
noncomputable def hjResidual (p : MassiveParameters) (R : ℝ) (dS : Covector)
    (boxR : ℝ) : ℝ :=
  minkowski dS dS - p.m ^ 2 * p.c ^ 2 - p.hbar ^ 2 * boxR / R

/-- The expanded divergence of R² ∂S at the level of jets. -/
def continuityResidual (R : ℝ) (dR dS : Covector) (boxS : ℝ) : ℝ :=
  2 * R * minkowski dR dS + R ^ 2 * boxS

/-- Explicit diagonal contraction links directional jets to the wave jet. -/
theorem polarSecondTangent_minkowski (p : MassiveParameters) (R S : ℝ)
    (dR dS ddR ddS : Covector) :
    polarSecondTangent R (S / p.hbar) (dR 0) (dS 0 / p.hbar) (ddR 0) (ddS 0 / p.hbar) -
      polarSecondTangent R (S / p.hbar) (dR 1) (dS 1 / p.hbar) (ddR 1) (ddS 1 / p.hbar) -
      polarSecondTangent R (S / p.hbar) (dR 2) (dS 2 / p.hbar) (ddR 2) (ddS 2 / p.hbar) -
      polarSecondTangent R (S / p.hbar) (dR 3) (dS 3 / p.hbar) (ddR 3) (ddS 3 / p.hbar) =
      boxJet p R S dR dS (ddR 0 - ddR 1 - ddR 2 - ddR 3)
        (ddS 0 - ddS 1 - ddS 2 - ddS 3) := by
  simp only [polarSecondTangent, boxJet, minkowski, Complex.ofReal_sub,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  ring

/-- Real and imaginary residual decomposition, requiring no field equation. -/
theorem kgResidual_decomposition (p : MassiveParameters) (R S : ℝ)
    (dR dS : Covector) (boxR boxS : ℝ) (hR : 0 < R) :
    kgResidual p R S dR dS boxR boxS = phase (S / p.hbar) *
      (((-R / p.hbar ^ 2 * hjResidual p R dS boxR : ℝ) : ℂ) +
        Complex.I * ((continuityResidual R dR dS boxS / (p.hbar * R) : ℝ) : ℂ)) := by
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
  have hh0 : (p.hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt p.hbar_pos)
  simp only [kgResidual, boxJet, wave, hjResidual, continuityResidual,
    Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  field_simp
  ring

/-- At positive amplitude, the complex KG jet equation is precisely the pair
of real Hamilton--Jacobi--Bohm and continuity jet equations. -/
theorem kgResidual_eq_zero_iff (p : MassiveParameters) (R S : ℝ)
    (dR dS : Covector) (boxR boxS : ℝ) (hR : 0 < R) :
    kgResidual p R S dR dS boxR boxS = 0 ↔
      hjResidual p R dS boxR = 0 ∧ continuityResidual R dR dS boxS = 0 := by
  rw [kgResidual_decomposition p R S dR dS boxR boxS hR]
  have he : phase (S / p.hbar) ≠ 0 := Complex.exp_ne_zero _
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hh0 : p.hbar ≠ 0 := ne_of_gt p.hbar_pos
  rw [mul_eq_zero, or_iff_right he]
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
      Complex.zero_re] at hr
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
      Complex.zero_im] at hi
    exact ⟨(mul_eq_zero.mp hr).resolve_left (div_ne_zero (neg_ne_zero.mpr hR0)
      (pow_ne_zero 2 hh0)), (div_eq_zero_iff.mp hi).resolve_right (mul_ne_zero hh0 hR0)⟩
  · rintro ⟨hhj, hcont⟩
    simp [hhj, hcont]

/-- The nonlinear amplitude-curvature defect follows from explicit generalized
Hamilton--Jacobi and continuity jet equations. This does not derive either
equation by stationary variation of an action. -/
theorem kgResidual_eq_nonlinearDefect (p : MassiveParameters) (lam R S : ℝ)
    (dR dS : Covector) (boxR boxS : ℝ) (hR : 0 < R)
    (hHJ : minkowski dS dS - p.m ^ 2 * p.c ^ 2 = 4 * lam * boxR / R)
    (hcont : continuityResidual R dR dS boxS = 0) :
    kgResidual p R S dR dS boxR boxS =
      (((1 - 4 * lam / p.hbar ^ 2) * boxR / R : ℝ) : ℂ) * wave p R S := by
  have hj : hjResidual p R dS boxR = (4 * lam - p.hbar ^ 2) * boxR / R := by
    unfold hjResidual
    rw [hHJ]
    ring
  rw [kgResidual_decomposition p R S dR dS boxR boxS hR, hcont, hj]
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
  have hh0 : (p.hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt p.hbar_pos)
  simp only [wave, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Complex.ofReal_one, zero_div, Complex.ofReal_zero, mul_zero, add_zero]
  field_simp
  ring

end FoliationQM.PolarSecondJet
