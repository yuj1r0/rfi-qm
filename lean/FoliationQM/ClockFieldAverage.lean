module

public import FoliationQM.ClockScales
public import FoliationQM.ClockCircleAverage
public import FoliationQM.PolarDifferential
public import FoliationQM.DressedVelocity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Actual real clock-carrier differentiation and phase averaging

Sources: v13 `thm:clock_sideband` (Route II) and
`eq:sideband_averaged_lagrangian`. The quadratic real clock Lagrangian is the
source's supplied input. Its consequences are computed using actual Fréchet
derivatives and normalized phase integrals. The four-direction contraction
uses the explicit inverse Minkowski signs `(+---)`; it is not a positive
spatial Fisher metric. Density is positive at the point under consideration.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ClockFieldAverage

open ClockCircleAverage
open MeasureTheory (volume)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The supplied real amplitude-modulated clock readout at initial phase `θ`. -/
def carrier (p : MassiveParameters) (ρ τ : E → ℝ) (θ : ℝ) (x : E) : ℝ :=
  Real.sqrt (2 * ρ x) * Real.cos (p.omega0 * τ x + θ)

/-- The continuous linear differential of the real clock carrier. -/
def carrierDifferential (p : MassiveParameters) (ρ τ θ : ℝ)
    (dρ dτ : E →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  (Real.cos (p.omega0 * τ + θ) / Real.sqrt (2 * ρ)) • dρ -
    (Real.sqrt (2 * ρ) * Real.sin (p.omega0 * τ + θ) * p.omega0) • dτ

/-- Product and chain rules give the actual carrier differential at positive density. -/
theorem hasFDerivAt_carrier (p : MassiveParameters) {ρ τ : E → ℝ}
    {dρ dτ : E →L[ℝ] ℝ} {x : E}
    (hρ : HasFDerivAt ρ dρ x) (hτ : HasFDerivAt τ dτ x)
    (hpos : 0 < ρ x) (θ : ℝ) :
    HasFDerivAt (carrier p ρ τ θ)
      (carrierDifferential p (ρ x) (τ x) θ dρ dτ) x := by
  have hroot := (hρ.const_mul 2).sqrt (by positivity)
  have hcos := ((hτ.const_mul p.omega0).add_const θ).cos
  change HasFDerivAt (fun y => Real.sqrt (2 * ρ y) *
    Real.cos (p.omega0 * τ y + θ)) _ x
  convert hroot.mul hcos using 1
  ext v
  simp only [carrierDifferential, add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

/-- Only pointwise differentiability and positive density are needed. -/
theorem differentiableAt_carrier (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x)
    (hpos : 0 < ρ x) (θ : ℝ) : DifferentiableAt ℝ (carrier p ρ τ θ) x :=
  (hasFDerivAt_carrier p hρ.hasFDerivAt hτ.hasFDerivAt hpos θ).differentiableAt

/-- Evaluation of the actual Fréchet derivative displays the two clock quadratures. -/
theorem fderiv_carrier_apply (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x)
    (hpos : 0 < ρ x) (θ : ℝ) (v : E) :
    fderiv ℝ (carrier p ρ τ θ) x v =
      (fderiv ℝ ρ x v / Real.sqrt (2 * ρ x)) * Real.cos (p.omega0 * τ x + θ) +
      (-(Real.sqrt (2 * ρ x) * p.omega0 * fderiv ℝ τ x v)) *
        Real.sin (p.omega0 * τ x + θ) := by
  rw [(hasFDerivAt_carrier p hρ.hasFDerivAt hτ.hasFDerivAt hpos θ).fderiv]
  simp only [carrierDifferential, sub_apply,
    smul_apply, smul_eq_mul]
  ring

/-- The source clock kinetic prefactor equals the fixed physical `ℏ²`. -/
theorem clock_kinetic_coefficient (p : MassiveParameters) :
    p.m ^ 2 * p.c ^ 4 / p.omega0 ^ 2 = p.hbar ^ 2 := by
  have hm := ne_of_gt p.m_pos
  have hc := ne_of_gt p.c_pos
  have hh := ne_of_gt p.hbar_pos
  unfold MassiveParameters.omega0
  field_simp

/-- Frequency substitution recovers the source clock kinetic coefficient. -/
theorem clock_frequency_coefficient (p : MassiveParameters) :
    p.hbar ^ 2 * p.omega0 ^ 2 = p.m ^ 2 * p.c ^ 4 := by
  have hh := ne_of_gt p.hbar_pos
  unfold MassiveParameters.omega0
  field_simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The supplied carrier has zero actual full-turn phase mean. -/
theorem average_carrier (p : MassiveParameters) (ρ τ : E → ℝ) (x : E) :
    average (fun θ => carrier p ρ τ θ x) = 0 := by
  simp only [carrier, average_const_mul, average_cos, mul_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The carrier's square is genuinely integrable over the physical phase circle. -/
theorem intervalIntegrable_carrier_sq (p : MassiveParameters) (ρ τ : E → ℝ) (x : E) :
    IntervalIntegrable (fun θ => carrier p ρ τ θ x ^ 2) volume 0 (2 * Real.pi) := by
  simpa only [carrier, mul_pow] using
    (intervalIntegrable_cos_sq (p.omega0 * τ x)).const_mul (Real.sqrt (2 * ρ x) ^ 2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Actual normalized phase integration verifies the source density normalization. -/
theorem average_carrier_sq (p : MassiveParameters) (ρ τ : E → ℝ) (x : E)
    (hpos : 0 ≤ ρ x) : average (fun θ => carrier p ρ τ θ x ^ 2) = ρ x := by
  simp only [carrier, mul_pow, average_const_mul, average_cos_sq,
    Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hpos)]
  ring

/-- Products of actual directional carrier derivatives have phase integrability. -/
theorem intervalIntegrable_fderiv_product (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x)
    (hpos : 0 < ρ x) (u v : E) :
    IntervalIntegrable (fun θ => fderiv ℝ (carrier p ρ τ θ) x u *
      fderiv ℝ (carrier p ρ τ θ) x v) volume 0 (2 * Real.pi) := by
  simp_rw [fderiv_carrier_apply p hρ hτ hpos]
  exact intervalIntegrable_quadrature_product _ _ _ _ _

/-- The averaged actual derivative product contains the envelope and clock
terms; their mixed quadratures vanish by genuine integration. -/
theorem average_fderiv_product (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x)
    (hpos : 0 < ρ x) (u v : E) :
    average (fun θ => fderiv ℝ (carrier p ρ τ θ) x u *
      fderiv ℝ (carrier p ρ τ θ) x v) =
      fderiv ℝ ρ x u * fderiv ℝ ρ x v / (4 * ρ x) +
        ρ x * p.omega0 ^ 2 * fderiv ℝ τ x u * fderiv ℝ τ x v := by
  simp_rw [fderiv_carrier_apply p hρ hτ hpos]
  rw [average_quadrature_product]
  calc
    _ = (fderiv ℝ ρ x u * fderiv ℝ ρ x v / (Real.sqrt (2 * ρ x)) ^ 2 +
        (Real.sqrt (2 * ρ x)) ^ 2 * p.omega0 ^ 2 *
          fderiv ℝ τ x u * fderiv ℝ τ x v) / 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity)]; ring

/-- The actual derivative's phase second moment is the stated positive
two-quadrature expression before any Lorentzian contraction is taken. -/
theorem average_fderiv_sq (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x)
    (hpos : 0 < ρ x) (v : E) :
    average (fun θ => (fderiv ℝ (carrier p ρ τ θ) x v) ^ 2) =
      (fderiv ℝ ρ x v) ^ 2 / (4 * ρ x) +
        ρ x * p.omega0 ^ 2 * (fderiv ℝ τ x v) ^ 2 := by
  simpa only [pow_two, mul_assoc] using average_fderiv_product p hρ hτ hpos v v

/-- The signed four-direction actual derivative contraction is phase integrable. -/
theorem intervalIntegrable_kinetic (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x)
    (hpos : 0 < ρ x) (e : Fin 4 → E) :
    IntervalIntegrable (fun θ => minkowski
      (fun μ => fderiv ℝ (carrier p ρ τ θ) x (e μ))
      (fun μ => fderiv ℝ (carrier p ρ τ θ) x (e μ))) volume 0 (2 * Real.pi) := by
  let hi (μ : Fin 4) := intervalIntegrable_fderiv_product p hρ hτ hpos (e μ) (e μ)
  exact ((hi 0 |>.sub (hi 1)).sub (hi 2)).sub (hi 3)

/-- Actual clock averaging commutes with the explicit inverse Minkowski
contraction. This signed quantity is not asserted to be positive. -/
theorem average_kinetic (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x)
    (hpos : 0 < ρ x) (e : Fin 4 → E) :
    average (fun θ => minkowski
      (fun μ => fderiv ℝ (carrier p ρ τ θ) x (e μ))
      (fun μ => fderiv ℝ (carrier p ρ τ θ) x (e μ))) =
      (1 / (4 * ρ x)) * minkowski (fun μ => fderiv ℝ ρ x (e μ))
        (fun μ => fderiv ℝ ρ x (e μ)) +
      ρ x * p.omega0 ^ 2 * minkowski (fun μ => fderiv ℝ τ x (e μ))
        (fun μ => fderiv ℝ τ x (e μ)) := by
  let hi (μ : Fin 4) := intervalIntegrable_fderiv_product p hρ hτ hpos (e μ) (e μ)
  unfold minkowski
  rw [average_sub (((hi 0).sub (hi 1)).sub (hi 2)) (hi 3),
    average_sub ((hi 0).sub (hi 1)) (hi 2), average_sub (hi 0) (hi 1)]
  simp_rw [average_fderiv_product p hρ hτ hpos]
  ring

/-- The supplied quadratic real scalar clock Lagrangian, evaluated with actual
field derivatives and four supplied coordinate directions. -/
def clockLagrangian (p : MassiveParameters) (ρ τ : E → ℝ) (x : E)
    (e : Fin 4 → E) (θ : ℝ) : ℝ :=
  p.hbar ^ 2 * minkowski (fun μ => fderiv ℝ (carrier p ρ τ θ) x (e μ))
    (fun μ => fderiv ℝ (carrier p ρ τ θ) x (e μ)) -
    p.m ^ 2 * p.c ^ 2 * carrier p ρ τ θ x ^ 2

/-- The definition is exactly the source's frequency-prefactor input Lagrangian. -/
theorem clockLagrangian_eq_frequency_form (p : MassiveParameters) (ρ τ : E → ℝ)
    (x : E) (e : Fin 4 → E) (θ : ℝ) :
    clockLagrangian p ρ τ x e θ =
      (p.m ^ 2 * p.c ^ 4 / p.omega0 ^ 2) *
        minkowski (fun μ => fderiv ℝ (carrier p ρ τ θ) x (e μ))
          (fun μ => fderiv ℝ (carrier p ρ τ θ) x (e μ)) -
        p.m ^ 2 * p.c ^ 2 * carrier p ρ τ θ x ^ 2 := by
  rw [clock_kinetic_coefficient]
  rfl

/-- Actual interval integrability justifies the complete clock-Lagrangian average. -/
theorem intervalIntegrable_clockLagrangian (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x)
    (hpos : 0 < ρ x) (e : Fin 4 → E) :
    IntervalIntegrable (clockLagrangian p ρ τ x e) volume 0 (2 * Real.pi) :=
  ((intervalIntegrable_kinetic p hρ hτ hpos e).const_mul (p.hbar ^ 2)).sub
    ((intervalIntegrable_carrier_sq p ρ τ x).const_mul (p.m ^ 2 * p.c ^ 2))

/-- The full source averaged Lagrangian at positive density, using actual
Fréchet derivatives of the carrier, clock, and logarithmic density. -/
theorem average_clockLagrangian (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x)
    (hpos : 0 < ρ x) (e : Fin 4 → E) :
    average (clockLagrangian p ρ τ x e) =
      ρ x * (p.m ^ 2 * p.c ^ 4 *
        minkowski (fun μ => fderiv ℝ τ x (e μ)) (fun μ => fderiv ℝ τ x (e μ)) -
        p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 / 4 *
        minkowski (fun μ => fderiv ℝ (fun y => Real.log (ρ y)) x (e μ))
          (fun μ => fderiv ℝ (fun y => Real.log (ρ y)) x (e μ))) := by
  unfold clockLagrangian
  rw [average_sub ((intervalIntegrable_kinetic p hρ hτ hpos e).const_mul _)
      ((intervalIntegrable_carrier_sq p ρ τ x).const_mul _),
    average_const_mul, average_const_mul, average_kinetic p hρ hτ hpos,
    average_carrier_sq p ρ τ x hpos.le]
  simp_rw [PolarDifferential.fderiv_log_density_apply hρ hpos]
  unfold minkowski MassiveParameters.omega0
  have hr := ne_of_gt hpos
  have hh := ne_of_gt p.hbar_pos
  field_simp
  ring

/-- The same actual derivative-integral identity in the source's literal
period coefficient, using the separately proved physical scale substitution. -/
theorem average_clockLagrangian_period (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x)
    (hpos : 0 < ρ x) (e : Fin 4 → E) :
    average (clockLagrangian p ρ τ x e) =
      ρ x * (p.m ^ 2 * p.c ^ 4 *
        minkowski (fun μ => fderiv ℝ τ x (e μ)) (fun μ => fderiv ℝ τ x (e μ)) -
        p.m ^ 2 * p.c ^ 2 +
        (p.m ^ 2 * p.c ^ 4 * p.period ^ 2 / (16 * Real.pi ^ 2)) *
        minkowski (fun μ => fderiv ℝ (fun y => Real.log (ρ y)) x (e μ))
          (fun μ => fderiv ℝ (fun y => Real.log (ρ y)) x (e μ))) := by
  rw [ClockScales.period_fisher_coefficient]
  exact average_clockLagrangian p hρ hτ hpos e

end FoliationQM.ClockFieldAverage
