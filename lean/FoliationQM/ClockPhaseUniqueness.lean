module

public import FoliationQM.NodalPolarConverse
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniqueness of the reconstructed wave modulo a constant phase

Source: v13 `thm:wallstrom` Part(a), "`ψ = R q` ... unique up to a constant
phase factor per connected component", and the closing bijection of Part(c),
component kinds B and C. On an open connected set, two unit phases with the
clock differential relation for the same clock form differ by a constant of
unit modulus, so the fields built from one amplitude differ by that constant.
Consequently two differentiable non-vanishing waves with equal modulus and
equal clock form on such a set differ by a constant phase, and conversely a
constant phase multiple of a wave has the same modulus and clock form.

A single-valued phase is a hypothesis here, as in the source; the existence
of a phase for a given closed form with integral periods is not proved.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ClockPhaseUniqueness

open Set NodalPolarConverse CirclePolarEnergy
open scoped Topology ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
  {α : E → E →L[ℝ] ℝ} {w : ℝ}

/-- Two unit phases with the same clock differential relation on an open
connected set differ by a constant of unit modulus. -/
theorem phase_unique {q₁ q₂ : E → ℂ} (hC : IsOpen C) (hconn : IsPreconnected C)
    (h₁ : ∀ x ∈ C, HasFDerivAt q₁ ((α x).smulRight (-Complex.I * (w : ℂ) * q₁ x)) x)
    (h₂ : ∀ x ∈ C, HasFDerivAt q₂ ((α x).smulRight (-Complex.I * (w : ℂ) * q₂ x)) x)
    (hu₁ : ∀ x ∈ C, ‖q₁ x‖ = 1) (hu₂ : ∀ x ∈ C, ‖q₂ x‖ = 1) :
    ∃ c : ℂ, (C.Nonempty → ‖c‖ = 1) ∧ ∀ x ∈ C, q₂ x = c * q₁ x := by
  let g : E → ℂ := fun x => q₂ x * conj (q₁ x)
  have hg (x : E) (hx : x ∈ C) : HasFDerivAt g (0 : E →L[ℝ] ℂ) x := by
    have hc : HasFDerivAt (fun y => conj (q₁ y))
        (Complex.conjCLE.toContinuousLinearMap.comp
          ((α x).smulRight (-Complex.I * (w : ℂ) * q₁ x))) x :=
      Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x (h₁ x hx)
    have hm := (h₂ x hx).mul hc
    have hz : q₂ x • (Complex.conjCLE.toContinuousLinearMap.comp
          ((α x).smulRight (-Complex.I * (w : ℂ) * q₁ x))) +
        conj (q₁ x) • (α x).smulRight (-Complex.I * (w : ℂ) * q₂ x) = 0 := by
      ext v
      simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearEquiv.coe_coe,
        Complex.conjCLE_apply, Complex.real_smul, smul_eq_mul, map_mul, map_neg,
        Complex.conj_I, Complex.conj_ofReal, zero_apply]
      ring
    rw [hz] at hm
    exact hm
  obtain ⟨c, hc⟩ := hC.exists_is_const_of_fderiv_eq_zero (𝕜 := ℝ) hconn
    (fun x hx => (hg x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hg x hx).fderiv)
  have hnorm (x : E) (hx : x ∈ C) : q₁ x * conj (q₁ x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu₁ x hx]
    simp
  refine ⟨c, fun ⟨x, hx⟩ => ?_, fun x hx => ?_⟩
  · rw [← hc x hx]
    simp only [g, norm_mul, RCLike.norm_conj, hu₁ x hx, hu₂ x hx, mul_one]
  · rw [← hc x hx]
    simp only [g]
    rw [mul_assoc, mul_comm (conj (q₁ x)), hnorm x hx, mul_one]

/-- The fields reconstructed from one amplitude and two admissible phases
differ by a constant phase on each open connected set. -/
theorem field_unique {R : E → ℝ} {q₁ q₂ : E → ℂ} (hC : IsOpen C) (hconn : IsPreconnected C)
    (h₁ : ∀ x ∈ C, HasFDerivAt q₁ ((α x).smulRight (-Complex.I * (w : ℂ) * q₁ x)) x)
    (h₂ : ∀ x ∈ C, HasFDerivAt q₂ ((α x).smulRight (-Complex.I * (w : ℂ) * q₂ x)) x)
    (hu₁ : ∀ x ∈ C, ‖q₁ x‖ = 1) (hu₂ : ∀ x ∈ C, ‖q₂ x‖ = 1) :
    ∃ c : ℂ, (C.Nonempty → ‖c‖ = 1) ∧ ∀ x ∈ C, field R q₂ x = c * field R q₁ x := by
  obtain ⟨c, hc, h⟩ := phase_unique hC hconn h₁ h₂ hu₁ hu₂
  refine ⟨c, hc, fun x hx => ?_⟩
  simp only [field, h x hx, Complex.real_smul]
  ring

/-- Two differentiable non-vanishing waves with equal modulus and equal clock
form on an open connected set differ by a constant phase. -/
theorem wave_unique {ψ₁ ψ₂ : E → ℂ} (hw : w ≠ 0) (hC : IsOpen C) (hconn : IsPreconnected C)
    (hd₁ : ∀ x ∈ C, DifferentiableAt ℝ ψ₁ x) (hd₂ : ∀ x ∈ C, DifferentiableAt ℝ ψ₂ x)
    (hn₁ : ∀ x ∈ C, ψ₁ x ≠ 0) (hn₂ : ∀ x ∈ C, ψ₂ x ≠ 0)
    (hmod : ∀ x ∈ C, ‖ψ₂ x‖ = ‖ψ₁ x‖)
    (hclock : ∀ x ∈ C, clockDeriv w (ψ₂ x) (fderiv ℝ ψ₂ x) =
      clockDeriv w (ψ₁ x) (fderiv ℝ ψ₁ x)) :
    ∃ c : ℂ, (C.Nonempty → ‖c‖ = 1) ∧ ∀ x ∈ C, ψ₂ x = c * ψ₁ x := by
  obtain ⟨c, hc, h⟩ := phase_unique (α := fun x => clockDeriv w (ψ₁ x) (fderiv ℝ ψ₁ x))
    (q₁ := unitPhase ψ₁) (q₂ := unitPhase ψ₂) hC hconn
    (fun x hx => hasFDerivAt_unitPhase hw (hd₁ x hx).hasFDerivAt (hn₁ x hx))
    (fun x hx => hclock x hx ▸ hasFDerivAt_unitPhase hw (hd₂ x hx).hasFDerivAt (hn₂ x hx))
    (fun x hx => norm_unitPhase (hn₁ x hx)) (fun x hx => norm_unitPhase (hn₂ x hx))
  refine ⟨c, hc, fun x hx => ?_⟩
  have e₁ := congrFun (field_eq ψ₁) x
  have e₂ := congrFun (field_eq ψ₂) x
  simp only [field, amplitude] at e₁ e₂
  rw [← e₂, ← e₁, h x hx, hmod x hx, Complex.real_smul, Complex.real_smul]
  ring

/-- A constant unit phase multiple of a wave has the same modulus and the same
clock form. -/
theorem modulus_clock_of_phase_multiple {ψ : E → ℂ} {x : E} (c : ℂ) (hc : ‖c‖ = 1)
    (hd : DifferentiableAt ℝ ψ x) :
    amplitude (fun y => c * ψ y) x = amplitude ψ x ∧
    clockDeriv w (c * ψ x) (fderiv ℝ (fun y => c * ψ y) x) =
      clockDeriv w (ψ x) (fderiv ℝ ψ x) := by
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; exact one_ne_zero)
  refine ⟨by simp only [amplitude, norm_mul, hc, one_mul], ?_⟩
  ext v
  rw [clockDeriv_apply, clockDeriv_apply, fderiv_const_mul hd]
  simp only [smul_apply, smul_eq_mul]
  congr 2
  rw [mul_inv, mul_assoc,
    show c⁻¹ * ((ψ x)⁻¹ * (c * (fderiv ℝ ψ x) v)) =
      (c⁻¹ * c) * ((ψ x)⁻¹ * (fderiv ℝ ψ x) v) by ring,
    inv_mul_cancel₀ hc0, one_mul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A positive amplitude and a unit phase give a non-vanishing field. -/
theorem field_ne_zero {R : E → ℝ} {q : E → ℂ} {x : E} (hR : 0 < R x) (hq : ‖q x‖ = 1) :
    field R q x ≠ 0 := by
  simp only [field, ne_eq, smul_eq_zero, not_or]
  exact ⟨hR.ne', fun h => by rw [h, norm_zero] at hq; exact zero_ne_one hq⟩

/-- The reconstructed field is as smooth as its amplitude and phase. -/
theorem contDiffAt_field {R : E → ℝ} {q : E → ℂ} {x : E} {n : WithTop ℕ∞}
    (hR : ContDiffAt ℝ n R x) (hq : ContDiffAt ℝ n q x) : ContDiffAt ℝ n (field R q) x :=
  hR.smul hq

end FoliationQM.ClockPhaseUniqueness
