module

public import FoliationQM.NodalPolarConverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantization of the clock circulation

Source: v13 `thm:wallstrom` Part(a) and `eq:sagnac_quant`, component kinds B
and C. Let `q` be a complex phase satisfying the clock differential relation
`dq = -i ω q α` along a differentiable curve `γ`. Then `q` is transported along
the curve by the exponential of the line integral of `α`. If the curve is
closed and `q` does not vanish at its base point, the circulation
`∮ α = ∫₀¹ α(γ(t)) γ'(t) dt` is an integer multiple of `T₀ = 2π/ω`, and the
action circulation `∮ dS` with `dS = -mc² α` is an integer multiple of `2πħ`.
The clock form of a continuously differentiable wave that does not vanish on
the curve has this property.

The single-valued phase is a hypothesis, as in the source; no phase is
reconstructed from the form here. The curve is a differentiable map of the
real line with `γ 1 = γ 0`, and the differential relation is used along the
whole curve.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SagnacQuantization

open MeasureTheory Set NodalPolarConverse
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : E → ℂ}
  {α : E → E →L[ℝ] ℝ} {w : ℝ} {γ γ' : ℝ → E}

/-- The circulation of a one-form along a parametrized curve over the unit interval. -/
def circulation (α : E → E →L[ℝ] ℝ) (γ γ' : ℝ → E) : ℝ :=
  ∫ t in (0 : ℝ)..1, α (γ t) (γ' t)

/-- The clock form is `(i/ω) q⁻¹ dq` wherever the phase is nonzero. -/
theorem clock_eq_log_derivative {x : E} (hw : w ≠ 0) (hne : q x ≠ 0) (v : E) :
    Complex.I / w * ((q x)⁻¹ * ((α x).smulRight (-Complex.I * (w : ℂ) * q x)) v) =
      α x v := by
  have hwc : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  rw [ContinuousLinearMap.smulRight_apply, Complex.real_smul,
    show Complex.I / w * ((q x)⁻¹ * (((α x v : ℝ) : ℂ) * (-Complex.I * w * q x))) =
      -(Complex.I * Complex.I) * ((α x v : ℝ) : ℂ) * ((w : ℂ)⁻¹ * w) * ((q x)⁻¹ * q x) by ring,
    Complex.I_mul_I, inv_mul_cancel₀ hwc, inv_mul_cancel₀ hne]
  simp

/-- A phase with the clock differential relation along a curve is transported
by the exponential of the line integral of the clock form. -/
theorem phase_transport (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hq : ∀ t, HasFDerivAt q ((α (γ t)).smulRight (-Complex.I * (w : ℂ) * q (γ t))) (γ t))
    (hα : Continuous fun t => α (γ t) (γ' t)) (t : ℝ) :
    q (γ t) = q (γ 0) *
      Complex.exp (-Complex.I * w * ((∫ s in (0 : ℝ)..t, α (γ s) (γ' s) : ℝ) : ℂ)) := by
  let J : ℝ → ℝ := fun u => ∫ s in (0 : ℝ)..u, α (γ s) (γ' s)
  let F : ℝ → ℂ := fun u => q (γ u) * Complex.exp (Complex.I * w * (J u : ℂ))
  have hJ (u : ℝ) : HasDerivAt J (α (γ u) (γ' u)) u :=
    intervalIntegral.integral_hasDerivAt_right (hα.intervalIntegrable 0 u)
      (hα.stronglyMeasurableAtFilter _ _) hα.continuousAt
  have hF (u : ℝ) : HasDerivAt F 0 u := by
    have h1 : HasDerivAt (fun u => q (γ u))
        (α (γ u) (γ' u) • (-Complex.I * (w : ℂ) * q (γ u))) u := by
      have h := (hq u).comp_hasDerivAt u (hγ u)
      rw [ContinuousLinearMap.smulRight_apply] at h
      exact h
    have h2 : HasDerivAt (fun u => Complex.exp (Complex.I * w * (J u : ℂ)))
        (Complex.exp (Complex.I * w * (J u : ℂ)) *
          (Complex.I * w * ((α (γ u) (γ' u) : ℝ) : ℂ))) u :=
      ((hJ u).ofReal_comp.const_mul (Complex.I * w)).cexp
    have h3 := h1.mul h2
    have hz : α (γ u) (γ' u) • (-Complex.I * (w : ℂ) * q (γ u)) *
          Complex.exp (Complex.I * w * (J u : ℂ)) +
        q (γ u) * (Complex.exp (Complex.I * w * (J u : ℂ)) *
          (Complex.I * w * ((α (γ u) (γ' u) : ℝ) : ℂ))) = 0 := by
      rw [Complex.real_smul]
      ring
    rw [hz] at h3
    exact h3
  have hconst : F t = F 0 :=
    is_const_of_deriv_eq_zero (fun u => (hF u).differentiableAt) (fun u => (hF u).deriv) t 0
  have h0 : F 0 = q (γ 0) := by
    simp [F, J]
  have hexp : Complex.exp (Complex.I * w * (J t : ℂ)) *
      Complex.exp (-Complex.I * w * (J t : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc q (γ t) = F t * Complex.exp (-Complex.I * w * (J t : ℂ)) := by
        simp only [F]
        rw [mul_assoc, hexp, mul_one]
    _ = q (γ 0) * Complex.exp (-Complex.I * w * (J t : ℂ)) := by rw [hconst, h0]

/-- Sagnac–Wallstrom quantization: along a closed curve the circulation of the
clock form is an integer multiple of the period `2π/ω`. -/
theorem circulation_quantized (hw : w ≠ 0) (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hq : ∀ t, HasFDerivAt q ((α (γ t)).smulRight (-Complex.I * (w : ℂ) * q (γ t))) (γ t))
    (hα : Continuous fun t => α (γ t) (γ' t)) (hclosed : γ 1 = γ 0) (hne : q (γ 0) ≠ 0) :
    ∃ n : ℤ, circulation α γ γ' = -(n : ℝ) * (2 * Real.pi / w) := by
  have h := phase_transport hγ hq hα 1
  rw [hclosed] at h
  have hexp : Complex.exp (-Complex.I * w * ((circulation α γ γ' : ℝ) : ℂ)) = 1 := by
    have h' : q (γ 0) * 1 = q (γ 0) *
        Complex.exp (-Complex.I * w * ((circulation α γ γ' : ℝ) : ℂ)) := by
      rw [mul_one]
      exact h
    exact (mul_left_cancel₀ hne h').symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨n, ?_⟩
  have hI : (-(w : ℂ) * ((circulation α γ γ' : ℝ) : ℂ) - n * (2 * Real.pi)) * Complex.I = 0 := by
    linear_combination hn
  have hreal : -(w : ℂ) * ((circulation α γ γ' : ℝ) : ℂ) = n * (2 * Real.pi) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hI).resolve_right Complex.I_ne_zero)
  have hr : -w * circulation α γ γ' = n * (2 * Real.pi) := by exact_mod_cast hreal
  field_simp
  linarith

/-- The Wallstrom circulation condition: with `ω = mc²/ħ` and action form
`dS = -mc² α`, the action circulation is an integer multiple of `2πħ`. -/
theorem action_circulation_quantized (p : MassiveParameters)
    (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hq : ∀ t, HasFDerivAt q ((α (γ t)).smulRight
      (-Complex.I * ((p.m * p.c ^ 2 / p.hbar : ℝ) : ℂ) * q (γ t))) (γ t))
    (hα : Continuous fun t => α (γ t) (γ' t)) (hclosed : γ 1 = γ 0) (hne : q (γ 0) ≠ 0) :
    ∃ n : ℤ, -(p.m * p.c ^ 2) * circulation α γ γ' = 2 * Real.pi * n * p.hbar := by
  have hm := p.m_pos
  have hc := p.c_pos
  have hh := p.hbar_pos
  have hw : p.m * p.c ^ 2 / p.hbar ≠ 0 := by positivity
  obtain ⟨n, hn⟩ := circulation_quantized hw hγ hq hα hclosed hne
  refine ⟨n, ?_⟩
  rw [hn]
  field_simp

/-- The clock form `-ω⁻¹ Im(dψ/ψ)` of a continuously differentiable wave has
quantized circulation along every closed curve on which the wave is nonzero. -/
theorem wave_circulation_quantized {ψ : E → ℂ} (hw : w ≠ 0) (hψ : ContDiff ℝ 1 ψ)
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ') (hclosed : γ 1 = γ 0)
    (hne : ∀ t, ψ (γ t) ≠ 0) :
    ∃ n : ℤ, circulation (fun x => clockDeriv w (ψ x) (fderiv ℝ ψ x)) γ γ' =
      -(n : ℝ) * (2 * Real.pi / w) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  have hcont : Continuous fun t => clockDeriv w (ψ (γ t)) (fderiv ℝ ψ (γ t)) (γ' t) := by
    simp only [clockDeriv_apply]
    exact continuous_const.mul (Complex.continuous_im.comp
      (((hψ.continuous.comp hγc).inv₀ hne).mul
        (((hψ.continuous_fderiv one_ne_zero).comp hγc).clm_apply hγ')))
  exact circulation_quantized (q := unitPhase ψ) hw hγ
    (fun t => hasFDerivAt_unitPhase hw (hψ.differentiable one_ne_zero (γ t)).hasFDerivAt (hne t))
    hcont hclosed (fun h => by
      have h1 := norm_unitPhase (hne 0)
      rw [h, norm_zero] at h1
      exact zero_ne_one h1)

end FoliationQM.SagnacQuantization
