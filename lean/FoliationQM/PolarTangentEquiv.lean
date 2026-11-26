module

public import FoliationQM.ActionDensity

/-!
# Invertible density-phase variations on the regular polar domain

Source: v13 `thm:kahler` and `eq:master_variational_equivalence`.
These are explicit pointwise tangent maps and their actual one-parameter
derivative realization, for positive density and a supplied real phase lift.
The algebraic inverse does not choose a phase branch or assert that a global
real phase exists. Compact support and smoothness of field variations are
separate analytic questions.
-/
@[expose] public section

namespace FoliationQM.PolarTangentEquiv

open ActionDensity PolarDifferential MasterMetricAndCone
open scoped ComplexConjugate

/-- The complex tangent induced by density increment `a` and action-phase
increment `b`, at a background field `ψ` with density `ρ`. -/
noncomputable def tangent (p : MassiveParameters) (ρ : ℝ) (ψ : ℂ) (a b : ℝ) : ℂ :=
  ψ * ((a / (2 * ρ) : ℝ) + Complex.I * (b / p.hbar : ℝ))

/-- The density increment recovered from a complex tangent. -/
noncomputable def densityVariation (ψ η : ℂ) : ℝ :=
  2 * (conj ψ * η).re

/-- The action-phase increment recovered from a complex tangent. -/
noncomputable def phaseVariation (p : MassiveParameters) (ρ : ℝ) (ψ η : ℂ) : ℝ :=
  p.hbar * (conj ψ * η).im / ρ

/-- Multiplication by the conjugate background diagonalizes the two real
variation components. -/
theorem conj_mul_tangent (p : MassiveParameters) {ρ : ℝ} {ψ : ℂ}
    (hρ : 0 < ρ) (hborn : conj ψ * ψ = (ρ : ℂ)) (a b : ℝ) :
    conj ψ * tangent p ρ ψ a b = (a / 2 : ℝ) + Complex.I * (ρ * b / p.hbar : ℝ) := by
  rw [tangent, ← mul_assoc, hborn]
  have hr : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ)
  push_cast
  field_simp

/-- Recovering the density component after the forward tangent map. -/
theorem densityVariation_tangent (p : MassiveParameters) {ρ : ℝ} {ψ : ℂ}
    (hρ : 0 < ρ) (hborn : conj ψ * ψ = (ρ : ℂ)) (a b : ℝ) :
    densityVariation ψ (tangent p ρ ψ a b) = a := by
  rw [densityVariation, conj_mul_tangent p hρ hborn]
  simp
  ring

/-- Recovering the action-phase component after the forward tangent map. -/
theorem phaseVariation_tangent (p : MassiveParameters) {ρ : ℝ} {ψ : ℂ}
    (hρ : 0 < ρ) (hborn : conj ψ * ψ = (ρ : ℂ)) (a b : ℝ) :
    phaseVariation p ρ ψ (tangent p ρ ψ a b) = b := by
  rw [phaseVariation, conj_mul_tangent p hρ hborn]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
  have hh := ne_of_gt p.hbar_pos
  have hr := ne_of_gt hρ
  field_simp

/-- Reconstructing every complex tangent from its two recovered real
components. The Born identity is the only background relation used. -/
theorem tangent_inverse (p : MassiveParameters) {ρ : ℝ} {ψ : ℂ}
    (hρ : 0 < ρ) (hborn : conj ψ * ψ = (ρ : ℂ)) (η : ℂ) :
    tangent p ρ ψ (densityVariation ψ η) (phaseVariation p ρ ψ η) = η := by
  have hr : ρ ≠ 0 := ne_of_gt hρ
  have hh : p.hbar ≠ 0 := ne_of_gt p.hbar_pos
  have hcomponents :
      ((densityVariation ψ η / (2 * ρ) : ℝ) : ℂ) +
        Complex.I * (phaseVariation p ρ ψ η / p.hbar : ℝ) =
      (conj ψ * η) / (ρ : ℂ) := by
    apply Complex.ext <;>
      simp [densityVariation, phaseVariation, Complex.div_re, Complex.div_im,
        Complex.normSq_ofReal] <;> field_simp
  rw [tangent, hcomponents, mul_div_assoc]
  rw [← mul_assoc, mul_comm ψ (conj ψ), hborn]
  simpa only [mul_div_assoc] using
    mul_div_cancel_left₀ η (Complex.ofReal_ne_zero.mpr hr)

/-- The forward tangent is injective in its two real components. -/
theorem tangent_injective (p : MassiveParameters) {ρ : ℝ} {ψ : ℂ}
    (hρ : 0 < ρ) (hborn : conj ψ * ψ = (ρ : ℂ)) :
    Function.Injective (fun q : ℝ × ℝ => tangent p ρ ψ q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · simpa only [densityVariation_tangent p hρ hborn] using
      congrArg (densityVariation ψ) h
  · simpa only [phaseVariation_tangent p hρ hborn] using
      congrArg (phaseVariation p ρ ψ) h

/-- The forward tangent reaches every complex variation. -/
theorem tangent_surjective (p : MassiveParameters) {ρ : ℝ} {ψ : ℂ}
    (hρ : 0 < ρ) (hborn : conj ψ * ψ = (ρ : ℂ)) :
    Function.Surjective (fun q : ℝ × ℝ => tangent p ρ ψ q.1 q.2) := by
  intro η
  exact ⟨(densityVariation ψ η, phaseVariation p ρ ψ η), tangent_inverse p hρ hborn η⟩

/-- The regular polar differential is a genuine equivalence of real tangent
coordinates; this does not assert a globally injective phase coordinate. -/
noncomputable def tangentEquiv (p : MassiveParameters) {ρ : ℝ} {ψ : ℂ}
    (hρ : 0 < ρ) (hborn : conj ψ * ψ = (ρ : ℂ)) : (ℝ × ℝ) ≃ ℂ where
  toFun q := tangent p ρ ψ q.1 q.2
  invFun η := (densityVariation ψ η, phaseVariation p ρ ψ η)
  left_inv q := Prod.ext (densityVariation_tangent p hρ hborn q.1 q.2)
    (phaseVariation_tangent p hρ hborn q.1 q.2)
  right_inv := tangent_inverse p hρ hborn

/-- The factorized tangent formula agrees with the already verified polar
differential at a positive-density action field. -/
theorem tangent_eq_polarTangent (p : MassiveParameters) (ρ S a b : ℝ)
    (hρ : 0 < ρ) :
    tangent p ρ ((Real.sqrt ρ : ℂ) * phase (S / p.hbar)) a b =
      polarTangent ρ (S / p.hbar) a (b / p.hbar) := by
  have hs : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hρ)
  have hr : ρ ≠ 0 := ne_of_gt hρ
  have hcoeff : Real.sqrt ρ * (a / (2 * ρ)) = a / (2 * Real.sqrt ρ) := by
    field_simp
    rw [Real.sq_sqrt hρ.le]
    ring
  have hcoeffc : (Real.sqrt ρ : ℂ) * ((a / (2 * ρ) : ℝ) : ℂ) =
      ((a / (2 * Real.sqrt ρ) : ℝ) : ℂ) := by
    exact_mod_cast hcoeff
  simp only [tangent, polarTangent, amplitudeTangent]
  calc
    _ = phase (S / p.hbar) *
        ((Real.sqrt ρ : ℂ) * ((a / (2 * ρ) : ℝ) : ℂ) +
          Complex.I * (Real.sqrt ρ : ℂ) * (b / p.hbar : ℝ)) := by ring
    _ = _ := by rw [hcoeffc]

/-- An affine path of density and action phase realizes the forward tangent
as an actual derivative at zero. Only positivity at the base point is used. -/
theorem hasDerivAt_polarVariation (p : MassiveParameters) (ρ S a b : ℝ)
    (hρ : 0 < ρ) :
    HasDerivAt
      (fun t : ℝ => actionField p (fun _ : Unit => ρ + t * a)
        (fun _ => S + t * b) ())
      (tangent p ρ ((Real.sqrt ρ : ℂ) * phase (S / p.hbar)) a b) 0 := by
  have hdρ : HasDerivAt (fun t : ℝ => ρ + t * a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_add ρ
  have hdΦ : HasDerivAt (fun t : ℝ => (S + t * b) / p.hbar) (b / p.hbar) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const b).const_add S).div_const p.hbar
  have hd := (hasFDerivAt_polarField hdρ.hasFDerivAt hdΦ.hasFDerivAt
    (by simpa using hρ)).hasDerivAt
  rw [polarDifferential_apply] at hd
  change HasDerivAt (polarField (fun t => ρ + t * a)
    (fun t => (S + t * b) / p.hbar))
    (tangent p ρ ((Real.sqrt ρ : ℂ) * phase (S / p.hbar)) a b) 0
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    one_mul, zero_mul, add_zero,
    tangent_eq_polarTangent p ρ S a b hρ] using hd

end FoliationQM.PolarTangentEquiv
