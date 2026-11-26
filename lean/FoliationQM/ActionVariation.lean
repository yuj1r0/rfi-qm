module

public import FoliationQM.ActionDensity
public import FoliationQM.PolarSecondDifferential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# First variation of the flat quadratic action

Source: v13 `eq:KG_action` and `thm:kahler`. The real action is the integral
of the source's diagonal Hermitian density. An exact quadratic expansion
justifies its first variation under explicit differentiability and integrability
conditions. Boundary terms and the Euler--Lagrange conclusion are separate.
-/
@[expose] public section

namespace FoliationQM.ActionVariation

open scoped ComplexConjugate
open MeasureTheory PolarSecondDifferential

/-- The flat Hermitian kinetic pairing with signs `(+---)`. -/
def kineticPairing (du dv : Fin 4 → ℂ) : ℂ :=
  conj (du 0) * dv 0 - conj (du 1) * dv 1 -
    conj (du 2) * dv 2 - conj (du 3) * dv 3

/-- The polarized quadratic Klein--Gordon density. -/
noncomputable def pairing (p : MassiveParameters) (u v : ℂ)
    (du dv : Fin 4 → ℂ) : ℂ :=
  (p.hbar : ℂ) ^ 2 * kineticPairing du dv -
    (p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2 * conj u * v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The polarized density using actual directional derivatives. -/
noncomputable def fieldPairing (p : MassiveParameters) (f g : E → ℂ)
    (e : Fin 4 → E) (x : E) : ℂ :=
  pairing p (f x) (g x) (fun μ => directionalDerivative f (e μ) x)
    (fun μ => directionalDerivative g (e μ) x)

/-- The real quadratic Klein--Gordon action for a supplied measure. -/
noncomputable def action [MeasurableSpace E] (p : MassiveParameters) (ψ : E → ℂ)
    (e : Fin 4 → E) (μ : Measure E) : ℝ :=
  ∫ x, (fieldPairing p ψ ψ e x).re ∂μ

/-- Hermitian symmetry of the concrete polarized density. -/
theorem pairing_conj (p : MassiveParameters) (u v : ℂ) (du dv : Fin 4 → ℂ) :
    conj (pairing p u v du dv) = pairing p v u dv du := by
  simp only [pairing, kineticPairing, map_sub, map_mul, map_pow,
    Complex.conj_ofReal]
  simp only [starRingEnd_self_apply]
  ring

/-- Interchanging the two fields preserves the real polarized density. -/
theorem fieldPairing_re_symm (p : MassiveParameters) (f g : E → ℂ)
    (e : Fin 4 → E) (x : E) :
    (fieldPairing p f g e x).re = (fieldPairing p g f e x).re := by
  have h := congrArg Complex.re (pairing_conj p (f x) (g x)
    (fun μ => directionalDerivative f (e μ) x)
    (fun μ => directionalDerivative g (e μ) x))
  simpa only [fieldPairing, Complex.conj_re] using h

/-- On the diagonal the polarized density is the literal source density. -/
theorem fieldPairing_self_eq_fieldDensity (p : MassiveParameters) {ψ : E → ℂ}
    {x : E} (hψ : DifferentiableAt ℝ ψ x) (e : Fin 4 → E) :
    fieldPairing p ψ ψ e x = ActionDensity.fieldDensity p ψ x e := by
  rw [ActionDensity.fieldDensity_eq_kgDensity p hψ]
  simp only [fieldPairing, pairing, kineticPairing, directionalDerivative,
    ActionDensity.kgDensity, ActionDensity.complexKinetic]
  ring

/-- Exact polynomial expansion of the Hermitian density along a real variation. -/
theorem pairing_variation (p : MassiveParameters) (u v : ℂ)
    (du dv : Fin 4 → ℂ) (t : ℝ) :
    pairing p (u + t * v) (u + t * v)
        (fun i => du i + t * dv i) (fun i => du i + t * dv i) =
      pairing p u u du du + t * (pairing p u v du dv + pairing p v u dv du) +
        (t : ℂ) ^ 2 * pairing p v v dv dv := by
  simp only [pairing, kineticPairing, map_add, map_mul, Complex.conj_ofReal]
  ring

/-- The actual directional derivative of an affine field variation. -/
theorem directionalDerivative_variation {ψ η : E → ℂ} {x : E}
    (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x)
    (t : ℝ) (v : E) :
    directionalDerivative (fun y => ψ y + t * η y) v x =
      directionalDerivative ψ v x + t * directionalDerivative η v x := by
  unfold directionalDerivative
  have hd := hψ.hasFDerivAt.add (hη.hasFDerivAt.const_mul (t : ℂ))
  change (fderiv ℝ (ψ + fun y => (t : ℂ) * η y) x) v = _
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-- The real density along an actual affine variation has its exact quadratic form. -/
theorem fieldPairing_variation_re (p : MassiveParameters) {ψ η : E → ℂ} {x : E}
    (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x)
    (e : Fin 4 → E) (t : ℝ) :
    (fieldPairing p (fun y => ψ y + t * η y) (fun y => ψ y + t * η y) e x).re =
      (fieldPairing p ψ ψ e x).re + 2 * t * (fieldPairing p η ψ e x).re +
        t ^ 2 * (fieldPairing p η η e x).re := by
  have hj := pairing_variation p (ψ x) (η x)
    (fun μ => directionalDerivative ψ (e μ) x)
    (fun μ => directionalDerivative η (e μ) x) t
  simp only [fieldPairing, directionalDerivative_variation hψ hη]
  rw [hj]
  change _ = (fieldPairing p ψ ψ e x).re +
    2 * t * (fieldPairing p η ψ e x).re + t ^ 2 * (fieldPairing p η η e x).re
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, ← Complex.ofReal_pow]
  change (fieldPairing p ψ ψ e x).re +
    t * ((fieldPairing p ψ η e x).re + (fieldPairing p η ψ e x).re) +
    t ^ 2 * (fieldPairing p η η e x).re = _
  rw [fieldPairing_re_symm p ψ η]
  ring

variable [MeasurableSpace E]

/-- Integrability along the full real variation follows from three real pairings. -/
theorem integrable_variation (p : MassiveParameters) (ψ η : E → ℂ)
    (e : Fin 4 → E) (μ : Measure E)
    (hψ : ∀ᵐ x ∂μ, DifferentiableAt ℝ ψ x)
    (hη : ∀ᵐ x ∂μ, DifferentiableAt ℝ η x)
    (hself : Integrable (fun x => (fieldPairing p ψ ψ e x).re) μ)
    (hcross : Integrable (fun x => (fieldPairing p η ψ e x).re) μ)
    (htest : Integrable (fun x => (fieldPairing p η η e x).re) μ) (t : ℝ) :
    Integrable (fun x =>
      (fieldPairing p (fun y => ψ y + t * η y) (fun y => ψ y + t * η y) e x).re) μ := by
  apply ((hself.add (hcross.const_mul (2 * t))).add (htest.const_mul (t ^ 2))).congr
  filter_upwards [hψ, hη] with x hxψ hxη
  exact (fieldPairing_variation_re p hxψ hxη e t).symm

/-- Exact quadratic expansion of the genuine integrated action. -/
theorem action_variation (p : MassiveParameters) (ψ η : E → ℂ)
    (e : Fin 4 → E) (μ : Measure E)
    (hψ : ∀ᵐ x ∂μ, DifferentiableAt ℝ ψ x)
    (hη : ∀ᵐ x ∂μ, DifferentiableAt ℝ η x)
    (hself : Integrable (fun x => (fieldPairing p ψ ψ e x).re) μ)
    (hcross : Integrable (fun x => (fieldPairing p η ψ e x).re) μ)
    (htest : Integrable (fun x => (fieldPairing p η η e x).re) μ) (t : ℝ) :
    action p (fun y => ψ y + t * η y) e μ =
      action p ψ e μ + 2 * t * (∫ x, (fieldPairing p η ψ e x).re ∂μ) +
        t ^ 2 * action p η e μ := by
  unfold action
  calc
    _ = ∫ x, (fieldPairing p ψ ψ e x).re +
        2 * t * (fieldPairing p η ψ e x).re +
        t ^ 2 * (fieldPairing p η η e x).re ∂μ := by
      apply integral_congr_ae
      filter_upwards [hψ, hη] with x hxψ hxη
      exact fieldPairing_variation_re p hxψ hxη e t
    _ = _ := by
      have hs : Integrable (fun x => (fieldPairing p ψ ψ e x).re +
          2 * t * (fieldPairing p η ψ e x).re) μ := hself.add (hcross.const_mul (2 * t))
      rw [integral_add hs (htest.const_mul (t ^ 2)),
        integral_add hself (hcross.const_mul (2 * t)), integral_const_mul, integral_const_mul]

/-- The first variation is an actual derivative of the integrated action.
The exact quadratic formula avoids any exchange of a limit with an integral. -/
theorem hasDerivAt_action_variation (p : MassiveParameters) (ψ η : E → ℂ)
    (e : Fin 4 → E) (μ : Measure E)
    (hψ : ∀ᵐ x ∂μ, DifferentiableAt ℝ ψ x)
    (hη : ∀ᵐ x ∂μ, DifferentiableAt ℝ η x)
    (hself : Integrable (fun x => (fieldPairing p ψ ψ e x).re) μ)
    (hcross : Integrable (fun x => (fieldPairing p η ψ e x).re) μ)
    (htest : Integrable (fun x => (fieldPairing p η η e x).re) μ) :
    HasDerivAt (fun t : ℝ => action p (fun y => ψ y + t * η y) e μ)
      (2 * ∫ x, (fieldPairing p η ψ e x).re ∂μ) 0 := by
  have heq : (fun t : ℝ => action p (fun y => ψ y + t * η y) e μ) =
      (fun t => action p ψ e μ + 2 * t * (∫ x, (fieldPairing p η ψ e x).re ∂μ) +
        t ^ 2 * action p η e μ) :=
    funext (action_variation p ψ η e μ hψ hη hself hcross htest)
  rw [heq]
  convert ((hasDerivAt_const 0 (action p ψ e μ)).add
    (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
      (∫ x, (fieldPairing p η ψ e x).re ∂μ))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (action p η e μ)) using 1
  · funext t
    rfl
  · norm_num

/-- Integrating the proved positive-density substitution gives equality of
the real actions. This equality alone does not identify all admissible variations. -/
theorem action_polar_eq (p : MassiveParameters) (ρ S : E → ℝ)
    (e : Fin 4 → E) (μ : Measure E)
    (hρ : ∀ᵐ x ∂μ, DifferentiableAt ℝ ρ x)
    (hS : ∀ᵐ x ∂μ, DifferentiableAt ℝ S x)
    (hpos : ∀ᵐ x ∂μ, 0 < ρ x)
    (hint : Integrable (fun x => ActionDensity.hydroDensity p (ρ x)
      (fun i => fderiv ℝ S x (e i))
      (fun i => fderiv ℝ (fun y => Real.log (ρ y)) x (e i))) μ) :
    Integrable (fun x =>
        (fieldPairing p (ActionDensity.actionField p ρ S)
          (ActionDensity.actionField p ρ S) e x).re) μ ∧
      action p (ActionDensity.actionField p ρ S) e μ =
        ∫ x, ActionDensity.hydroDensity p (ρ x) (fun i => fderiv ℝ S x (e i))
          (fun i => fderiv ℝ (fun y => Real.log (ρ y)) x (e i)) ∂μ := by
  have heq : (fun x => (fieldPairing p (ActionDensity.actionField p ρ S)
        (ActionDensity.actionField p ρ S) e x).re) =ᵐ[μ]
      (fun x => ActionDensity.hydroDensity p (ρ x) (fun i => fderiv ℝ S x (e i))
        (fun i => fderiv ℝ (fun y => Real.log (ρ y)) x (e i))) := by
    filter_upwards [hρ, hS, hpos] with x hxρ hxS hxpos
    have hphase : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
      simpa only [div_eq_mul_inv, mul_comm] using hxS.const_mul p.hbar⁻¹
    have hfield : DifferentiableAt ℝ (ActionDensity.actionField p ρ S) x :=
      PolarDifferential.differentiableAt_polarField hxρ hphase hxpos
    rw [fieldPairing_self_eq_fieldDensity p hfield,
      ActionDensity.field_action_density_identity p hxρ hxS hxpos]
    rfl
  exact ⟨hint.congr heq.symm, integral_congr_ae heq⟩

end FoliationQM.ActionVariation
