module

public import FoliationQM.OpenIntegrationByParts
public import FoliationQM.Madelung

/-!
# The conserved complex scalar current in flat spacetime

For v13 `eq:noether_current`, the current of a complex scalar is the
antisymmetric field-derivative bilinear with coefficient iℏ/(2m).
Its divergence is computed directly from the wave field, so current
conservation on the Klein–Gordon equation also holds at zeros.
-/

@[expose] public section
noncomputable section
open scoped ComplexConjugate
namespace FoliationQM.ScalarPhaseCurrent

open PolarSecondDifferential Madelung

/-- The four lower real components of the scalar phase current in the x⁰ = ct coordinates. -/
def current (p : MassiveParameters) (ψ : Covector → ℂ) (x : Covector) : Covector :=
  fun i => -(p.hbar / p.m) * (conj (ψ x) * directionalDerivative ψ (coordinateVector i) x).im

/-- The four current components vary continuously at every C¹ scalar-field point. -/
theorem continuousAt_current (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 1 ψ x) : ContinuousAt (current p ψ) x := by
  apply continuousAt_pi.mpr
  intro i
  have hd : ContinuousAt (directionalDerivative ψ (coordinateVector i)) x :=
    (hψ.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  exact continuousAt_const.mul (Complex.continuous_im.continuousAt.comp (hψ.continuousAt.star.mul hd))

/-- The literal complex source bilinear equals the real current, with the derivative
taken on the actual conjugate field in its second term. -/
theorem current_eq_complex (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : DifferentiableAt ℝ ψ x) (i : Fin 4) :
    Complex.I * (p.hbar : ℂ) / (2 * (p.m : ℂ)) *
      (conj (ψ x) * directionalDerivative ψ (coordinateVector i) x -
       ψ x * directionalDerivative (fun y => conj (ψ y)) (coordinateVector i) x) =
      (current p ψ x i : ℂ) := by
  let d := directionalDerivative ψ (coordinateVector i) x
  have hd : directionalDerivative (fun y => conj (ψ y)) (coordinateVector i) x = conj d :=
    ActionDensity.fderiv_conj_apply hψ _
  have he : ψ x * conj d = conj (conj (ψ x) * d) := by simp
  change Complex.I * (p.hbar : ℂ) / (2 * (p.m : ℂ)) *
    (conj (ψ x) * d - ψ x * directionalDerivative (fun y => conj (ψ y)) (coordinateVector i) x) =
      ((-(p.hbar / p.m) * (conj (ψ x) * d).im : ℝ) : ℂ)
  rw [hd, he, Complex.sub_conj]
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- The divergence of the lower scalar current uses the four genuine coordinate derivatives and (+−−−). -/
def divergence (p : MassiveParameters) (ψ : Covector → ℂ) (x : Covector) : ℝ :=
  let term := fun i => directionalDerivative (fun y => current p ψ y i) (coordinateVector i) x
  term 0 - term 1 - term 2 - term 3

/-- In each diagonal derivative the product of the two first jets is real, leaving only the second jet. -/
theorem current_component_derivative (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ x) (i : Fin 4) :
    directionalDerivative (fun y => current p ψ y i) (coordinateVector i) x =
      -(p.hbar / p.m) * (conj (ψ x) * secondDirectionalDerivative ψ (coordinateVector i) x).im := by
  let v := coordinateVector i
  let D := directionalDerivative ψ v
  have hf := (hψ.differentiableAt (by norm_num)).hasFDerivAt
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x hf
  have hd : DifferentiableAt ℝ D x :=
    (OpenIntegrationByParts.contDiffAt_directionalDerivative hψ v).differentiableAt_one
  have he := ((Complex.imCLM.hasFDerivAt.comp x (hc.fun_mul hd.hasFDerivAt)).const_mul (-(p.hbar / p.m)))
  change fderiv ℝ (fun y => -(p.hbar/p.m) * (conj (ψ y) * D y).im) x v = _
  change HasFDerivAt (fun y => -(p.hbar/p.m) * (conj (ψ y) * D y).im) _ x at he
  rw [he.fderiv]
  change -(p.hbar / p.m) * (conj (ψ x) * (fderiv ℝ D x v) + D x * conj (D x)).im = _
  rw [mul_comm (D x), ← Complex.normSq_eq_conj_mul_self, Complex.add_im, Complex.ofReal_im, add_zero]
  rfl

/-- Divergence for an arbitrary C² complex field before imposing the massive field equation. -/
theorem divergence_eq_box (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ x) :
    divergence p ψ x = -(p.hbar / p.m) * (conj (ψ x) * box ψ coordinateVector x).im := by
  simp only [divergence, current_component_derivative p hψ, box, mul_sub, Complex.sub_im]

/-- A pointwise Klein–Gordon solution conserves the actual scalar current, including at nodes. -/
theorem divergence_eq_zero_of_kg (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ x) (hkg : box ψ coordinateVector x +
      (((p.m^2*p.c^2/p.hbar^2 : ℝ) : ℂ) * ψ x) = 0) : divergence p ψ x = 0 := by
  rw [divergence_eq_box p hψ, eq_neg_of_add_eq_zero_left hkg, mul_neg, mul_left_comm (conj (ψ x)),
    ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul]
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, mul_zero]

end FoliationQM.ScalarPhaseCurrent
