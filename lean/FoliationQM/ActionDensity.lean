module

public import FoliationQM.PolarDifferential
public import FoliationQM.DressedVelocity

/-!
# Local flat action-density identity

Sources: v13 `eq:coupled_action`, `eq:KG_action`, and `thm:kahler`.
The contractions below use the explicit inverse Minkowski signs `(+---)`.
When applied to spacetime coordinate directions, the time coordinate is
`x⁰ = ct`. The field results use actual real Fréchet derivatives and a local
real phase. They establish equality of integrands at positive density;
integration, boundary terms, and stationary variation are separate questions.
-/
@[expose] public section

namespace FoliationQM.ActionDensity

open PolarDifferential MasterMetricAndCone
open scoped ComplexConjugate

variable {E : Type*}

/-- The physical phase field, with `Φ = S / ℏ`. -/
noncomputable def actionField (p : MassiveParameters) (ρ S : E → ℝ) : E → ℂ :=
  polarField ρ (fun x => S x / p.hbar)

/-- The diagonal complex kinetic contraction with explicit `(+---)` signs. -/
def complexKinetic (dψ : Fin 4 → ℂ) : ℂ :=
  conj (dψ 0) * dψ 0 - conj (dψ 1) * dψ 1 -
    conj (dψ 2) * dψ 2 - conj (dψ 3) * dψ 3

/-- The real value of the same kinetic contraction. -/
def realKinetic (dψ : Fin 4 → ℂ) : ℝ :=
  Complex.normSq (dψ 0) - Complex.normSq (dψ 1) -
    Complex.normSq (dψ 2) - Complex.normSq (dψ 3)

/-- The complex notation for the quadratic Klein--Gordon density. -/
noncomputable def kgDensity (p : MassiveParameters) (ψ : ℂ) (dψ : Fin 4 → ℂ) : ℂ :=
  (p.hbar : ℂ) ^ 2 * complexKinetic dψ -
    (p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2 * (conj ψ * ψ)

/-- The source density in real density, action-phase, and log-density variables. -/
noncomputable def hydroDensity (p : MassiveParameters) (ρ : ℝ)
    (dS dlogρ : Covector) : ℝ :=
  ρ * (minkowski dS dS - p.m ^ 2 * p.c ^ 2 +
    p.hbar ^ 2 / 4 * minkowski dlogρ dlogρ)

/-- The Born modulus identity for the concrete polar map. This is not a
uniqueness statement about the radial coordinate. -/
theorem polarField_normSq (ρ Φ : E → ℝ) (x : E) (hρ : 0 ≤ ρ x) :
    Complex.normSq (polarField ρ Φ x) = ρ x := by
  have hphase : Complex.normSq (phase (Φ x)) = 1 := by
    simp only [phase, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq (Φ x)]
  rw [polarField, Complex.normSq_mul, hphase, mul_one]
  simpa only [Complex.normSq_ofReal, ← pow_two] using Real.sq_sqrt hρ

/-- Born's identity in the source's conjugate-product notation. -/
theorem actionField_conj_mul (p : MassiveParameters) (ρ S : E → ℝ) (x : E)
    (hρ : 0 ≤ ρ x) :
    conj (actionField p ρ S x) * actionField p ρ S x = (ρ x : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self, actionField, polarField_normSq ρ _ x hρ]

/-- The complex kinetic expression is the real signed norm contraction. -/
theorem complexKinetic_eq_realKinetic (dψ : Fin 4 → ℂ) :
    complexKinetic dψ = (realKinetic dψ : ℂ) := by
  simp only [complexKinetic, realKinetic, Complex.ofReal_sub,
    Complex.normSq_eq_conj_mul_self]

/-- The density-phase first jet gives the canonical real kinetic density. -/
theorem polar_kinetic_identity (p : MassiveParameters) (ρ S : ℝ)
    (dρ dS : Covector) (hρ : 0 < ρ) :
    p.hbar ^ 2 * realKinetic
        (fun μ => polarTangent ρ (S / p.hbar) (dρ μ) (dS μ / p.hbar)) =
      ρ * (minkowski dS dS + p.hbar ^ 2 / 4 *
        minkowski (fun μ => dρ μ / ρ) (fun μ => dρ μ / ρ)) := by
  simp only [realKinetic, polarTangent_normSq _ _ _ _ hρ, minkowski]
  have hh : p.hbar ≠ 0 := ne_of_gt p.hbar_pos
  have hr : ρ ≠ 0 := ne_of_gt hρ
  field_simp
  ring

/-- The complete first-jet action-density equality, including the mass term. -/
theorem polar_action_density_identity (p : MassiveParameters) (ρ S : ℝ)
    (dρ dS : Covector) (hρ : 0 < ρ) :
    kgDensity p ((Real.sqrt ρ : ℂ) * phase (S / p.hbar))
        (fun μ => polarTangent ρ (S / p.hbar) (dρ μ) (dS μ / p.hbar)) =
      (hydroDensity p ρ dS (fun μ => dρ μ / ρ) : ℂ) := by
  have hborn := actionField_conj_mul p (fun _ : ℝ => ρ) (fun _ => S) 0 hρ.le
  change conj ((Real.sqrt ρ : ℂ) * phase (S / p.hbar)) *
    ((Real.sqrt ρ : ℂ) * phase (S / p.hbar)) = (ρ : ℂ) at hborn
  rw [kgDensity, hborn, complexKinetic_eq_realKinetic]
  have hkin := polar_kinetic_identity p ρ S dρ dS hρ
  have hreal : p.hbar ^ 2 * realKinetic
        (fun μ => polarTangent ρ (S / p.hbar) (dρ μ) (dS μ / p.hbar)) -
      p.m ^ 2 * p.c ^ 2 * ρ = hydroDensity p ρ dS (fun μ => dρ μ / ρ) := by
    rw [hkin, hydroDensity]
    ring
  exact_mod_cast hreal

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The source's literal field density, differentiating the conjugate field
before taking the four signed coordinate products. -/
noncomputable def fieldDensity (p : MassiveParameters) (ψ : E → ℂ)
    (x : E) (v : Fin 4 → E) : ℂ :=
  (p.hbar : ℂ) ^ 2 *
      (fderiv ℝ (fun y => conj (ψ y)) x (v 0) * fderiv ℝ ψ x (v 0) -
       fderiv ℝ (fun y => conj (ψ y)) x (v 1) * fderiv ℝ ψ x (v 1) -
       fderiv ℝ (fun y => conj (ψ y)) x (v 2) * fderiv ℝ ψ x (v 2) -
       fderiv ℝ (fun y => conj (ψ y)) x (v 3) * fderiv ℝ ψ x (v 3)) -
    (p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2 * (conj (ψ x) * ψ x)

/-- Conjugation commutes with the actual real differential of a complex field. -/
theorem fderiv_conj_apply {ψ : E → ℂ} {x : E}
    (hψ : DifferentiableAt ℝ ψ x) (v : E) :
    fderiv ℝ (fun y => conj (ψ y)) x v = conj (fderiv ℝ ψ x v) := by
  have hd : HasFDerivAt (fun y => conj (ψ y))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ ψ x)) x := by
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply] using
      Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x hψ.hasFDerivAt
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply]

/-- The literal source density agrees with the signed squared-norm density. -/
theorem fieldDensity_eq_kgDensity (p : MassiveParameters) {ψ : E → ℂ} {x : E}
    (hψ : DifferentiableAt ℝ ψ x) (v : Fin 4 → E) :
    fieldDensity p ψ x v = kgDensity p (ψ x) (fun μ => fderiv ℝ ψ x (v μ)) := by
  simp only [fieldDensity, fderiv_conj_apply hψ, kgDensity, complexKinetic]

/-- The actual differential of the action phase divided by `ℏ`. -/
theorem fderiv_action_phase_apply (p : MassiveParameters) {S : E → ℝ} {x : E}
    (hS : DifferentiableAt ℝ S x) (v : E) :
    fderiv ℝ (fun y => S y / p.hbar) x v = fderiv ℝ S x v / p.hbar := by
  have hd : HasFDerivAt (fun y => S y / p.hbar)
      (p.hbar⁻¹ • fderiv ℝ S x) x := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.hasFDerivAt.const_mul p.hbar⁻¹
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Equality of the source action densities for actual source-field derivatives,
evaluated on any four supplied tangent directions. Coordinate vectors recover
the flat spacetime formula with `x⁰ = ct`. -/
theorem action_density_identity (p : MassiveParameters) {ρ S : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x)
    (hpos : 0 < ρ x) (v : Fin 4 → E) :
    kgDensity p (actionField p ρ S x)
        (fun μ => fderiv ℝ (actionField p ρ S) x (v μ)) =
      (hydroDensity p (ρ x) (fun μ => fderiv ℝ S x (v μ))
        (fun μ => fderiv ℝ (fun y => Real.log (ρ y)) x (v μ)) : ℂ) := by
  have hphase : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.const_mul p.hbar⁻¹
  simp only [actionField, fderiv_polarField_apply hρ hphase hpos,
    fderiv_action_phase_apply p hS, fderiv_log_density_apply hρ hpos]
  exact polar_action_density_identity p (ρ x) (S x)
    (fun μ => fderiv ℝ ρ x (v μ)) (fun μ => fderiv ℝ S x (v μ)) hpos

/-- The full local action-density equality in the source's literal
derivative-of-conjugate notation. -/
theorem field_action_density_identity (p : MassiveParameters) {ρ S : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x)
    (hpos : 0 < ρ x) (v : Fin 4 → E) :
    fieldDensity p (actionField p ρ S) x v =
      (hydroDensity p (ρ x) (fun μ => fderiv ℝ S x (v μ))
        (fun μ => fderiv ℝ (fun y => Real.log (ρ y)) x (v μ)) : ℂ) := by
  have hphase : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.const_mul p.hbar⁻¹
  have hψ : DifferentiableAt ℝ (actionField p ρ S) x :=
    differentiableAt_polarField hρ hphase hpos
  rw [fieldDensity_eq_kgDensity p hψ v]
  exact action_density_identity p hρ hS hpos v

end FoliationQM.ActionDensity
