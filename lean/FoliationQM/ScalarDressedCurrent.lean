module

public import FoliationQM.ScalarPhaseCurrent
public import FoliationQM.NodalClockForm

/-! On a positive scalar polar chart, the complex bilinear current in v13
`eq:noether_current` is minus the density times the actual phase gradient
divided by the bare mass. Its timelike decomposition uses the previously
constructed normalized velocity and Fisher-dressed rest density. -/

@[expose] public section
noncomputable section
namespace FoliationQM.ScalarDressedCurrent

open ActionDensity PolarDifferential PolarSecondDifferential DressedMassDensityVariation
open scoped ComplexConjugate ContDiff

/-- On the positive polar chart the physical current agrees with the lower
phase-gradient current, including its sign and bare-mass normalization. -/
theorem current_actionField (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) (μ : Fin 4) :
    ScalarPhaseCurrent.current p (actionField p ρ S) x μ = -(ρ x / p.m) * phaseDifferential S x μ := by
  let ψ := actionField p ρ S
  let v := Madelung.coordinateVector μ
  have hc : conj (ψ x) * ψ x = (ρ x : ℂ) := actionField_conj_mul p ρ S x hp.le
  have hz : ψ x ≠ 0 := fun h => (Complex.ofReal_ne_zero.mpr hp.ne') (by rw [← hc, h]; simp)
  have hf : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv] using hS.mul_const p.hbar⁻¹
  have he := congrArg (fun w : Covector [⋀^Fin 1]→L[ℝ] ℝ => w (fun _ => v)) <|
    NodalClockForm.angleForm_polar hρ hf hp
  change ((ψ x)⁻¹ * fderiv ℝ ψ x v).im =
    HamiltonJacobiPullback.phaseDifferential (fun y => S y / p.hbar) x (fun _ => v) at he
  rw [HamiltonJacobiPullback.phaseDifferential_apply, fderiv_action_phase_apply p hS] at he
  have heq : conj (ψ x) * fderiv ℝ ψ x v =
      (ρ x : ℂ) * ((ψ x)⁻¹ * fderiv ℝ ψ x v) := by rw [← hc]; field_simp
  change -(p.hbar / p.m) * (conj (ψ x) * fderiv ℝ ψ x v).im = -(ρ x / p.m) * fderiv ℝ S x v
  rw [heq, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, he]
  simp only [zero_mul, add_zero]
  field_simp [p.m_pos.ne', p.hbar_pos.ne']

/-- The source's comoving scalar density on the regular timelike domain. -/
def restDensity (p : MassiveParameters) (ρ S : Covector → ℝ) (x : Covector) : ℝ :=
  ρ x * effectiveMass p.c (phaseDifferential S x) / p.m

/-- The current of the original complex wave has positive dressed rest density
and factors through the same normalized lower velocity as the mass identity. -/
theorem current_eq_restDensity_velocity (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x)
    (ht : 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)) :
    0 < restDensity p ρ S x ∧ ScalarPhaseCurrent.current p (actionField p ρ S) x =
      restDensity p ρ S x • velocityCovector p.c (phaseDifferential S x) := by
  refine ⟨div_pos (mul_pos hp (effectiveMass_pos p.c_pos ht)) p.m_pos, ?_⟩
  funext μ
  rw [current_actionField p hρ hS hp]
  exact current_factorization p (phaseDifferential S x) ht (ρ x) μ

/-- A scalar-action extremal has conserved complex current everywhere on its
positive chart. At its timelike points the same current has the dressed factorization. -/
theorem of_scalar_extremal (p : MassiveParameters) {ρ S : Covector → ℝ} {V : Set Covector}
    (hV : IsOpen V) (hρ : ∀ x ∈ V, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ V, ContDiffAt ℝ ∞ S x)
    (hp : ∀ x ∈ V, 0 < ρ x)
    (hst : RelativePolarStationaryAction.RelativePolarStationaryOn p ρ S Madelung.coordinateVector V)
    {x : Covector} (hx : x ∈ V) :
    ScalarPhaseCurrent.divergence p (actionField p ρ S) x = 0 ∧
    (0 < minkowski (phaseDifferential S x) (phaseDifferential S x) →
      0 < restDensity p ρ S x ∧ ScalarPhaseCurrent.current p (actionField p ρ S) x =
        restDensity p ρ S x • velocityCovector p.c (phaseDifferential S x)) := by
  have hkg := (RelativePolarStationaryAction.relativePolarStationaryOn_iff_kleinGordon p hV hρ hS hp).mp hst x hx
  have hψ := (OpenPolarVariations.contDiffAt_actionField p (hρ x hx) (hS x hx) (hp x hx)).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ by simp)
  exact ⟨ScalarPhaseCurrent.divergence_eq_zero_of_kg p hψ hkg,
    current_eq_restDensity_velocity p ((hρ x hx).differentiableAt (by simp))
      ((hS x hx).differentiableAt (by simp)) (hp x hx)⟩

end FoliationQM.ScalarDressedCurrent
