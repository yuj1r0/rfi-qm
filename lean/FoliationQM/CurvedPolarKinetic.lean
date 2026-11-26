module

public import FoliationQM.CurvedGreenBoundary
public import FoliationQM.CurvedGradientCovariance
public import FoliationQM.PolarKahlerGeometry

/-!
# The covariant polar kinetic identity

Pairing the genuine polar differentials in two arbitrary directions gives
the phase and logarithmic-density terms in v13 Eq. `eq:master_variational_equivalence`.
Contracting every diagonal and off-diagonal component with the inverse
metric retains these real terms. Hermitian symmetry makes the contraction
real for any complex field when the metric is symmetric.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedPolarKinetic

open LorentzMatrixGroup RealLorentzFrame RNCCoordinateConnection CurvedFluxGreen
open CurvedGradientCovariance ActionDensity PolarKahlerGeometry PolarDifferential
open scoped BigOperators ComplexConjugate Matrix.Norms.Operator

variable {g : Covector → Mat4} {ρ S : Covector → ℝ} {x : Covector}

/-- The first slot of the kinetic form may be written using the actual differential of the conjugate test field. -/
theorem kinetic_conjugate_derivative (g : Covector → Mat4) {u : Covector → ℂ}
    (f : Covector → ℂ) (hu : DifferentiableAt ℝ u x) :
    kinetic g u f x = ∑ i, ∑ j, (g x)⁻¹ i j •
      (fderiv ℝ (fun y => conj (u y)) x (axis i) * fderiv ℝ f x (axis j)) := by
  simp only [kinetic, fderiv_conj_apply hu, Complex.star_def]

/-- Self-pairing in a symmetric metric has zero imaginary part for every complex field. -/
theorem kinetic_im_zero (hs : (g x).IsSymm) (ψ : Covector → ℂ) : (kinetic g ψ ψ x).im = 0 := by
  have he := congrArg Complex.im (CurvedGreenBoundary.kinetic_hermitian hs ψ ψ)
  simp only [Complex.star_def, Complex.conj_im] at he
  linarith

/-- The real polar contribution for two independent test directions, before contraction by a metric. -/
theorem polar_mixed_re (p : MassiveParameters) (hρ : DifferentiableAt ℝ ρ x)
    (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) (v w : Covector) :
    p.hbar ^ 2 * (star (fderiv ℝ (actionField p ρ S) x v) * fderiv ℝ (actionField p ρ S) x w).re =
      ρ x * (fderiv ℝ S x v * fderiv ℝ S x w + p.hbar ^ 2 / 4 *
        (fderiv ℝ (Real.log ∘ ρ) x v * fderiv ℝ (Real.log ∘ ρ) x w)) := by
  have hΦ : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.const_mul p.hbar⁻¹
  have he := congrArg Complex.re (fderiv_polarField_conj_mul hρ hΦ hp v w)
  have hreal (A B : ℝ) : ((A : ℂ) + Complex.I * B).re = A := by simp
  rw [hreal, metric_apply] at he
  simp only [fderiv_action_phase_apply p hS] at he
  change p.hbar ^ 2 * (conj (fderiv ℝ (actionField p ρ S) x v) * fderiv ℝ (actionField p ρ S) x w).re =
    ρ x * (fderiv ℝ S x v * fderiv ℝ S x w + p.hbar ^ 2 / 4 *
      (fderiv ℝ (fun y => Real.log (ρ y)) x v * fderiv ℝ (fun y => Real.log (ρ y)) x w))
  rw [actionField, he, fderiv_log_density_apply hρ hp, fderiv_log_density_apply hρ hp]
  field_simp [p.hbar_pos.ne', hp.ne']
  ring

/-- Contracting the polar derivative with an arbitrary inverse metric gives the real curved kinetic density. -/
theorem polar_kinetic_re (p : MassiveParameters) (g : Covector → Mat4) (hρ : DifferentiableAt ℝ ρ x)
    (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) :
    p.hbar ^ 2 * (kinetic g (actionField p ρ S) (actionField p ρ S) x).re =
      ρ x * (pairing g S S x + p.hbar ^ 2 / 4 * pairing g (Real.log ∘ ρ) (Real.log ∘ ρ) x) := by
  simp only [kinetic, Complex.re_sum, Complex.smul_re, smul_eq_mul, pairing, RNCHalfDensityJet.form_apply,
    components, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  linear_combination (g x)⁻¹ i j * polar_mixed_re p hρ hS hp (axis i) (axis j)

/-- For a symmetric metric the entire complex kinetic term equals the real hydrodynamic expression. -/
theorem polar_kinetic_complex (p : MassiveParameters) (hs : (g x).IsSymm)
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) :
    (p.hbar : ℂ) ^ 2 * kinetic g (actionField p ρ S) (actionField p ρ S) x =
      (ρ x * (pairing g S S x + p.hbar ^ 2 / 4 * pairing g (Real.log ∘ ρ) (Real.log ∘ ρ) x) : ℝ) := by
  rw [← Complex.ofReal_pow]
  apply Complex.ext
  · simpa only [Complex.re_ofReal_mul, Complex.ofReal_re] using polar_kinetic_re p g hρ hS hp
  · simp only [Complex.im_ofReal_mul, Complex.ofReal_im, kinetic_im_zero hs, mul_zero]

end FoliationQM.CurvedPolarKinetic
