module

public import FoliationQM.TwoBodyPolarSecondJet
public import FoliationQM.TwoBodyPolarContinuity

/-!
# The real and imaginary parts of the two-particle Schrödinger equation

Removing the polar phase from the Schrödinger residual yields the
Hamilton–Jacobi–Bohm and continuity residuals, with their physical
coefficients. Each particle contributes its own mass-weighted Laplacian.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodySchrodingerResidual

open TwoBodyCoordinates TwoBodyActionDensity TwoBodyPolarWave TwoBodyPolarSecondJet
open TwoBodyPolarContinuity
open scoped BigOperators

/-- The left side minus the right side of the physical two-particle Schrödinger equation. -/
def schrodinger (h m₁ m₂ : ℝ) (V : Point → ℝ) (ψ : Point → ℂ) (p : Point) : ℂ :=
  Complex.I * (h : ℂ) * Dt ψ p +
    (∑ j, ((h ^ 2 / (2 * mass m₁ m₂ j) : ℝ) : ℂ) * D (axis j) (D (axis j) ψ) p) -
    (V p : ℂ) * ψ p

/-- The nonlocal quantum potential in the signed amplitude coordinate. -/
def quantum (h m₁ m₂ : ℝ) (R : Point → ℝ) (p : Point) : ℝ :=
  -(∑ j, h ^ 2 / (2 * mass m₁ m₂ j) * D (axis j) (D (axis j) R) p) / R p

/-- The action-phase Hamilton–Jacobi residual, including the Bohm potential. -/
def hamiltonJacobi (h m₁ m₂ : ℝ) (V R S : Point → ℝ) (p : Point) : ℝ :=
  Dt S p + (∑ j, (D (axis j) S p) ^ 2 / (2 * mass m₁ m₂ j)) + V p +
    quantum h m₁ m₂ R p

/-- Splitting the kinetic sum gives the separate physical particle Laplacians. -/
theorem schrodinger_laplacians (h m₁ m₂ : ℝ) (V : Point → ℝ) (ψ : Point → ℂ) (p : Point) :
    schrodinger h m₁ m₂ V ψ p = Complex.I * (h : ℂ) * Dt ψ p +
      (((h ^ 2 / (2 * m₁) : ℝ) : ℂ) * lap₁ ψ p + ((h ^ 2 / (2 * m₂) : ℝ) : ℂ) * lap₂ ψ p) -
      (V p : ℂ) * ψ p := by
  simp only [schrodinger, Fintype.sum_sum_type, mass, axis, Sum.elim_inl, Sum.elim_inr,
    lap₁, lap₂, D₁, D₂, Finset.mul_sum]

/-- The quantum potential is the sum of the two inverse-mass-weighted amplitude curvatures. -/
theorem quantum_laplacians (h m₁ m₂ : ℝ) (R : Point → ℝ) (p : Point) :
    quantum h m₁ m₂ R p = -(h ^ 2 / (2 * m₁) * lap₁ R p +
      h ^ 2 / (2 * m₂) * lap₂ R p) / R p := by
  simp only [quantum, Fintype.sum_sum_type, mass, axis, Sum.elim_inl, Sum.elim_inr,
    lap₁, lap₂, D₁, D₂, Finset.mul_sum]

private theorem rotate_residual (z : ℂ) (h m₁ m₂ : ℝ) (V : Point → ℝ) (ψ : Point → ℂ) (p : Point) :
    z * schrodinger h m₁ m₂ V ψ p =
      Complex.I * ((h : ℂ) * (z * Dt ψ p)) +
        (∑ j, ((h ^ 2 / (2 * mass m₁ m₂ j) : ℝ) : ℂ) * (z * D (axis j) (D (axis j) ψ) p)) -
        (V p : ℂ) * (z * ψ p) := by
  simp only [schrodinger, mul_sub, mul_add, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

private theorem real_kinetic {h : ℝ} (hh : h ≠ 0) (m r s a : ℝ) :
    h ^ 2 / (2 * m) * (a - r * (s / h) ^ 2) =
      h ^ 2 / (2 * m) * a - r * (s ^ 2 / (2 * m)) := by
  have hc : h ^ 2 * (s / h) ^ 2 = s ^ 2 := by field_simp
  calc
    _ = h ^ 2 / (2 * m) * a - r * (h ^ 2 * (s / h) ^ 2) / (2 * m) := by ring
    _ = _ := by rw [hc]; ring

private theorem imag_kinetic {h r : ℝ} (hh : h ≠ 0) (hr : r ≠ 0) (m a b c : ℝ) :
    h ^ 2 / (2 * m) * ((2 * a * b + r * c) / h) =
      h / (2 * r) * ((2 * r * a * b + r ^ 2 * c) / m) := by
  by_cases hm : m = 0
  · simp [hm]
  · field_simp

/-- The phase-rotated residual has real part minus amplitude times the physical
Hamilton–Jacobi–Bohm residual and imaginary part proportional to the density continuity law. -/
theorem rotated_parts {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) (V : Point → ℝ)
    {R S : Point → ℝ} {p : Point} (hR : ContDiffAt ℝ 2 R p) (hS : ContDiffAt ℝ 2 S p)
    (hn : R p ≠ 0) :
    (star (phase (S p / h)) * schrodinger h m₁ m₂ V (wave h R S) p).re =
      -R p * hamiltonJacobi h m₁ m₂ V R S p ∧
    (star (phase (S p / h)) * schrodinger h m₁ m₂ V (wave h R S) p).im =
      (h / (2 * R p)) * continuity m₁ m₂ (fun z => R z ^ 2) S p := by
  have hdR := hR.differentiableAt (by norm_num)
  have hdS := hS.differentiableAt (by norm_num)
  rw [rotate_residual, rotate_value]
  constructor
  · simp only [Complex.add_re, Complex.sub_re, Complex.I_mul_re, Complex.im_ofReal_mul,
      Complex.re_sum, Complex.re_ofReal_mul, Complex.ofReal_re, rotate_time_im h hdR hdS,
      rotate_second_re h hR hS, real_kinetic hh, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hamiltonJacobi, quantum]
    field_simp
    ring
  · simp only [Complex.add_im, Complex.sub_im, Complex.I_mul_im, Complex.re_ofReal_mul,
      Complex.im_sum, Complex.im_ofReal_mul, Complex.ofReal_im, mul_zero, sub_zero,
      rotate_time_re h hdR hdS, rotate_second_im h hR hS, imag_kinetic hh hn,
      ← Finset.mul_sum, continuity_sq m₁ m₂ hdR hS]
    field_simp

end FoliationQM.TwoBodySchrodingerResidual
