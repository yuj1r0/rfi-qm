module

public import FoliationQM.TwoBodyPolarWave
public import FoliationQM.TwoBodyFisherAmplitude
public import FoliationQM.ActionDensity

/-!
# Two-particle action densities

The time term uses physical time. The six spatial terms use the mass of
the particle whose coordinate is differentiated. The positive density
chart identifies the literal Fisher action integrand with the real
quadratic Schrödinger integrand of v13 Theorem 8.2(i).
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyActionDensity

open TwoBodyCoordinates TwoBodyPolarWave
open scoped BigOperators

/-- The three Cartesian coordinates of each of the two particles. -/
abbrev Index := Fin 3 ⊕ Fin 3

/-- Constant spatial tangent vector for a particle-coordinate index. -/
def axis : Index → Point := Sum.elim leftAxis rightAxis

/-- The particle mass associated with a spatial derivative. -/
def mass (m₁ m₂ : ℝ) : Index → ℝ := Sum.elim (fun _ => m₁) (fun _ => m₂)

/-- The source potential is the sum of the separate local particle potentials. -/
def localPotential (V₁ V₂ : Base → ℝ) (p : Point) : ℝ :=
  V₁ p.1 + V₂ (p.1.1,p.2)

/-- The real quadratic density of the time-dependent two-body Schrödinger action. -/
def complexL (h m₁ m₂ : ℝ) (V : Point → ℝ) (ψ : Point → ℂ) (p : Point) : ℝ :=
  -h * (star (ψ p) * Dt ψ p).im -
    (∑ j, h ^ 2 / (2 * mass m₁ m₂ j) * ‖D (axis j) ψ p‖ ^ 2) - V p * ‖ψ p‖ ^ 2

/-- The printed antisymmetric time term equals the real time density, including
its zero imaginary part, with the actual time derivative of the conjugated wave. -/
theorem antisymmetric_time (h : ℝ) {ψ : Point → ℂ} {p : Point} (hψ : DifferentiableAt ℝ ψ p) :
    Complex.I * (h : ℂ) / 2 * (star (ψ p) * Dt ψ p - ψ p * Dt (fun q => star (ψ q)) p) =
      ((-h * (star (ψ p) * Dt ψ p).im : ℝ) : ℂ) := by
  have hd : Dt (fun q => star (ψ q)) p = star (Dt ψ p) :=
    ActionDensity.fderiv_conj_apply hψ timeAxis
  rw [hd]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The inverse-mass-weighted spatial Fisher density in the density coordinate. -/
def fisherL (h m₁ m₂ : ℝ) (ρ : Point → ℝ) (p : Point) : ℝ :=
  ∑ j, h ^ 2 / (8 * mass m₁ m₂ j) * ((D (axis j) ρ p) ^ 2 / ρ p)

/-- The nonlinear action density in the original density and phase variables. -/
def densityL (h m₁ m₂ : ℝ) (V ρ S : Point → ℝ) (p : Point) : ℝ :=
  -ρ p * (Dt S p + (∑ j, (D (axis j) S p) ^ 2 / (2 * mass m₁ m₂ j)) + V p) -
    fisherL h m₁ m₂ ρ p

/-- The nonlinear action density expressed in the signed amplitude and phase variables. -/
def polarL (h m₁ m₂ : ℝ) (V R S : Point → ℝ) (p : Point) : ℝ :=
  -(R p) ^ 2 * (Dt S p + (∑ j, (D (axis j) S p) ^ 2 / (2 * mass m₁ m₂ j)) + V p) -
    ∑ j, h ^ 2 / (2 * mass m₁ m₂ j) * (D (axis j) R p) ^ 2

/-- Splitting the six-coordinate Fisher density recovers the two spatial particle contributions. -/
theorem fisherL_eq_rawDensity (h m₁ m₂ : ℝ) (ρ : Point → ℝ) (p : Point) :
    fisherL h m₁ m₂ ρ p = TwoBodyFisherAmplitude.rawDensity h m₁ m₂ ρ p := by
  simp only [fisherL, Fintype.sum_sum_type, axis, mass, Sum.elim_inl, Sum.elim_inr,
    TwoBodyFisherAmplitude.rawDensity, TwoParticleFisher.coefficient, Finset.mul_sum, D₁, D₂]

private theorem amplitude_sum (h m₁ m₂ : ℝ) (R : Point → ℝ) (p : Point) :
    (∑ j, h ^ 2 / (2 * mass m₁ m₂ j) * (D (axis j) R p) ^ 2) =
      TwoBodyFisherAmplitude.amplitudeDensity h m₁ m₂ R p := by
  simp only [Fintype.sum_sum_type, axis, mass, Sum.elim_inl, Sum.elim_inr,
    TwoBodyFisherAmplitude.amplitudeDensity, Finset.mul_sum, D₁, D₂]

/-- Substitution of the polar wave linearizes the full integrand, including its time term. -/
theorem complexL_wave {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) (V : Point → ℝ)
    {R S : Point → ℝ} {p : Point} (hR : DifferentiableAt ℝ R p) (hS : DifferentiableAt ℝ S p) :
    complexL h m₁ m₂ V (wave h R S) p = polarL h m₁ m₂ V R S p := by
  have cancel (s : ℝ) : h ^ 2 * (s / h) ^ 2 = s ^ 2 := by
    field_simp
  have kinetic_sum :
      (∑ j, h ^ 2 / (2 * mass m₁ m₂ j) * ‖D (axis j) (wave h R S) p‖ ^ 2) =
      (∑ j, h ^ 2 / (2 * mass m₁ m₂ j) * (D (axis j) R p) ^ 2) +
        (R p) ^ 2 * ∑ j, (D (axis j) S p) ^ 2 / (2 * mass m₁ m₂ j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [kinetic h hR hS (axis j)]
    calc
      _ = h ^ 2 / (2 * mass m₁ m₂ j) * (D (axis j) R p) ^ 2 +
          (R p) ^ 2 * (h ^ 2 * (D (axis j) S p / h) ^ 2) / (2 * mass m₁ m₂ j) := by ring
      _ = _ := by rw [cancel]; ring
  rw [complexL, time_term hh hR hS, kinetic_sum, born, polarL]
  ring

/-- Squaring a nonvanishing amplitude gives the same nonlinear action density. -/
theorem densityL_square (h m₁ m₂ : ℝ) (V : Point → ℝ) {R : Point → ℝ} (S : Point → ℝ)
    {p : Point} (hR : DifferentiableAt ℝ R p) (hn : R p ≠ 0) :
    densityL h m₁ m₂ V (fun z => (R z) ^ 2) S p = polarL h m₁ m₂ V R S p := by
  rw [densityL, polarL, fisherL_eq_rawDensity, amplitude_sum,
    TwoBodyFisherAmplitude.rawDensity_sq_eq_amplitude h m₁ m₂ hR hn]

/-- On a positive density chart the original density-phase action and the complex
quadratic action have equal integrands under the printed square-root substitution. -/
theorem complexL_sqrt {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) (V : Point → ℝ)
    {ρ S : Point → ℝ} {p : Point} (hρ : DifferentiableAt ℝ ρ p)
    (hS : DifferentiableAt ℝ S p) (hp : 0 < ρ p) :
    complexL h m₁ m₂ V (wave h (fun z => Real.sqrt (ρ z)) S) p =
      densityL h m₁ m₂ V ρ S p := by
  rw [complexL_wave hh m₁ m₂ V (hρ.sqrt hp.ne') hS, polarL, Real.sq_sqrt hp.le, densityL,
    fisherL_eq_rawDensity, amplitude_sum, TwoBodyFisherAmplitude.rawDensity_eq_sqrt h m₁ m₂ hρ hp]

end FoliationQM.TwoBodyActionDensity
