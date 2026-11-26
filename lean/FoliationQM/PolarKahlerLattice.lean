module

public import FoliationQM.Conventions

@[expose] public section

/-!
# First algebraic core of the polar lattice

Source: v13, Section 2, `eq:polar_kahler_lattice` and
`eq:s1_lattice_hamiltonian`, including the adjacent canonicalization paragraph.
These are kind A identities for arbitrary signed real amplitudes and real phase
lifts. They prove the individual edge identities, not the semidiscrete evolution,
boundary convention, regularization residual, or a numerical conservation law.
-/

namespace FoliationQM.PolarKahlerLattice

/-- Euler-coordinate expansion used to check the source edge identity. -/
theorem phase_re (φ : ℝ) : (phase φ).re = Real.cos φ := by
  simp [phase]

/-- Euler-coordinate expansion used to check the source edge identity. -/
theorem phase_im (φ : ℝ) : (phase φ).im = Real.sin φ := by
  simp [phase]

/-- Source `eq:polar_kahler_lattice`, complete algebraic single-edge subclaim.
There is no positivity restriction on either amplitude. -/
theorem geometric_edge_normSq (Ra Rb φa φb : ℝ) :
    Rb * Ra * (1 - Real.cos (φb - φa)) + (Rb - Ra) ^ 2 / 2 =
      Complex.normSq ((Rb : ℂ) * phase φb - (Ra : ℂ) * phase φa) / 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, phase_re, phase_im, Real.cos_sub]
  nlinarith [congrArg (fun x : ℝ => Ra ^ 2 * x) (Real.cos_sq_add_sin_sq φa),
    congrArg (fun x : ℝ => Rb ^ 2 * x) (Real.cos_sq_add_sin_sq φb)]

/-- The source single-edge identity stated with the actual complex norm. -/
theorem geometric_edge_norm (Ra Rb φa φb : ℝ) :
    Rb * Ra * (1 - Real.cos (φb - φa)) + (Rb - Ra) ^ 2 / 2 =
      ‖(Rb : ℂ) * phase φb - (Ra : ℂ) * phase φa‖ ^ 2 / 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  exact geometric_edge_normSq Ra Rb φa φb

/-- Source `eq:s1_lattice_hamiltonian`, complete algebraic coefficient-gap subclaim. -/
theorem arithmetic_geometric_gap (Ra Rb : ℝ) :
    (Rb ^ 2 + Ra ^ 2) / 2 - Rb * Ra = (Rb - Ra) ^ 2 / 2 := by
  ring

/-- Exact edge defect before multiplication by lattice/clock scale factors.
This is the algebraic subclaim underlying the source's order estimate. -/
theorem arithmetic_geometric_edge_defect (Ra Rb Δφ : ℝ) :
    ((Rb ^ 2 + Ra ^ 2) / 2 * (1 - Real.cos Δφ) + (Rb - Ra) ^ 2 / 2) -
      (Rb * Ra * (1 - Real.cos Δφ) + (Rb - Ra) ^ 2 / 2) =
      (Rb - Ra) ^ 2 / 2 * (1 - Real.cos Δφ) := by
  ring

/-- A half-turn negates the unit complex phase. -/
theorem phase_add_pi (φ : ℝ) : phase (φ + Real.pi) = -phase φ := by
  apply Complex.ext <;> simp [phase_re, phase_im, Real.cos_add_pi, Real.sin_add_pi]

/-- Source Section 2 canonicalization, valid also at amplitude zero.
The indicator is represented explicitly by `if R < 0 then 1 else 0`. -/
theorem signed_amplitude_canonicalization (R φ : ℝ) :
    (R : ℂ) * phase φ =
      (|R| : ℝ) * phase (φ + Real.pi * (if R < 0 then (1 : ℝ) else 0)) := by
  by_cases hR : R < 0
  · simp [hR, abs_of_neg hR, phase_add_pi]
  · simp [hR, abs_of_nonneg (le_of_not_gt hR)]

/-- Integer full-turn changes of a real lift preserve its actual exponential.
This supports phase-lift replacement; no modulo-reduction algorithm is claimed. -/
theorem phase_add_int_mul_two_pi (φ : ℝ) (k : ℤ) :
    phase (φ + (k : ℝ) * (2 * Real.pi)) = phase φ := by
  apply Complex.ext <;> simp [phase_re, phase_im]

end FoliationQM.PolarKahlerLattice
