module

public import FoliationQM.LatticeLinkCurrent
public import FoliationQM.LatticePolarSignChange

/-!
# Regularized site velocity from the two adjacent link currents

The regularized drift in v13 Eq. 9 and in the reference solver is the
average of the two oriented link currents divided by the regularized site
density. The site velocity is determined by the reconstructed complex wave.
Away from a node the change from the zero-width velocity is an explicit
density-dependent damping factor.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeStaggeredVelocity

open LatticeLinkCurrent LatticeConservation LatticeComplexEnergy LatticeLagHamiltonian
open LatticeClockRegularization LatticePolarSignChange

/-- Velocity at a site, using its adjacent oriented currents and regularized density. -/
def siteVelocity {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (R φ : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  (plus p h R φ i + minus p h R φ i) / (2 * ((R i)^2 + ε^2))

/-- The lag-coordinate formula evaluated by the reference solver, with the signs
of its forward and backward phase differences and its replicated endpoints. -/
theorem lag_formula {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (R τ : Fin n → ℝ)
    (i : Fin n) :
    siteVelocity p h ε R (lagPhase p τ) i =
      (1/2 : ℝ) * (R i * R (nextNode i) * (p.ellC * p.c / h) *
        Real.sin ((p.c / p.ellC) * (τ (nextNode i) - τ i)) +
        R (prevNode i) * R i * (p.ellC * p.c / h) *
        Real.sin ((p.c / p.ellC) * (τ i - τ (prevNode i)))) / ((R i)^2 + ε^2) := by
  simp only [siteVelocity, plus, minus, link, lagPhase, mul_sub, div_mul_eq_div_div]
  ring

/-- Both currents are imaginary parts of adjacent complex products, and their
denominator uses the complex squared modulus at the observation site. -/
theorem complex_formula {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (R φ : Fin n → ℝ)
    (i : Fin n) :
    siteVelocity p h ε R φ i =
      (p.ellC * p.c / h) * ((star (wave R φ i) * wave R φ (nextNode i)).im +
        (star (wave R φ (prevNode i)) * wave R φ i).im) /
        (2 * (Complex.normSq (wave R φ i) + ε^2)) := by
  rw [siteVelocity, plus_eq_im, minus_eq_im, wave_normSq, ← mul_add]

/-- Any two sets of real polar coordinates reconstructing the same wave have
the same velocity at every site. -/
theorem congr_wave {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (R φ S ψ : Fin n → ℝ)
    (hw : wave R φ = wave S ψ) (i : Fin n) :
    siteVelocity p h ε R φ i = siteVelocity p h ε S ψ i := by
  rw [complex_formula, hw, ← complex_formula]

/-- Independent signed-amplitude flips and simultaneous phase half turns at
any sites preserve the regularized velocity. -/
theorem half_turn {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (flip : Fin n → Bool)
    (R φ : Fin n → ℝ) (i : Fin n) :
    siteVelocity p h ε (amplitude flip R) (angle flip φ) i = siteVelocity p h ε R φ i :=
  congr_wave p h ε _ _ _ _ (wave_change flip R φ) i

/-- A common change of phase origin leaves the velocity unchanged. -/
theorem constant_phase_shift {n : ℕ} (p : MassiveParameters) (h ε a : ℝ)
    (R φ : Fin n → ℝ) (i : Fin n) :
    siteVelocity p h ε R (fun j => φ j + a) i = siteVelocity p h ε R φ i := by
  simp [siteVelocity, plus, minus, link]

/-- At a node both adjacent oriented currents vanish, so the site velocity
vanishes for every positive regulator width. -/
theorem at_node {n : ℕ} (p : MassiveParameters) (h : ℝ) {ε : ℝ} (_hε : 0 < ε)
    (R φ : Fin n → ℝ) (i : Fin n) (hi : R i = 0) : siteVelocity p h ε R φ i = 0 := by
  simp [siteVelocity, plus, minus, link, hi]

/-- At a nonzero amplitude the positive-width velocity equals the raw velocity
times the retained density fraction. The identity also holds at width zero. -/
theorem damping {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (R φ : Fin n → ℝ)
    (i : Fin n) (hR : R i ≠ 0) :
    siteVelocity p h ε R φ i = (R i)^2 / ((R i)^2 + ε^2) * siteVelocity p h 0 R φ i := by
  simp only [siteVelocity, zero_pow (by decide : 2 ≠ 0), add_zero]
  field_simp [hR, (denominator_pos ε (R i) (Or.inl hR)).ne']

/-- Above an amplitude floor δ, the difference between the regularized and
zero-width velocities is at most ε²/δ² times the absolute zero-width velocity. -/
theorem damping_error_le {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (R φ : Fin n → ℝ)
    (i : Fin n) {δ : ℝ} (hδ : 0 < δ) (hr : δ ≤ |R i|) :
    |siteVelocity p h ε R φ i - siteVelocity p h 0 R φ i| ≤
      (ε^2/δ^2) * |siteVelocity p h 0 R φ i| := by
  have hR := abs_pos.mp (hδ.trans_le hr)
  have hsum : (R i)^2 / ((R i)^2 + ε^2) + defectFraction ε (R i) = 1 := by
    unfold defectFraction
    rw [← add_div, div_self (denominator_pos ε (R i) (Or.inl hR)).ne']
  have he : siteVelocity p h ε R φ i - siteVelocity p h 0 R φ i =
      -(defectFraction ε (R i) * siteVelocity p h 0 R φ i) := by
    rw [damping p h ε R φ i hR]
    linear_combination (siteVelocity p h 0 R φ i) * hsum
  rw [he, abs_neg, abs_mul, abs_of_nonneg (defectFraction_mem_unitInterval ε (R i)).1]
  exact mul_le_mul_of_nonneg_right (defectFraction_le_of_abs_ge ε (R i) δ hδ hr) (abs_nonneg _)

end FoliationQM.LatticeStaggeredVelocity
