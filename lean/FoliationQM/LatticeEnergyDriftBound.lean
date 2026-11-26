module

public import FoliationQM.LatticePolarEnergyBalance
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative energy variation on a regular lattice region

For a fixed grid with every signed amplitude bounded away from zero, the
regularizer changes the energy at a rate controlled by its squared width.
The coefficient below retains the physical kinetic scale, the radial stencil
and the site amplitude speeds.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeEnergyDriftBound

open LatticePolarEnergyBalance LatticeClockRegularization LatticeConservation
open LatticeLagHamiltonian LatticeRegularizedFlow LatticePolarStencil Set

/-- Sum of the absolute site coefficients in the energy balance before applying
the regularization fraction. -/
def driftWeight {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ : Fin n → ℝ) : ℝ :=
  ∑ i, |(-2 * h) * sourceAmplitudeRHS p.ellC p.c h R φ i *
    (p.ellC ^ 2 / (2 * h ^ 2)) * radial R φ i|

/-- At a fixed lattice state separated from zero by δ the energy drift has an
explicit bound quadratic in the regulator width. -/
theorem away_bound {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (R φ : Fin n → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hr : ∀ i, δ ≤ |R i|) :
    |drift p h ε R φ| ≤ driftWeight p h R φ * (ε^2 / δ^2) := by
  unfold drift driftWeight
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul, abs_of_nonneg (defectFraction_mem_unitInterval ε (R i)).1]
  exact mul_le_mul_of_nonneg_left (defectFraction_le_of_abs_ge ε (R i) δ hδ (hr i)) (abs_nonneg _)

/-- A solution staying δ away from all nodes with site-weight sum at most M
satisfies the corresponding finite-interval energy bound. -/
theorem interval_bound {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (ε : ℝ) (V : Fin n → ℝ) (γ : ℝ → State n) {a b δ M : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (field p h ε V (γ t)) t)
    (hr : ∀ t ∈ Icc a b, ∀ i, δ ≤ |(γ t).1 i|)
    (hM : ∀ t ∈ Icc a b, driftWeight p h (γ t).1 (lagPhase p (γ t).2) ≤ M) :
    |energyAlong p h V (γ b) - energyAlong p h V (γ a)| ≤ M * (ε^2 / δ^2) * (b-a) := by
  apply norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t => energyAlong p h V (γ t))
    (f' := fun t => drift p h ε (γ t).1 (lagPhase p (γ t).2)) _ _ b (right_mem_Icc.mpr hab)
  · intro t ht
    have hn (i : Fin n) : (γ t).1 i ≠ 0 ∨ ε ≠ 0 :=
      Or.inl (abs_pos.mp (lt_of_lt_of_le hδ (hr t ht i)))
    exact (energy_path p hh ε V γ t hn (hγ t ht)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
    exact (away_bound p h ε _ _ hδ (hr t ht')).trans
      (mul_le_mul_of_nonneg_right (hM t ht') (by positivity))

end FoliationQM.LatticeEnergyDriftBound
