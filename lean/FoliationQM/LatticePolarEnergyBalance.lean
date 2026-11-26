module

public import FoliationQM.LatticeRegularizedFlow

/-!
# Energy balance of the regularized polar lattice

The reciprocal substitution in the real equations of v13 lines 215–220
changes the kinetic part of the geometric energy derivative. The two
site-potential contributions cancel exactly. The residual drift vanishes at
zero width on every time interval where the signed-amplitude chart is regular.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticePolarEnergyBalance

open LatticeConservation LatticePolarStencil LatticePolarVariation LatticeLagHamiltonian
open LatticeClockRegularization LatticeRegularizedFlow WeightedLatticeHamiltonian

/-- Weighted geometric Hamiltonian evaluated in physical lag-clock coordinates. -/
def energyAlong {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) (x : State n) : ℝ :=
  geometric p h x.1 (lagPhase p x.2) V

/-- Sum of the site energy rates produced by the lost kinetic fraction. -/
def drift {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (R φ : Fin n → ℝ) : ℝ :=
  ∑ i, -2 * h * sourceAmplitudeRHS p.ellC p.c h R φ i *
    (p.ellC ^ 2 / (2 * h ^ 2)) * radial R φ i * defectFraction ε (R i)

/-- The radial and angular contributions to the site energy rate cancel except
for the lost fraction of the kinetic clock term. -/
theorem site_balance {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (R τ V : Fin n → ℝ)
    (i : Fin n) (hn : R i ≠ 0 ∨ ε ≠ 0) :
    radialGradient p h R (lagPhase p τ) V i * sourceAmplitudeRHS p.ellC p.c h R (lagPhase p τ) i +
        phaseGradient p h R (lagPhase p τ) i * ((p.c / p.ellC) * lagRate p h ε R (lagPhase p τ) V i) =
      -2 * h * sourceAmplitudeRHS p.ellC p.c h R (lagPhase p τ) i * (p.ellC ^ 2 / (2 * h ^ 2)) *
        radial R (lagPhase p τ) i * defectFraction ε (R i) := by
  rw [← mul_assoc (phaseGradient ..), lag_gradient_eq_amplitude_rate, radialGradient, lagRate]
  have hret : R i * reciprocal ε (R i) = 1 - defectFraction ε (R i) :=
    eq_sub_of_add_eq (mul_reciprocal_add_defectFraction ε (R i) hn)
  calc
    _ = 2 * h * sourceAmplitudeRHS p.ellC p.c h R (lagPhase p τ) i *
        (p.ellC ^ 2 / (2 * h ^ 2)) * radial R (lagPhase p τ) i * (R i * reciprocal ε (R i) - 1) := by ring
    _ = _ := by rw [hret]; ring

/-- Actual derivative of the normalized geometric energy on a source integral
curve, including nodes whenever the regularization width is nonzero. -/
theorem energy_path {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h) (ε : ℝ)
    (V : Fin n → ℝ) (γ : ℝ → State n) (t : ℝ) (hn : ∀ i, (γ t).1 i ≠ 0 ∨ ε ≠ 0)
    (hγ : HasDerivAt γ (field p h ε V (γ t)) t) :
    HasDerivAt (fun s => energyAlong p h V (γ s)) (drift p h ε (γ t).1 (lagPhase p (γ t).2)) t := by
  obtain ⟨hR, hτ⟩ := component_rates p h ε V γ t hγ
  have hg := geometric_path p hh (fun s => (γ s).1) (fun s => lagPhase p (γ s).2)
    V _ _ t hR (fun i => (hτ i).const_mul (p.c / p.ellC))
  apply hg.congr_deriv
  exact Finset.sum_congr rfl fun i _ => site_balance p h ε (γ t).1 (γ t).2 V i (hn i)

/-- The algebraic drift has zero width factor at every site. -/
theorem drift_zero_width {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ : Fin n → ℝ) :
    drift p h 0 R φ = 0 := by simp [drift, defectFraction]

/-- On the nonzero signed chart the unregularized source field has zero energy derivative. -/
theorem energy_path_zero_width {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (V : Fin n → ℝ) (γ : ℝ → State n) (t : ℝ) (hn : ∀ i, (γ t).1 i ≠ 0)
    (hγ : HasDerivAt γ (field p h 0 V (γ t)) t) :
    HasDerivAt (fun s => energyAlong p h V (γ s)) 0 t := by
  simpa only [drift_zero_width] using energy_path p hh 0 V γ t (fun i => Or.inl (hn i)) hγ

/-- The geometric energies at any two times in a nonnodal open interval agree
along a solution of the unregularized polar equations on that interval. -/
theorem energy_eq_on_interval {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (V : Fin n → ℝ) (γ : ℝ → State n) {a b : ℝ} (hn : ∀ t ∈ Set.Ioo a b, ∀ i, (γ t).1 i ≠ 0)
    (hγ : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (field p h 0 V (γ t)) t)
    {s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    energyAlong p h V (γ s) = energyAlong p h V (γ t) := by
  have hd (u : ℝ) (hu : u ∈ Set.Ioo a b) := energy_path_zero_width p hh V γ u (hn u hu) (hγ u hu)
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt) (fun u hu => (hd u hu).deriv) hs ht

end FoliationQM.LatticePolarEnergyBalance
