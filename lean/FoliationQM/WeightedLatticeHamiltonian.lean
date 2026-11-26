module

public import FoliationQM.PolarKahlerLattice
public import FoliationQM.LatticeConservation

/-!
# Weighted arithmetic and geometric lattice Hamiltonians

The finite sums in v13 lines 209–212 and 232–238 use the site measure
Δx, with density R² and a real lift of the positive lag-clock phase.
The reference solver replicates the last site in its forward stencil.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WeightedLatticeHamiltonian

open LatticeConservation
open scoped BigOperators

/-- Forward lattice increment with the replicated right endpoint. -/
def forwardDiff {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : ℝ := f (nextNode i) - f i

/-- Weighted site energy with a supplied coefficient for the phase link.
Both Hamiltonians have the same amplitude-gradient and site-potential terms. -/
def weightedSite {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ V : Fin n → ℝ)
    (i : Fin n) (link : ℝ) : ℝ :=
  h * (link * (p.ellC ^ 2 / h ^ 2) * (1 - Real.cos (forwardDiff φ i)) +
    (p.ellC ^ 2 / 2) * (forwardDiff R i / h) ^ 2 + R i ^ 2 * (V i / (p.m * p.c ^ 2)))

/-- Eq. 10 with the arithmetic mean of the two endpoint densities on each link. -/
def arithmetic {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ V : Fin n → ℝ) : ℝ :=
  ∑ i, weightedSite p h R φ V i ((R (nextNode i) ^ 2 + R i ^ 2) / 2)

/-- The polar Hamiltonian with the product of the two signed amplitudes on each link. -/
def geometric {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ V : Fin n → ℝ) : ℝ :=
  ∑ i, weightedSite p h R φ V i (R (nextNode i) * R i)

/-- At the replicated last site both gradient terms vanish, leaving the
full site-potential contribution even on a one-site grid. -/
theorem terminal_site {n : ℕ} (p : MassiveParameters) (h : ℝ)
    (R φ V : Fin (n + 1) → ℝ) (link : ℝ) :
    weightedSite p h R φ V (Fin.last n) link =
      h * (R (Fin.last n) ^ 2 * (V (Fin.last n) / (p.m * p.c ^ 2))) := by
  simp [weightedSite, forwardDiff, nextNode]

/-- The weighted difference at one site equals its squared amplitude increment
times its phase cost with coefficient ℓ_C²/(2h). -/
theorem weighted_site_defect {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ V : Fin n → ℝ) (i : Fin n) :
    weightedSite p h R φ V i ((R (nextNode i) ^ 2 + R i ^ 2) / 2) -
      weightedSite p h R φ V i (R (nextNode i) * R i) =
        p.ellC ^ 2 / (2*h) * ((forwardDiff R i) ^ 2 * (1 - Real.cos (forwardDiff φ i))) := by
  have hscale : h * (p.ellC ^ 2 / h ^ 2) = p.ellC ^ 2 / h := by field_simp
  calc
    _ = h * (p.ellC ^ 2 / h ^ 2) *
        (((R (nextNode i) ^ 2 + R i ^ 2) / 2 - R (nextNode i) * R i) *
          (1 - Real.cos (forwardDiff φ i))) := by unfold weightedSite; ring
    _ = _ := by
      rw [hscale, PolarKahlerLattice.arithmetic_geometric_gap]
      unfold forwardDiff
      ring

/-- On any finite replicated grid the difference between the two Hamiltonians is
exactly the weighted sum of the phase-modulated squared amplitude increments. -/
theorem weighted_defect {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ V : Fin n → ℝ) :
    arithmetic p h R φ V - geometric p h R φ V =
      p.ellC ^ 2 / (2*h) * ∑ i, (forwardDiff R i) ^ 2 * (1 - Real.cos (forwardDiff φ i)) := by
  rw [arithmetic, geometric, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => weighted_site_defect p hh R φ V i

/-- For the solver's lag clocks the cosine uses (c/ℓ_C) times the actual
forward clock difference on every link. -/
theorem weighted_clock_defect {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R τ V : Fin n → ℝ) :
    arithmetic p h R (fun i => (p.c / p.ellC) * τ i) V -
      geometric p h R (fun i => (p.c / p.ellC) * τ i) V =
      p.ellC ^ 2 / (2*h) * ∑ i, (forwardDiff R i) ^ 2 *
        (1 - Real.cos ((p.c / p.ellC) * forwardDiff τ i)) := by
  simpa only [forwardDiff, mul_sub] using weighted_defect p hh R (fun i => (p.c / p.ellC) * τ i) V

/-- Every site contributes a nonnegative defect, so the arithmetic Hamiltonian
dominates the geometric Hamiltonian for all signed amplitudes and site potentials. -/
theorem geometric_le_arithmetic {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ V : Fin n → ℝ) :
    geometric p h R φ V ≤ arithmetic p h R φ V := by
  apply sub_nonneg.mp
  rw [weighted_defect p hh]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (Real.cos_le_one _)))

end FoliationQM.WeightedLatticeHamiltonian
