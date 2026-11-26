module

public import FoliationQM.LatticePolarVariation

/-!
# One-site partial derivatives of the geometric lattice Hamiltonian

Varying one signed amplitude or one dimensionless phase in v13 lines 209–215
extracts its coefficient from the full path derivative. The potentials and all
other coordinates stay fixed along these affine paths.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeSiteVariation

open WeightedLatticeHamiltonian LatticePolarVariation

/-- Shift the coordinate at site `j` by the real parameter `s`. -/
def siteShift {n : ℕ} (u : Fin n → ℝ) (j : Fin n) (s : ℝ) (i : Fin n) : ℝ :=
  u i + s * (if i = j then 1 else 0)

/-- The one-site affine path starts at the unshifted profile. -/
theorem siteShift_zero {n : ℕ} (u : Fin n → ℝ) (j : Fin n) : siteShift u j 0 = u := by
  funext i
  simp [siteShift]

/-- The coordinate velocity of a one-site shift is the corresponding Kronecker delta. -/
theorem siteShift_path {n : ℕ} (u : Fin n → ℝ) (j i : Fin n) (t : ℝ) :
    HasDerivAt (fun s => siteShift u j s i) (if i = j then 1 else 0) t := by
  simpa only [siteShift, id_eq, one_mul] using
    ((hasDerivAt_id t).mul_const (if i = j then (1 : ℝ) else 0)).const_add (u i)

/-- The radial gradient is the partial derivative along the actual signed-amplitude
coordinate at a site, including sites at which the underlying amplitude vanishes. -/
theorem radial_partial {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ V : Fin n → ℝ) (j : Fin n) :
    HasDerivAt (fun s => geometric p h (siteShift R j s) φ V) (radialGradient p h R φ V j) 0 := by
  simpa only [siteShift_zero, mul_zero, add_zero, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using geometric_path p hh (siteShift R j) (fun _ => φ) V
      (fun i => if i = j then 1 else 0) (fun _ => 0) 0
      (fun i => siteShift_path R j i 0) (fun i => hasDerivAt_const 0 (φ i))

/-- The angular gradient is the partial derivative along the actual dimensionless
phase coordinate at a site, with the signed amplitudes and potentials fixed. -/
theorem phase_partial {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ V : Fin n → ℝ) (j : Fin n) :
    HasDerivAt (fun s => geometric p h R (siteShift φ j s) V) (phaseGradient p h R φ j) 0 := by
  simpa only [siteShift_zero, mul_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using geometric_path p hh (fun _ => R) (siteShift φ j) V
      (fun _ => 0) (fun i => if i = j then 1 else 0) 0
      (fun i => hasDerivAt_const 0 (R i)) (fun i => siteShift_path φ j i 0)

end FoliationQM.LatticeSiteVariation
