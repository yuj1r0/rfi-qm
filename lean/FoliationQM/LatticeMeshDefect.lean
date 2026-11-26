module

public import FoliationQM.WeightedLatticeHamiltonian
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The arithmetic–geometric Hamiltonian defect under mesh refinement

The unweighted edge factor in v13 line 238 is exact. The Hamiltonians also
contain an inverse mesh spacing. Bounds on both forward increments and on
the total site weight give a quadratic bound on the full energy difference.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeMeshDefect

open WeightedLatticeHamiltonian Filter Asymptotics
open scoped BigOperators Topology

/-- Under linear increment bounds the amplitude square times the phase cost
has a quartic upper bound in the mesh spacing at each site. -/
theorem edge_factor_le {r θ h A B : ℝ} (hh : 0 ≤ h) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr : |r| ≤ A*h) (hθ : |θ| ≤ B*h) :
    r^2 * (1 - Real.cos θ) ≤ (A*h)^2 * ((B*h)^2 / 2) := by
  have hr' : r^2 ≤ (A*h)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg r) (mul_nonneg hA hh)).mpr hr
  have hθ' : θ^2 ≤ (B*h)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg θ) (mul_nonneg hB hh)).mpr hθ
  have hcost : 1 - Real.cos θ ≤ (B*h)^2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
  exact mul_le_mul hr' hcost (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _)

/-- A bounded total site weight and uniform bounds on amplitude and phase
increments give an explicit order-two error constant for the full Hamiltonians. -/
theorem weighted_defect_le {n : ℕ} (p : MassiveParameters) {h A B L : ℝ}
    (hh : 0 < h) (hA : 0 ≤ A) (hB : 0 ≤ B) (hlen : (n : ℝ)*h ≤ L)
    (R φ V : Fin n → ℝ) (hR : ∀ i, |forwardDiff R i| ≤ A*h)
    (hφ : ∀ i, |forwardDiff φ i| ≤ B*h) :
    arithmetic p h R φ V - geometric p h R φ V ≤ (p.ellC^2*L*A^2*B^2/4)*h^2 := by
  rw [weighted_defect p hh]
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => edge_factor_le hh.le hA hB (hR i) (hφ i))
  calc
    _ ≤ p.ellC^2/(2*h) * ((n : ℝ) * ((A*h)^2 * ((B*h)^2/2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using hs
    _ = ((n : ℝ)*h) * (p.ellC^2*A^2*B^2*h^2/4) := by
      field_simp
      ring
    _ ≤ L * (p.ellC^2*A^2*B^2*h^2/4) := mul_le_mul_of_nonneg_right hlen (by positivity)
    _ = _ := by ring

/-- For a mesh family with varying site counts, the actual finite Hamiltonian
difference is big-O of its squared spacing along any filter on which the
total site weight and both increment bounds eventually hold uniformly. -/
theorem family_defect_isBigO {ι : Type*} (l : Filter ι) (p : MassiveParameters)
    (n : ι → ℕ) (h : ι → ℝ) (R φ V : (k : ι) → Fin (n k) → ℝ) {A B L : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hmesh : ∀ᶠ k in l, 0 < h k ∧ (n k : ℝ) * h k ≤ L ∧
      (∀ i, |forwardDiff (R k) i| ≤ A*h k) ∧ (∀ i, |forwardDiff (φ k) i| ≤ B*h k)) :
    (fun k => arithmetic p (h k) (R k) (φ k) (V k) - geometric p (h k) (R k) (φ k) (V k))
      =O[l] (fun k => (h k)^2) := by
  apply IsBigO.of_bound (p.ellC^2*L*A^2*B^2/4)
  filter_upwards [hmesh] with k hk
  obtain ⟨hh, hlen, hR, hφ⟩ := hk
  simpa only [Real.norm_of_nonneg (sub_nonneg.mpr (geometric_le_arithmetic p hh _ _ _)),
    Real.norm_of_nonneg (sq_nonneg _)] using
    weighted_defect_le p hh hA hB hlen (R k) (φ k) (V k) hR hφ

end FoliationQM.LatticeMeshDefect
