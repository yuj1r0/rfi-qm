module

public import FoliationQM.WeightedLatticeHamiltonian
public import FoliationQM.ClockScales
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A fixed-length lattice with a nodal phase jump

For v13 Eq. 10 take one zero-amplitude site and a single phase jump of π.
All forward amplitude differences have size at most the mesh width. The
arithmetic and geometric Hamiltonians then differ to first order in the
mesh width. The potential is arbitrary on each grid.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeNodalMeshRate

open LatticeConservation WeightedLatticeHamiltonian Filter Asymptotics
open scoped Topology

/-- Spacing on a grid of N+2 sites of total rectangular weight one. -/
def spacing (N : ℕ) : ℝ := 1 / ((N : ℝ) + 2)

/-- The amplitude rises from zero at the first site to one mesh width. -/
def amplitude (N : ℕ) (i : Fin (N+2)) : ℝ := if i = 0 then 0 else spacing N

/-- A half-period phase at the node gives one physical link with phase cost two. -/
def angle (N : ℕ) (i : Fin (N+2)) : ℝ := if i = 0 then Real.pi else 0

/-- The actual v13 weighted energy difference on the nodal grid. -/
def defect (p : MassiveParameters) (N : ℕ) (V : Fin (N+2) → ℝ) : ℝ :=
  arithmetic p (spacing N) (amplitude N) (angle N) V -
    geometric p (spacing N) (amplitude N) (angle N) V

private theorem spacing_pos (N : ℕ) : 0 < spacing N := by unfold spacing; positivity

private theorem next_ne_zero (N : ℕ) (i : Fin (N+2)) : nextNode i ≠ 0 := by
  unfold nextNode
  split
  · intro h
    have hz := congrArg Fin.val h
    simp at hz
  · rename_i h
    rintro rfl
    simp at h

/-- The total rectangular weight is exactly one for every mesh. -/
theorem grid_weight (N : ℕ) : ((N+2 : ℕ) : ℝ) * spacing N = 1 := by
  push_cast
  unfold spacing
  field_simp

/-- Every forward amplitude increment has magnitude at most one mesh width. -/
theorem amplitude_increment_le (N : ℕ) (i : Fin (N+2)) :
    |forwardDiff (amplitude N) i| ≤ spacing N := by
  by_cases hi : i = 0
  · simp [forwardDiff, amplitude, next_ne_zero, hi, abs_of_pos (spacing_pos N)]
  · simp [forwardDiff, amplitude, next_ne_zero, hi, (spacing_pos N).le]

/-- One link contributes the entire weighted defect ℓ_C² h, including for
nonzero site potentials and when the terminal replicated link is present. -/
theorem defect_eq (p : MassiveParameters) (N : ℕ) (V : Fin (N+2) → ℝ) :
    defect p N V = p.ellC^2 * spacing N := by
  rw [defect, weighted_defect p (spacing_pos N)]
  rw [Finset.sum_eq_single (0 : Fin (N+2))]
  · simp only [forwardDiff, amplitude, angle, next_ne_zero, ite_false, ite_true,
      sub_zero, zero_sub, Real.cos_neg, Real.cos_pi]
    field_simp [(spacing_pos N).ne']
    ring
  · intro i _ hi
    simp [forwardDiff, amplitude, hi, next_ne_zero]
  · simp

private theorem sites_tendsto : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
  tendsto_atTop_mono (fun _ => by linarith) tendsto_natCast_atTop_atTop

/-- The fixed-total-weight grids have spacing tending to zero. -/
theorem spacing_tendsto : Tendsto spacing atTop (𝓝 0) := by
  unfold spacing
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp sites_tendsto

/-- Dividing the nodal energy defect by the squared spacing gives a sequence
tending to positive infinity for every family of site potentials. -/
theorem defect_ratio_tendsto (p : MassiveParameters) (V : (N : ℕ) → Fin (N+2) → ℝ) :
    Tendsto (fun N => defect p N (V N) / (spacing N)^2) atTop atTop := by
  have he (N : ℕ) : defect p N (V N) / (spacing N)^2 = p.ellC^2 * ((N : ℝ) + 2) := by
    rw [defect_eq]
    unfold spacing
    field_simp
  simp_rw [he]
  exact sites_tendsto.const_mul_atTop (sq_pos_of_pos (ClockScales.ellC_pos p))

/-- An amplitude increment bound alone allows this fixed-length family to
violate every quadratic-in-spacing upper bound on the weighted energy defect. -/
theorem not_quadratic (p : MassiveParameters) (V : (N : ℕ) → Fin (N+2) → ℝ) :
    ¬ (fun N => defect p N (V N)) =O[atTop] (fun N => (spacing N)^2) := by
  intro hb
  obtain ⟨C,hC⟩ := isBigO_iff.mp hb
  obtain ⟨N,hn,hgt⟩ := (hC.and ((defect_ratio_tendsto p V).eventually_gt_atTop C)).exists
  have hd : 0 ≤ defect p N (V N) := by rw [defect_eq]; positivity [spacing_pos N]
  simp only [Real.norm_eq_abs, abs_of_nonneg hd, abs_of_nonneg (sq_nonneg (spacing N))] at hn
  exact (not_lt_of_ge hn) ((lt_div_iff₀ (sq_pos_of_pos (spacing_pos N))).mp hgt)

end FoliationQM.LatticeNodalMeshRate
