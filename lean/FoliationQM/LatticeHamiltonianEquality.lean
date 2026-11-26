module

public import FoliationQM.WeightedLatticeHamiltonian

/-!
# Equality and a nodal edge in the finite lattice energy

V13 Eq. 10 uses the arithmetic mean of the two site intensities.
The nonnegative weighted defects give an edgewise equality criterion.
On a two-site lattice a phase change at a zero-amplitude site leaves
the complex field fixed but can change this arithmetic energy.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeHamiltonianEquality

open WeightedLatticeHamiltonian

/-- Exact equality of the two Hamiltonians holds when every edge either has
equal signed amplitudes or its phase increment is an integer number of turns. -/
theorem eq_iff {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ V : Fin n → ℝ) :
    arithmetic p h R φ V = geometric p h R φ V ↔
      ∀ i, forwardDiff R i = 0 ∨ ∃ k : ℤ, (k : ℝ)*(2*Real.pi) = forwardDiff φ i := by
  have hell : 0 < p.ellC := div_pos p.hbar_pos (mul_pos p.m_pos p.c_pos)
  have hp : 0 < p.ellC^2/(2*h) := by positivity
  have hn (i : Fin n) : 0 ≤ (forwardDiff R i)^2*(1-Real.cos (forwardDiff φ i)) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (Real.cos_le_one _))
  rw [← sub_eq_zero, weighted_defect p hh R φ V, mul_eq_zero, or_iff_right hp.ne',
    Fintype.sum_eq_zero_iff_of_nonneg hn, funext_iff]
  apply forall_congr'
  intro i
  rw [← Real.cos_eq_one_iff]
  change _ * _ = 0 ↔ _
  rw [mul_eq_zero, sub_eq_zero, eq_comm (a := (1 : ℝ)) (b := Real.cos _)]
  simp

/-- For an edge with a zero at its first site and amplitude a at the second,
the arithmetic excess is a² times the exact weighted phase cost. The replicated
second edge contributes zero, including for a nonzero endpoint potential. -/
theorem two_site_nodal_defect (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (a θ : ℝ) (V : Fin 2 → ℝ) :
    let R : Fin 2 → ℝ := fun i => if i = 0 then 0 else a
    let φ : Fin 2 → ℝ := fun i => if i = 0 then θ else 0
    arithmetic p h R φ V - geometric p h R φ V =
      p.ellC^2/(2*h)*a^2*(1-Real.cos θ) := by
  dsimp only
  rw [weighted_defect p hh, Fin.sum_univ_two]
  have h₀ : LatticeConservation.nextNode (0 : Fin 2) = 1 := rfl
  have h₁ : LatticeConservation.nextNode (1 : Fin 2) = 1 := rfl
  simp [forwardDiff, h₀, h₁, mul_assoc]

/-- The phase at the zero site can be changed by π without changing either
complex grid value. At that half-turn the arithmetic excess is ℓ_C² a²/h. -/
theorem half_turn_at_node (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (a : ℝ) (V : Fin 2 → ℝ) :
    let R : Fin 2 → ℝ := fun i => if i = 0 then 0 else a
    let φ : Fin 2 → ℝ := fun i => if i = 0 then Real.pi else 0
    (∀ i, (R i : ℂ)*phase (φ i) = (R i : ℂ)*phase 0) ∧
      geometric p h R φ V = geometric p h R (fun _ => 0) V ∧
      arithmetic p h R φ V - geometric p h R φ V = p.ellC^2*a^2/h := by
  dsimp only
  constructor
  · intro i
    by_cases hi : i = 0 <;> simp [hi]
  · constructor
    · have h₀ : LatticeConservation.nextNode (0 : Fin 2) = 1 := rfl
      have h₁ : LatticeConservation.nextNode (1 : Fin 2) = 1 := rfl
      simp [geometric, Fin.sum_univ_two, weightedSite, forwardDiff, h₀, h₁]
    · rw [two_site_nodal_defect p hh a Real.pi V, Real.cos_pi]
      ring

end FoliationQM.LatticeHamiltonianEquality
