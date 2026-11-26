module

public import FoliationQM.LatticeConservation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Summation by parts on the replicated Neumann grid

The geometric energy in v13 lines 209–215 and the same-lattice comparison
at line 229 use a finite path. With replicated endpoint values, the
forward differences vanish on the terminal self-link. The conjugate
pairing of two differences yields the three-point Neumann Laplacian.
-/

@[expose] public section
namespace FoliationQM.LatticeNeumannGreen

open LatticeConservation
open scoped BigOperators

/-- Complex forward increment on the replicated path. -/
noncomputable def forward {n : ℕ} (z : Fin n → ℂ) (i : Fin n) : ℂ :=
  z (nextNode i) - z i

/-- Three-point replicated Neumann Laplacian before dividing by the squared mesh spacing. -/
noncomputable def laplacian {n : ℕ} (z : Fin n → ℂ) (i : Fin n) : ℂ :=
  z (nextNode i) - 2 * z i + z (prevNode i)

/-- Summing a directed edge observable with zero diagonal from its initial
or its final vertex gives the same finite path sum. -/
theorem sum_forward_eq_backward {M : Type*} [AddCommMonoid M] {n : ℕ}
    (F : Fin n → Fin n → M) (diag : ∀ i, F i i = 0) :
    (∑ i, F i (nextNode i)) = ∑ i, F (prevNode i) i := by
  cases n with
  | zero => simp
  | succ k =>
    have next_cast (i : Fin k) : nextNode i.castSucc = i.succ := by
      have h : i.val + 1 < k + 1 := Nat.succ_lt_succ i.isLt
      apply Fin.ext
      simp [nextNode, h]
    have prev_succ (i : Fin k) : prevNode i.succ = i.castSucc := by
      apply Fin.ext
      simp [prevNode]
    rw [Fin.sum_univ_castSucc (fun i => F i (nextNode i)),
      Fin.sum_univ_succ (fun i => F (prevNode i) i)]
    have hn : nextNode (Fin.last k) = Fin.last k := by simp [nextNode]
    have hp : prevNode (0 : Fin (k + 1)) = 0 := by apply Fin.ext; simp [prevNode]
    simp [next_cast, prev_succ, hn, hp, diag]

/-- Varying a forward increment shifts the variation onto the difference of
incoming and outgoing edge coefficients at each site, including endpoints. -/
theorem summation_by_parts {K : Type*} [Ring K] {n : ℕ}
    (F : Fin n → Fin n → K) (diag : ∀ i, F i i = 0) (z : Fin n → K) :
    (∑ i, F i (nextNode i) * (z (nextNode i) - z i)) =
      ∑ i, (F (prevNode i) i - F i (nextNode i)) * z i := by
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [sum_forward_eq_backward (fun i j => F i j * z j) (fun i => by simp [diag])]

/-- The complex Green identity identifies the negative Neumann Laplacian
with the sesquilinear energy of the actual forward increments. -/
theorem green {n : ℕ} (u v : Fin n → ℂ) :
    (∑ i, star (u i) * (-laplacian v i)) = ∑ i, star (forward u i) * forward v i := by
  calc
    _ = ∑ i, ((v i - v (prevNode i)) - (v (nextNode i) - v i)) * star (u i) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold laplacian
      ring
    _ = ∑ i, (v (nextNode i) - v i) * (star (u (nextNode i)) - star (u i)) :=
      (summation_by_parts (fun i j => v j - v i) (fun i => sub_self _) (fun i => star (u i))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [forward, forward, star_sub, mul_comm]

end FoliationQM.LatticeNeumannGreen
