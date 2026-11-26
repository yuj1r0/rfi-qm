module

public import FoliationQM.FinitePartialTrace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Pure bipartite states and their finite Born marginals

In the proof of v13 `thm:entanglement_nosignaling` the Born marginal is
the inner product of a wave-function fiber with itself. For finite basis
sets, tracing the joint outer product over the second index gives the full
matrix of such inner products. The sum of the marginal weights is the total
squared norm of the bipartite amplitude.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FiniteMarginalBorn

open Matrix FinitePartialTrace
open scoped BigOperators Matrix ComplexOrder

variable {α β : Type*}

/-- The joint outer product of a bipartite amplitude with its conjugate. -/
def pureDensity (A : Matrix α β ℂ) : Matrix (α × β) (α × β) ℂ :=
  let ψ := fun p : α × β => A p.1 p.2
  Matrix.vecMulVec ψ (star ψ)

/-- The two joint indices are ordered as ket coordinates followed by bra coordinates. -/
theorem pureDensity_apply (A : Matrix α β ℂ) (p q : α × β) :
    pureDensity A p q = A p.1 p.2 * star (A q.1 q.2) := rfl

/-- A pure state's joint operator is positive semidefinite. -/
theorem pureDensity_posSemidef [Finite α] [Finite β] (A : Matrix α β ℂ) :
    (pureDensity A).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _

variable [Fintype β]

/-- Tracing out the second index gives the Gram matrix of the amplitude rows. -/
theorem partialTrace_pureDensity (A : Matrix α β ℂ) :
    partialTrace (pureDensity A) = A * Aᴴ := rfl

/-- Each reduced entry is the partial inner product conjugate-linear in the
second matrix-row index, in accordance with the bra-ket convention. -/
theorem partialTrace_pureDensity_inner (A : Matrix α β ℂ) (i j : α) :
    partialTrace (pureDensity A) i j =
      inner ℂ (WithLp.toLp 2 (A j)) (WithLp.toLp 2 (A i)) := rfl

/-- The reduced Gram operator is positive semidefinite for every bipartite amplitude. -/
theorem partialTrace_pureDensity_posSemidef [Finite α] (A : Matrix α β ℂ) :
    (partialTrace (pureDensity A)).PosSemidef := by
  rw [partialTrace_pureDensity]
  exact Matrix.posSemidef_self_mul_conjTranspose A

/-- The diagonal marginal at the retained site is the sum of the partner's Born weights. -/
theorem partialTrace_pureDensity_diag (A : Matrix α β ℂ) (i : α) :
    partialTrace (pureDensity A) i i = (↑(∑ b, ‖A i b‖ ^ 2) : ℂ) := by
  simp only [partialTrace, pureDensity_apply, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_sum]

variable [Fintype α]

/-- Summing the Born diagonal over the retained site recovers the total joint mass. -/
theorem trace_partialTrace_pureDensity (A : Matrix α β ℂ) :
    (partialTrace (pureDensity A)).trace = (↑(∑ p : α × β, ‖A p.1 p.2‖ ^ 2) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, partialTrace_pureDensity_diag,
    Fintype.sum_prod_type, Complex.ofReal_sum]

/-- A normalized bipartite amplitude has a trace-one reduced density matrix. -/
theorem trace_one_of_normalized (A : Matrix α β ℂ) (h : (∑ p : α × β, ‖A p.1 p.2‖ ^ 2) = 1) :
    (partialTrace (pureDensity A)).trace = 1 := by simp [trace_partialTrace_pureDensity, h]

/-- A nonzero amplitude has joint density of rank exactly one. -/
theorem pureDensity_rank_one (A : Matrix α β ℂ) (hA : A ≠ 0) : (pureDensity A).rank = 1 := by
  classical
  have hu : (pureDensity A).rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have hl : (pureDensity A).rank ≠ 0 := by
    intro hz
    rw [Matrix.rank_eq_finrank_span_cols, Submodule.finrank_eq_zero] at hz
    apply hA
    ext i b
    have hcol := Submodule.subset_span (R := ℂ) (s := Set.range (pureDensity A).col)
      (Set.mem_range_self (i,b))
    rw [hz] at hcol
    have hzero : (pureDensity A).col (i,b) = 0 := hcol
    have he := congrFun hzero (i,b)
    change A i b * star (A i b) = 0 at he
    simpa using he
  omega

end FoliationQM.FiniteMarginalBorn
