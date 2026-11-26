module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Basic.Complex.Basic

/-!
# Finite subsystem partial trace and local-unitary covariance

For v13 `thm:entanglement_nosignaling` (subsystem-unitary argument), trace out
the second finite complex subsystem by summing its diagonal index. Conjugation
by a supplied product operator acts on the reduced matrix by the first
operator alone when the second is unitary. The proof applies to arbitrary
joint matrices, including density matrices of entangled states.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FinitePartialTrace

open Matrix
open scoped BigOperators Matrix Kronecker

variable {α β : Type*} [Fintype β]

/-- The matrix on subsystem A obtained by summing over the diagonal index of B. -/
def partialTrace (ρ : Matrix (α × β) (α × β) ℂ) : Matrix α α ℂ :=
  fun i j => ∑ b, ρ (i,b) (j,b)

/-- Each entry retains both first-subsystem indices and sums one shared second index. -/
theorem partialTrace_apply (ρ : Matrix (α × β) (α × β) ℂ) (i j : α) :
    partialTrace ρ i j = ∑ b, ρ (i,b) (j,b) := rfl

variable [Fintype α]

/-- Taking the ordinary trace after partial trace gives the joint trace. -/
theorem trace_partialTrace (ρ : Matrix (α × β) (α × β) ℂ) :
    (partialTrace ρ).trace = ρ.trace := by
  simp [Matrix.trace, Matrix.diag, partialTrace, Fintype.sum_prod_type]

/-- Left multiplication on the retained subsystem passes through the partial trace. -/
theorem local_left [DecidableEq β] (U : Matrix α α ℂ) (ρ : Matrix (α × β) (α × β) ℂ) :
    partialTrace ((U ⊗ₖ (1 : Matrix β β ℂ)) * ρ) = U * partialTrace ρ := by
  ext i j
  simp only [partialTrace_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.mul_sum]
  exact Finset.sum_comm

/-- Right multiplication on the retained subsystem passes through the partial trace. -/
theorem local_right [DecidableEq β] (ρ : Matrix (α × β) (α × β) ℂ) (U : Matrix α α ℂ) :
    partialTrace (ρ * (U ⊗ₖ (1 : Matrix β β ℂ))) = partialTrace ρ * U := by
  ext i j
  simp only [partialTrace_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.sum_mul]
  exact Finset.sum_comm

private def block (ρ : Matrix (α × β) (α × β) ℂ) (i j : α) : Matrix β β ℂ :=
  fun b c => ρ (i,b) (j,c)

private theorem block_left [DecidableEq α] (V : Matrix β β ℂ) (ρ : Matrix (α × β) (α × β) ℂ) (i j : α) :
    block (((1 : Matrix α α ℂ) ⊗ₖ V) * ρ) i j = V * block ρ i j := by
  ext b c
  simp [block, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, ite_mul, Finset.sum_ite_irrel]

private theorem block_right [DecidableEq α] (ρ : Matrix (α × β) (α × β) ℂ) (V : Matrix β β ℂ) (i j : α) :
    block (ρ * ((1 : Matrix α α ℂ) ⊗ₖ V)) i j = block ρ i j * V := by
  ext b c
  simp [block, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, ite_mul, mul_ite, Finset.sum_ite_irrel]

variable [DecidableEq α] [DecidableEq β]

/-- Conjugation on B cancels in the partial trace, by cyclicity of the
ordinary finite trace of each B-block and the identity V†V = 1. -/
theorem partialTrace_remote (V : Matrix β β ℂ) (ρ : Matrix (α × β) (α × β) ℂ)
    (hV : Vᴴ * V = 1) :
    partialTrace (((1 : Matrix α α ℂ) ⊗ₖ V) * ρ * ((1 : Matrix α α ℂ) ⊗ₖ V)ᴴ) =
      partialTrace ρ := by
  ext i j
  change (block _ i j).trace = (block ρ i j).trace
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, block_right, block_left,
    Matrix.trace_mul_cycle, hV, Matrix.one_mul]

/-- For a factored operation the surviving conjugation is the one on A.
The identity on B uses only V†V = 1. -/
theorem partialTrace_local (U : Matrix α α ℂ) (V : Matrix β β ℂ) (ρ : Matrix (α × β) (α × β) ℂ)
    (hV : Vᴴ * V = 1) :
    partialTrace ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) = U * partialTrace ρ * Uᴴ := by
  have he : U ⊗ₖ V = (U ⊗ₖ (1 : Matrix β β ℂ)) * ((1 : Matrix α α ℂ) ⊗ₖ V) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [he, Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker U,
    Matrix.conjTranspose_one, ← Matrix.mul_assoc, local_right]
  simp only [Matrix.mul_assoc]
  rw [local_left, ← Matrix.mul_assoc, partialTrace_remote V ρ hV, Matrix.mul_assoc]

/-- The two-unitary covariance law for the finite-dimensional partial trace. -/
theorem partialTrace_unitary (U : Matrix.unitaryGroup α ℂ) (V : Matrix.unitaryGroup β ℂ)
    (ρ : Matrix (α × β) (α × β) ℂ) :
    partialTrace ((U.val ⊗ₖ V.val) * ρ * (U.val ⊗ₖ V.val)ᴴ) =
      U.val * partialTrace ρ * U.valᴴ :=
  partialTrace_local U.val V.val ρ (Unitary.star_mul_self_of_mem V.property)

end FoliationQM.FinitePartialTrace
