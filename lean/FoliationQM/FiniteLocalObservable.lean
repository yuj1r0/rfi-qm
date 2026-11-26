module

public import FoliationQM.FinitePartialTrace
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Finite density operators and local observables

The explicit partial trace preserves positivity. Testing the reduced
density by an arbitrary retained observable gives its expectation in the
joint state with the identity observable on the discarded subsystem.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FiniteLocalObservable

open Matrix FinitePartialTrace
open scoped Kronecker BigOperators ComplexOrder

variable {α β : Type*} [Fintype β]

/-- Tracing out the remote index sums the principal blocks restricted to a fixed remote basis state. -/
theorem partialTrace_eq_sum_blocks (ρ : Matrix (α × β) (α × β) ℂ) :
    partialTrace ρ = ∑ b : β, ρ.submatrix (fun i => (i,b)) (fun j => (j,b)) := by
  ext i j
  simp [partialTrace, Matrix.sum_apply]

/-- The partial trace of a positive semidefinite complex matrix is positive semidefinite. -/
theorem partialTrace_posSemidef {ρ : Matrix (α × β) (α × β) ℂ} (hρ : ρ.PosSemidef) :
    (partialTrace ρ).PosSemidef := by
  rw [partialTrace_eq_sum_blocks]
  exact Matrix.posSemidef_sum _ fun b _ => hρ.submatrix (fun i => (i,b))

variable [Fintype α]

/-- A finite bipartite density operator gives a positive reduced matrix of trace one. -/
theorem reduced_density {ρ : Matrix (α × β) (α × β) ℂ} (hp : ρ.PosSemidef)
    (ht : ρ.trace = 1) : (partialTrace ρ).PosSemidef ∧ (partialTrace ρ).trace = 1 :=
  ⟨partialTrace_posSemidef hp, (FinitePartialTrace.trace_partialTrace ρ).trans ht⟩

/-- A local matrix observable has the same expectation in the joint and reduced matrices. -/
theorem local_expectation [DecidableEq β] (A : Matrix α α ℂ) (ρ : Matrix (α × β) (α × β) ℂ) :
    ((A ⊗ₖ (1 : Matrix β β ℂ)) * ρ).trace = (A * partialTrace ρ).trace := by
  rw [← FinitePartialTrace.trace_partialTrace ((A ⊗ₖ (1 : Matrix β β ℂ)) * ρ),
    FinitePartialTrace.local_left]

end FoliationQM.FiniteLocalObservable
