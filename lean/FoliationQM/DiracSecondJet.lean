module

public import FoliationQM.RealLorentzFrame

/-!
# The Clifford contraction of symmetric spinor second jets

Source: the actual flat Dirac operator product preceding v13
`eq:spinor_quadratic_exact`. The concrete gamma anticommutator reduces a
symmetric spinor-valued second jet to its (+---) diagonal contraction.
Symmetry is explicit in this finite algebraic support; the field bridge
must establish it from genuine twice differentiable field derivatives.
No field equation or differential identity is assumed by these lemmas.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracSecondJet
open DiracMatrices RealLorentzFrame

/-- The actual symmetrized gamma product acting on a spinor is twice its Minkowski metric coefficient. -/
theorem gamma_pair_apply (a b : Fin 4) (z : Spinor) :
    (gamma a * gamma b).mulVec z + (gamma b * gamma a).mulVec z =
      (2 * eta a b) • z := by
  rw [← Matrix.add_mulVec, clifford, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The actual two-index Dirac metric contraction is twice the signed diagonal second-jet contraction. -/
theorem metric_contraction (H : Fin 4 → Fin 4 → Spinor) :
    (∑ a, ∑ b, (2 * eta a b) • H a b) =
      (2 : ℂ) • ∑ a, (sign a : ℂ) • H a a := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a=0 <;> simp [eta, sign, ha]

/-- A symmetric actual spinor second jet contracts with two gamma matrices to the signed diagonal Minkowski contraction. -/
theorem symmetric_contraction (H : Fin 4 → Fin 4 → Spinor)
    (hsym : ∀ a b, H a b=H b a) :
    (∑ a, ∑ b, (gamma a*gamma b).mulVec (H a b)) =
      ∑ a, (sign a : ℂ) • H a a := by
  have hswap : (∑ a, ∑ b, (gamma b*gamma a).mulVec (H a b)) =
      (∑ a, ∑ b, (gamma a*gamma b).mulVec (H a b)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hsym b a]
  have hpair : (∑ a, ∑ b, (gamma a*gamma b).mulVec (H a b)) +
      (∑ a, ∑ b, (gamma a*gamma b).mulVec (H a b)) =
      ∑ a, ∑ b, (2 * eta a b) • H a b := by
    nth_rw 2 [← hswap]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    exact gamma_pair_apply a b (H a b)
  have hh := hpair.trans (metric_contraction H)
  funext j
  have hj := congrArg (fun z : Spinor => z j) hh
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
  linear_combination (1/2 : ℂ)*hj

/-- Iterated actual gamma actions on a symmetric spinor second jet give the same signed diagonal contraction. -/
theorem symmetric_iterated_contraction (H : Fin 4 → Fin 4 → Spinor)
    (hsym : ∀ a b, H a b=H b a) :
    (∑ a, ∑ b, (gamma a).mulVec ((gamma b).mulVec (H a b))) =
      ∑ a, (sign a : ℂ) • H a a := by
  simp_rw [Matrix.mulVec_mulVec]
  exact symmetric_contraction H hsym

end FoliationQM.DiracSecondJet
