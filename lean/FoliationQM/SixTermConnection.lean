module

public import FoliationQM.DiracMatrices
public import Mathlib.Tactic.Ring
/-!
# The six signed connection-pair contractions

Source: v13 `eq:six_terms_omega`, the algebraic expansion in the proof of
`thm:dirac_lift` (iii). The diagonal signs are the real parts of the actual
Dirac representation's (+---) metric. The sum is literally over ordered
indices a < b, and its input is an arbitrary real contracted family.
No velocity-gradient, spin-gradient, connection-field, or geometric
interpretation of that family is assumed by these finite algebraic results.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SixTermConnection
open DiracMatrices

/-- The real diagonal sign of the actual Minkowski metric in the Dirac representation. -/
def metricDiagonal (a : Fin 4) : ℝ := (eta a a).re

/-- The actual real metric diagonal is +1 at the time index and -1 at each spatial index. -/
theorem metricDiagonal_eq (a : Fin 4) : metricDiagonal a = if a = 0 then 1 else -1 := by
  by_cases h : a = 0 <;> simp [metricDiagonal, eta, h]

/-- The actual sum over the six index pairs a < b weighted by the two Minkowski diagonal signs. -/
def signedPairSum (C : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, if a < b then metricDiagonal a * metricDiagonal b * C a b else 0

/-- The actual metric-weighted six-pair sum is minus its three temporal pairs plus its three spatial pairs. -/
theorem signedPairSum_eq_six_terms (C : Fin 4 → Fin 4 → ℝ) :
    signedPairSum C = -C 0 1 - C 0 2 - C 0 3 + C 1 2 + C 1 3 + C 2 3 := by
  norm_num [signedPairSum, metricDiagonal_eq, Fin.sum_univ_succ]
  ring

/-- The actual six-pair sum of two arbitrary real families contracted pointwise. -/
def pairedProductSum (U V : Fin 4 → Fin 4 → ℝ) : ℝ :=
  signedPairSum (fun a b => U a b * V a b)

/-- For a pointwise product family, the actual six-pair contraction has exactly the source temporal and spatial signs. -/
theorem pairedProductSum_eq_six_terms (U V : Fin 4 → Fin 4 → ℝ) :
    pairedProductSum U V =
      -(U 0 1 * V 0 1) - U 0 2 * V 0 2 - U 0 3 * V 0 3 +
        U 1 2 * V 1 2 + U 1 3 * V 1 3 + U 2 3 * V 2 3 := by
  exact signedPairSum_eq_six_terms (fun a b => U a b * V a b)

/-- The source grouping separates the three negative temporal pairs and the three positive spatial pairs. -/
theorem signedPairSum_eq_temporal_spatial (C : Fin 4 → Fin 4 → ℝ) :
    signedPairSum C = -(C 0 1 + C 0 2 + C 0 3) + (C 1 2 + C 1 3 + C 2 3) := by
  rw [signedPairSum_eq_six_terms]
  ring

end FoliationQM.SixTermConnection
