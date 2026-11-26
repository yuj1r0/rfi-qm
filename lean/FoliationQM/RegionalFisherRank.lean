module

public import FoliationQM.ObserverOscillatingBox
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Rank of the bounded-box Fisher example

The smooth positive one-coordinate profiles from the observer comparison
vary on a fixed finite-volume box. Their actual Fisher matrix has a positive
first diagonal entry and two null coordinate directions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RegionalFisherRank

open MeasureTheory FisherNormalization ObserverGaussianFisher ObserverOscillatingFactor ObserverOscillatingBox

/-- The first-coordinate score square accounts for the entire trace. -/
theorem entry_first (k : ℕ) : fisherMatrix (factor k) axes (volume.restrict box) 0 0 = 2*Real.pi := by
  rw [← trace_value k]
  unfold fisherMatrix fisherTrace
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp [matrixIntegrand, traceIntegrand, Fin.sum_univ_three, score_eq, axes, pow_two, mul_assoc]

/-- Every matrix entry with at least one transverse index vanishes, so both
transverse directions are genuine null directions on the bounded region. -/
theorem entry_transverse (k : ℕ) (i j : Fin 3) (h : i ≠ 0 ∨ j ≠ 0) :
    fisherMatrix (factor k) axes (volume.restrict box) i j = 0 := by
  have hz {l : Fin 3} (hl : l ≠ 0) (x : LorentzCoordinates.Spatial) :
      score (factor k) x (axes l) = 0 := by simp [score_eq, axes, Ne.symm hl]
  rcases h with hi | hj
  · simp [fisherMatrix, matrixIntegrand, hz hi]
  · simp [fisherMatrix, matrixIntegrand, hz hj]

/-- On this finite-volume region a strictly positive trace can coexist
with a singular Cartesian Fisher matrix for a smooth positive density. -/
theorem positive_trace_singular_matrix (k : ℕ) :
    0 < fisherTrace (factor k) axes (volume.restrict box) ∧
    ¬ Matrix.PosDef (fisherMatrix (factor k) axes (volume.restrict box)) := by
  constructor
  · rw [trace_value]
    positivity
  · intro h
    have hn := h.diag_pos (i := (1 : Fin 3))
    rw [entry_transverse k 1 1 (Or.inl (by decide))] at hn
    exact lt_irrefl _ hn

end FoliationQM.RegionalFisherRank
