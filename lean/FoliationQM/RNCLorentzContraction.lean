module

public import FoliationQM.LorentzMatrixGroup
public import FoliationQM.RNCHalfDensityJet
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Lorentz-frame independence of the normal-coordinate Hessian contraction

For v13 Lemma 9.1, the inverse Minkowski metric contracts both indices of
the Hessian in a normal frame. A change of orthonormal frame acts by
congruence on that matrix. The trace with the inverse metric is invariant.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCLorentzContraction

open Matrix LorentzMatrixGroup RealLorentzFrame PolarSecondDifferential

/-- Contraction of a covariant two-tensor with the inverse normal-frame metric. -/
def contract (A : Mat4) : ℝ := (eta * A).trace

/-- The contraction evaluates the time entry with a positive sign and the three spatial entries with negative signs. -/
theorem contract_diagonal (A : Mat4) :
    contract A = A 0 0 - A 1 1 - A 2 2 - A 3 3 := by
  simp [contract, eta, Matrix.trace, Matrix.diagonal_mul, Fin.sum_univ_succ, sign]
  ring

/-- A change of Lorentz frame preserves the normal-coordinate scalar contraction. -/
theorem contract_congruence (A M : Mat4) (hM : M.transpose * eta * M = eta) :
    contract (M.transpose * A * M) = contract A := by
  unfold contract
  calc
    _ = ((eta * M.transpose * A) * M).trace := by simp only [Matrix.mul_assoc]
    _ = (M * (eta * M.transpose) * A).trace := Matrix.trace_mul_cycle _ _ _
    _ = (eta * A).trace := by rw [← Matrix.mul_assoc M, metric_rows_of_metric M hM]

/-- An arbitrary differentiable field's coordinate Hessian is contracted by the same
operator as the project's Cartesian d'Alembertian, with actual iterated derivatives. -/
theorem contract_hessian (f : Covector → ℝ) (x : Covector) :
    contract (fun i j => fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1)) =
      box f (fun i => Pi.single i 1) x :=
  contract_diagonal _

/-- The Ricci bilinear form evaluated on two vectors is the matrix pairing in these coordinates. -/
theorem form_eq_pairing (A : Mat4) (u v : Covector) :
    RNCHalfDensityJet.form A u v = dotProduct u (A.mulVec v) := by
  rw [RNCHalfDensityJet.form_apply]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm, mul_comm]

/-- Pulling back both arguments of the Ricci form gives ordinary matrix congruence. -/
theorem form_pullback (A M : Mat4) (u v : Covector) :
    RNCHalfDensityJet.form A (M.mulVec u) (M.mulVec v) =
      RNCHalfDensityJet.form (M.transpose * A * M) u v := by
  simp only [form_eq_pairing, ← mulVec_mulVec, dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

/-- The half-density polynomial in transformed coordinates is the polynomial for the pulled-back Ricci tensor. -/
theorem weight_pullback (A M : Mat4) :
    (fun y => RNCHalfDensityJet.weight A (M.mulVec y)) =
      RNCHalfDensityJet.weight (M.transpose * A * M) := by
  funext y
  simp only [RNCHalfDensityJet.weight, form_pullback]

/-- In every orthonormal Lorentz frame the d'Alembertian of the transformed model yields the same scalar. -/
theorem box_pullback (A M : Mat4) (hM : M.transpose * eta * M = eta) :
    box (fun y => RNCHalfDensityJet.weight A (M.mulVec y)) (fun i => Pi.single i 1) 0 =
      -contract A / 6 := by
  rw [weight_pullback, RNCHalfDensityJet.box_weight, ← contract_congruence A M hM,
    contract_diagonal]
  rfl

end FoliationQM.RNCLorentzContraction
