module

public import FoliationQM.CurvedCoordinateDynamics
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Fixed Euclidean auxiliary norms and the actual matrix-raising operator

Coordinate derivatives retain the usual function-space norm. The explicit
Euclidean auxiliary norm below compares the full four-component covector
with the three spatial force components. Matrix bounds use the actual
continuous linear raising map on the coordinate function spaces.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAuxiliaryNorm

open LorentzMatrixGroup
open scoped Matrix.Norms.Operator

/-- The fixed Euclidean norm of all entries of a finite real coordinate vector. -/
def norm2 {n : ℕ} (v : Fin n → ℝ) : ℝ := ‖WithLp.toLp 2 v‖

/-- The Euclidean auxiliary norm is nonnegative. -/
theorem norm2_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ norm2 v := norm_nonneg _

/-- A real scalar rescales the Euclidean auxiliary norm by its absolute value. -/
theorem norm2_smul {n : ℕ} (a : ℝ) (v : Fin n → ℝ) :
    norm2 (a • v) = |a| * norm2 v := by
  simp only [norm2, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-- The fixed Euclidean auxiliary norm is continuous in the original coordinate topology. -/
theorem continuous_norm2 {n : ℕ} : Continuous (@norm2 n) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).norm

/-- The square of the auxiliary norm sums every coordinate square. -/
theorem norm2_sq {n : ℕ} (v : Fin n → ℝ) : norm2 v ^ 2 = ∑ i, v i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

/-- The coordinate supremum norm is bounded by the full Euclidean auxiliary norm. -/
theorem norm_le_norm2 {n : ℕ} (v : Fin n → ℝ) : ‖v‖ ≤ norm2 v :=
  (pi_norm_le_iff_of_nonneg (norm2_nonneg v)).mpr fun i =>
    PiLp.norm_apply_le (WithLp.toLp 2 v) i

/-- Three spatial components have Euclidean norm at most three times their coordinate supremum norm. -/
theorem spatial_norm2_le (z : Fin 3 → ℝ) : norm2 z ≤ 3 * ‖z‖ := by
  have hs : norm2 z ^ 2 ≤ 3 * ‖z‖ ^ 2 := by
    rw [norm2_sq]
    calc
      (∑ i : Fin 3, z i ^ 2) ≤ ∑ _i : Fin 3, ‖z‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := (sq_le_sq₀ (norm_nonneg (z i)) (norm_nonneg z)).mpr
          (norm_le_pi_norm z i)
        simpa only [Real.norm_eq_abs, sq_abs] using hi
      _ = 3 * ‖z‖ ^ 2 := by simp
  nlinarith [norm2_nonneg z, norm_nonneg z]

/-- The actual matrix-raising map as a continuous linear map between coordinate function spaces. -/
def raiseMap (A : Mat4) : Covector →L[ℝ] Covector :=
  (Matrix.toLin' A).toContinuousLinearMap

/-- The continuous linear raising map evaluates to the original full matrix-vector contraction. -/
theorem raiseMap_apply (A : Mat4) (ξ : Covector) : raiseMap A ξ = A.mulVec ξ := rfl

/-- The assignment of a matrix to its raising operator is itself continuous and linear. -/
def matrixRaiseMap : Mat4 →L[ℝ] (Covector →L[ℝ] Covector) :=
  ({ toFun := raiseMap
     map_add' := by
       intro A B
       ext ξ r
       change ((A + B).mulVec ξ) r = (A.mulVec ξ + B.mulVec ξ) r
       rw [Matrix.add_mulVec]
     map_smul' := by
       intro a A
       ext ξ r
       change ((a • A).mulVec ξ) r = (a • A.mulVec ξ) r
       rw [Matrix.smul_mulVec] } : Mat4 →ₗ[ℝ] (Covector →L[ℝ] Covector)).toContinuousLinearMap

/-- The continuous matrix-to-operator map agrees with the raising map used in the force estimates. -/
theorem matrixRaiseMap_apply (A : Mat4) : matrixRaiseMap A = raiseMap A := rfl

/-- An actual raising-operator bound controls matrix contraction by the full Euclidean covector norm. -/
theorem norm_mulVec_le {A : Mat4} {Bg : ℝ} (hA : ‖raiseMap A‖ ≤ Bg) (ξ : Covector) :
    ‖A.mulVec ξ‖ ≤ Bg * norm2 ξ :=
  (raiseMap A).le_of_opNorm_le_of_le hA (norm_le_norm2 ξ)

end FoliationQM.CurvedAuxiliaryNorm
