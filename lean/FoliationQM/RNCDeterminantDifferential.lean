module

public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Instances.Matrix

/-!
# The determinant differential for the normal-coordinate volume factor

The half-density in v13 `lem:rnc_half_density` uses the fourth root of the
absolute metric determinant. For a metric of negative determinant, its
variation therefore involves the differential of the matrix determinant.
The row-multilinear formula below gives this differential even at a singular
matrix. At an invertible matrix it recovers Jacobi's trace formula.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator

namespace FoliationQM.RNCDeterminantDifferential

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The determinant as a continuous multilinear form on the rows. -/
def rowDet : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  { Matrix.detRowAlternating.toMultilinearMap with cont := continuous_id.matrix_det }

/-- Row coordinates send the operator-norm matrix space continuously into the product of rows. -/
def rowsCLM : Matrix ι ι ℝ →L[ℝ] (ι → ι → ℝ) where
  toFun A i j := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_pi fun i => continuous_pi fun j =>
    (continuous_id : Continuous (id : Matrix ι ι ℝ → _)).matrix_elem i j

/-- The determinant of a real square matrix is smooth to every order. -/
theorem contDiff_det (k : WithTop ℕ∞) :
    ContDiff ℝ k (Matrix.det : Matrix ι ι ℝ → ℝ) :=
  (rowDet ι).contDiff.comp (rowsCLM ι).contDiff

/-- The trace as a continuous linear functional. -/
def traceCLM : Matrix ι ι ℝ →L[ℝ] ℝ :=
  ⟨Matrix.traceLinearMap ι ℝ ℝ, continuous_id.matrix_trace⟩

variable {ι}

/-- The Fréchet differential of the determinant sums single-row variations. -/
theorem fderiv_det_rows (A H : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det A H = ∑ i, (A.updateRow i (H i)).det := by
  have hd := ((rowDet ι).hasFDerivAt (rowsCLM ι A)).comp A (rowsCLM ι).hasFDerivAt
  calc
    _ = (rowDet ι).linearDeriv (rowsCLM ι A) (rowsCLM ι H) :=
      congrArg (fun L : Matrix ι ι ℝ →L[ℝ] ℝ => L H) hd.fderiv
    _ = _ := (rowDet ι).linearDeriv_apply (rowsCLM ι A) (rowsCLM ι H)

/-- Jacobi's formula for the Fréchet derivative on the invertible locus. -/
theorem fderiv_det_apply (A H : Matrix ι ι ℝ) (hA : IsUnit A.det) :
    fderiv ℝ Matrix.det A H = A.det * (A⁻¹ * H).trace := by
  have hmul : H * A⁻¹ * A = H := A.nonsing_inv_mul_cancel_right H hA
  have hrow (i : ι) : H i = ∑ k, (H * A⁻¹) i k • A k := by
    ext j
    simpa [Matrix.mul_apply, Finset.sum_apply] using
      (congrArg (fun B : Matrix ι ι ℝ => B i j) hmul).symm
  rw [fderiv_det_rows, Matrix.trace_mul_comm A⁻¹ H, Matrix.trace, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hrow i, Matrix.det_updateRow_sum]
  exact mul_comm _ _

/-- At the identity the actual determinant differential applied to a matrix is its trace. -/
theorem fderiv_det_one_apply (H : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det (1 : Matrix ι ι ℝ) H = H.trace := by
  simpa using fderiv_det_apply 1 H (by simp)

/-- The trace represents the Fréchet derivative at the identity matrix. -/
theorem hasFDerivAt_det_one :
    HasFDerivAt Matrix.det (traceCLM ι) (1 : Matrix ι ι ℝ) := by
  have he : fderiv ℝ Matrix.det (1 : Matrix ι ι ℝ) = traceCLM ι := by
    apply ContinuousLinearMap.ext
    exact fderiv_det_one_apply
  rw [← he]
  exact ((contDiff_det ι 1).contDiffAt.differentiableAt_one).hasFDerivAt

end FoliationQM.RNCDeterminantDifferential
