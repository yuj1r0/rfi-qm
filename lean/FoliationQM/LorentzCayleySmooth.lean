module
public import FoliationQM.LorentzCayleyAlgebra
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Actual real-matrix regularity of Lorentz Cayley formulas

Source scope: independent Lorentz-frame coordinates underlying v13
`prop:takabayasi`. These are ordinary real Frechet smoothness results on
ambient real matrix space. The actual nonsingular matrix inverse is smooth
only at invertible matrices; the two actual Cayley expressions therefore
retain their explicit nonsingular denominator domains. No Lorentz manifold
atlas or Spin covering is used in any smoothness definition here.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.LorentzCayleySmooth
open LorentzMatrixGroup LorentzCayleyAlgebra

/-- Actual nonsingular real-matrix inversion is smooth to every order at each invertible matrix. -/
theorem contDiffAt_inverse (n : WithTop ℕ∞) {M : Mat4} (hM : IsUnit M) :
    ContDiffAt ℝ n (fun N : Mat4 => N⁻¹) M := by
  rcases hM with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using (contDiffAt_ringInverse ℝ u)

/-- The actual Cayley expression is real-smooth at each matrix with invertible denominator 1-X. -/
theorem contDiffAt_cayley (n : WithTop ℕ∞) {X : Mat4} (hX : IsUnit (1-X)) :
    ContDiffAt ℝ n cayley X := by
  exact (contDiffAt_const.add contDiffAt_id).mul
    ((contDiffAt_inverse n hX).comp X (contDiffAt_const.sub contDiffAt_id))

/-- The actual Cayley expression is smooth on its full explicit nonsingular denominator domain. -/
theorem contDiffOn_cayley (n : WithTop ℕ∞) :
    ContDiffOn ℝ n cayley {X : Mat4 | IsUnit (1-X)} :=
  fun _ hX => (contDiffAt_cayley n hX).contDiffWithinAt

/-- The actual inverse Cayley expression is real-smooth at each matrix with invertible denominator M+1. -/
theorem contDiffAt_inverseCayley (n : WithTop ℕ∞) {M : Mat4} (hM : IsUnit (M+1)) :
    ContDiffAt ℝ n inverseCayley M := by
  exact (contDiffAt_id.sub contDiffAt_const).mul
    ((contDiffAt_inverse n hM).comp M (contDiffAt_id.add contDiffAt_const))

/-- The actual inverse Cayley expression is smooth on its full explicit nonsingular denominator domain. -/
theorem contDiffOn_inverseCayley (n : WithTop ℕ∞) :
    ContDiffOn ℝ n inverseCayley {M : Mat4 | IsUnit (M+1)} :=
  fun _ hM => (contDiffAt_inverseCayley n hM).contDiffWithinAt

/-- The metric-signed transpose is a genuine real continuous-linear map on ambient matrix space. -/
def signedTransposeCLM : Mat4 →L[ℝ] Mat4 :=
  ({ toFun := fun M => eta * M.transpose * eta
     map_add' := by intros; simp [Matrix.transpose_add, mul_add, add_mul]
     map_smul' := by intros; simp [Matrix.transpose_smul] } :
    Mat4 →ₗ[ℝ] Mat4).toContinuousLinearMap

/-- The signed-transpose continuous-linear map evaluates to the actual matrix formula. -/
theorem signedTransposeCLM_apply (M : Mat4) :
    signedTransposeCLM M = eta * M.transpose * eta := rfl

/-- On every independently defined Lorentz element, signed transpose agrees with the actual group inverse matrix. -/
theorem signedTransposeCLM_matrix (L : Lorentz) :
    signedTransposeCLM (matrix L) = matrix L⁻¹ := by
  rw [matrix_inv, inverse_formula_of_metric _ (metric L)]
  rfl

end FoliationQM.LorentzCayleySmooth
