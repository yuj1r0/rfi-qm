module
public import FoliationQM.SpinorMatrixSmooth
public import FoliationQM.MatrixDifferential
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Calculus.FDeriv.Congr
/-!
# Actual determinant-one matrix tangents

Source: the local determinant-one polar representative in v13
`prop:takabayasi` and its actual matrix connection in `lem:maurer_cartan`.
The real Frechet derivative of the actual complex two-by-two determinant
is proved from the four entry projections and the product rule. Its
explicit polynomial equals the trace of the actual adjugate times the
matrix increment, and hence the inverse trace at determinant one.

For a differentiable matrix field whose determinant equals one on a
neighborhood, the actual determinant derivative vanishes. This proves
that both actual inverse-times-derivative and derivative-times-inverse
connections have complex trace zero. No tangent expansion, trace-zero
condition, connection coefficient, or derivative conclusion is supplied
as a premise. Only differentiability at the point and a local actual
determinant equality are required; no abstract Lie-group or Spin
classification is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.SpecialLinearTangent
open SpinorMatrix

/-- An actual complex matrix entry as a real continuous-linear map in the operator-norm matrix space. -/
def entryCLM (i j : Fin 2) : Mat2 →L[ℝ] ℂ :=
  ({ toFun := fun M => M i j
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Mat2 →ₗ[ℝ] ℂ).toContinuousLinearMap

/-- The explicit real continuous-linear derivative candidate of the actual complex two-by-two determinant. -/
def detDerivative (A : Mat2) : Mat2 →L[ℝ] ℂ :=
  (A 0 0 • entryCLM 1 1 + A 1 1 • entryCLM 0 0) -
    (A 0 1 • entryCLM 1 0 + A 1 0 • entryCLM 0 1)

/-- The determinant derivative candidate evaluates to the exact four-entry Leibniz polynomial. -/
theorem detDerivative_apply (A B : Mat2) :
    detDerivative A B = A 0 0 * B 1 1 + A 1 1 * B 0 0 -
      (A 0 1 * B 1 0 + A 1 0 * B 0 1) := rfl

/-- The actual two-by-two determinant has the displayed real Frechet derivative, proved by the genuine product rule. -/
theorem hasFDerivAt_det (A : Mat2) :
    HasFDerivAt (Matrix.det : Mat2 → ℂ) (detDerivative A) A := by
  have h := (((entryCLM 0 0).hasFDerivAt (x := A)).mul
    ((entryCLM 1 1).hasFDerivAt (x := A))).sub
    (((entryCLM 0 1).hasFDerivAt (x := A)).mul ((entryCLM 1 0).hasFDerivAt (x := A)))
  convert! h using 1
  ext M
  exact Matrix.det_fin_two M

/-- The actual real Frechet derivative of the complex determinant equals the constructed continuous-linear map. -/
theorem fderiv_det (A : Mat2) :
    fderiv ℝ (Matrix.det : Mat2 → ℂ) A = detDerivative A :=
  (hasFDerivAt_det A).fderiv

/-- The actual directional determinant derivative is the explicit entrywise Leibniz formula. -/
theorem fderiv_det_apply (A B : Mat2) :
    fderiv ℝ (Matrix.det : Mat2 → ℂ) A B =
      A 0 0 * B 1 1 + A 1 1 * B 0 0 - (A 0 1 * B 1 0 + A 1 0 * B 0 1) := by
  rw [fderiv_det, detDerivative_apply]

/-- The proved determinant derivative equals the actual trace of adjugate times increment, for every matrix. -/
theorem detDerivative_eq_trace_adjugate (A B : Mat2) :
    detDerivative A B = Matrix.trace (A.adjugate * B) := by
  rw [detDerivative_apply, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.adjugate_fin_two]
  change A 0 0 * B 1 1 + A 1 1 * B 0 0 - (A 0 1 * B 1 0 + A 1 0 * B 0 1) =
    (A 1 1 * B 0 0 + (-A 0 1) * B 1 0) + ((-A 1 0) * B 0 1 + A 0 0 * B 1 1)
  ring

/-- At determinant one the proved determinant derivative equals the actual trace of inverse times increment. -/
theorem detDerivative_eq_trace_inverse (A B : Mat2) (hA : A.det = 1) :
    detDerivative A B = Matrix.trace (A⁻¹ * B) := by
  have hi : A⁻¹ = A.adjugate := Matrix.inv_eq_left_inv (by
    rw [Matrix.adjugate_mul, hA, one_smul])
  rw [hi, detDerivative_eq_trace_adjugate]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual body connection of a two-by-two matrix field, using its actual inverse and real Frechet derivative. -/
def body2 (A : E → Mat2) (x v : E) : Mat2 := (A x)⁻¹ * fderiv ℝ A x v

/-- The actual spatial connection of a two-by-two matrix field, with its actual inverse on the right. -/
def spatial2 (A : E → Mat2) (x v : E) : Mat2 := fderiv ℝ A x v * (A x)⁻¹

/-- The actual determinant of a matrix field obeys the real Frechet chain rule with the proved determinant derivative. -/
theorem hasFDerivAt_det_field {A : E → Mat2} {A' : E →L[ℝ] Mat2} {x : E}
    (hA : HasFDerivAt A A' x) :
    HasFDerivAt (fun y => Matrix.det (A y)) ((detDerivative (A x)).comp A') x :=
  (hasFDerivAt_det (A x)).comp x hA

/-- Applying the actual derivative of the field determinant gives the proved determinant derivative applied to its actual matrix derivative. -/
theorem fderiv_det_field_apply {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : E) :
    fderiv ℝ (fun y => Matrix.det (A y)) x v = detDerivative (A x) (fderiv ℝ A x v) := by
  rw [(hasFDerivAt_det_field hA.hasFDerivAt).fderiv]
  rfl

/-- A local actual determinant-one equality forces the genuine determinant derivative to vanish. -/
theorem fderiv_det_field_eq_zero {A : E → Mat2} {x : E}
    (hdet : ∀ᶠ y in 𝓝 x, Matrix.det (A y) = 1) :
    fderiv ℝ (fun y => Matrix.det (A y)) x = 0 := by
  have heq : (fun y => Matrix.det (A y)) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := hdet
  rw [heq.fderiv_eq]
  exact fderiv_const_apply (𝕜 := ℝ) (x := x) (1 : ℂ)

/-- Differentiating a local actual determinant-one field derives trace zero for its actual body connection, without a supplied tangent premise. -/
theorem body2_trace_zero {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x)
    (hdet : ∀ᶠ y in 𝓝 x, Matrix.det (A y) = 1) (v : E) :
    Matrix.trace (body2 A x v) = 0 := by
  have hf := fderiv_det_field_apply hA v
  rw [fderiv_det_field_eq_zero hdet, zero_apply,
    detDerivative_eq_trace_inverse _ _ hdet.self_of_nhds] at hf
  exact hf.symm

/-- The actual spatial connection of a locally determinant-one differentiable field also has trace zero by cyclicity of the actual matrix trace. -/
theorem spatial2_trace_zero {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x)
    (hdet : ∀ᶠ y in 𝓝 x, Matrix.det (A y) = 1) (v : E) :
    Matrix.trace (spatial2 A x v) = 0 := by
  rw [spatial2, Matrix.trace_mul_comm]
  exact body2_trace_zero hA hdet v

end FoliationQM.SpecialLinearTangent
