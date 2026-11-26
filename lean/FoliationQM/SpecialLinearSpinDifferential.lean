module
public import FoliationQM.SpinorMatrixSmooth
public import FoliationQM.MaurerCartanDifferential
/-!
# Actual differentiation of the concrete determinant-one spin representation

Sources: v13 `eq:maurer_cartan_def`, `lem:maurer_cartan`, and the actual
matrix representation in `prop:takabayasi`. The explicit real-linear
representation differentiates by its proved continuous-linear map. Its
multiplication law carries the actual two-by-two inverse to the actual
four-by-four inverse when the input determinant is one.

Combining these identities identifies the actual body and spatial
connections with the representation of the actual two-by-two derivative
products. Differentiability of the input field and determinant one at the
point are explicit premises. Local determinant-one constraints, traceless
tangent reconstruction, and real Lorentz generator coefficients are
separate results; no derivative or connection conclusion is assumed here.
All matrix calculus uses the existing operator norm.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.SpecialLinearSpinDifferential
open DiracMatrices SpinorMatrix SpecialLinearSpin SpinorMatrixSmooth MaurerCartanDifferential

/-- For a determinant-one input, the actual inverse Dirac representative is the representative of its actual two-by-two inverse. -/
theorem spin_inv (A : Mat2) (hA : A.det = 1) : (spin A)⁻¹ = spin (A⁻¹) := by
  have hi : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (by rw [hA]; exact isUnit_one)
  apply Matrix.inv_eq_left_inv
  rw [← spin_mul, hi, spin_one]

/-- The actual explicit spin representation has its real continuous-linear map as the genuine Frechet derivative. -/
theorem hasFDerivAt_spin (A : Mat2) : HasFDerivAt spin spinCLM A := spinCLM.hasFDerivAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual spin representation obeys the real Frechet chain rule on an arbitrary real normed domain. -/
theorem hasFDerivAt_spin_field {A : E → Mat2} {dA : E →L[ℝ] Mat2} {x : E}
    (hA : HasFDerivAt A dA x) :
    HasFDerivAt (fun y => spin (A y)) (spinCLM.comp dA) x :=
  (hasFDerivAt_spin (A x)).comp x hA

/-- An actually differentiable two-by-two matrix field gives an actually differentiable Dirac representative field. -/
theorem differentiableAt_spin_field {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) : DifferentiableAt ℝ (fun y => spin (A y)) x :=
  (hasFDerivAt_spin_field hA.hasFDerivAt).differentiableAt

/-- The actual directional derivative of the represented field is the representative of the actual directional matrix derivative. -/
theorem fderiv_spin_field_apply {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : E) :
    fderiv ℝ (fun y => spin (A y)) x v = spin (fderiv ℝ A x v) := by
  rw [(hasFDerivAt_spin_field hA.hasFDerivAt).fderiv]
  rfl

/-- The actual body connection of the represented field equals the representation of its actual inverse-times-derivative two-by-two product. -/
theorem spin_body {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : (A x).det = 1) (v : E) :
    body (fun y => spin (A y)) x v = spin ((A x)⁻¹ * fderiv ℝ A x v) := by
  rw [body, spin_inv (A x) hdet, fderiv_spin_field_apply hA, spin_mul]

/-- The actual spatial connection of the represented field equals the representation of its actual derivative-times-inverse two-by-two product. -/
theorem spin_spatial {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : (A x).det = 1) (v : E) :
    spatial (fun y => spin (A y)) x v = spin (fderiv ℝ A x v * (A x)⁻¹) := by
  rw [spatial, spin_inv (A x) hdet, fderiv_spin_field_apply hA, spin_mul]

end FoliationQM.SpecialLinearSpinDifferential
