module

public import FoliationQM.SecondOrderFrechet
public import FoliationQM.PolarSecondDifferential

/-!
# Fréchet Hessian of the normal-coordinate half-density polynomial

In v13 `lem:rnc_half_density`, the quadratic part of the fourth root of the
absolute metric determinant has Ricci coefficient −1/12. Differentiating the
polynomial in two arbitrary directions recovers the mixed Hessian. The final
contraction uses the manuscript's four-dimensional signature (+---).
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCHalfDensityJet

open scoped BigOperators
open ContinuousLinearMap

/-- Real coordinates for a finite-dimensional normal-coordinate model. -/
abbrev Coordinates (n : ℕ) := Fin n → ℝ

variable {n : ℕ}

/-- The continuous bilinear form with the given covariant matrix entries. -/
def form (A : Matrix (Fin n) (Fin n) ℝ) : Coordinates n →L[ℝ] Coordinates n →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j •
    (proj i : Coordinates n →L[ℝ] ℝ).smulRight (proj j : Coordinates n →L[ℝ] ℝ)

/-- Evaluation of the form is the double coordinate sum. -/
theorem form_apply (A : Matrix (Fin n) (Fin n) ℝ) (u v : Coordinates n) :
    form A u v = ∑ i, ∑ j, A i j * u i * v j := by
  simp [form, sum_apply, mul_assoc]

/-- The normal-coordinate quadratic model of the metric half-density. -/
def weight (A : Matrix (Fin n) (Fin n) ℝ) (y : Coordinates n) : ℝ :=
  1 - (1 / 12 : ℝ) * form A y y

/-- The model equals the manuscript's coordinate polynomial, including mixed terms. -/
theorem weight_eq (A : Matrix (Fin n) (Fin n) ℝ) (y : Coordinates n) :
    weight A y = 1 - (1 / 12 : ℝ) * ∑ i, ∑ j, A i j * y i * y j := by
  rw [weight, form_apply]

/-- The quadratic model is smooth to every order. -/
theorem contDiff_weight (A : Matrix (Fin n) (Fin n) ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (weight A) :=
  contDiff_const.sub (contDiff_const.mul ((form A).contDiff.clm_apply contDiff_id))

/-- The symmetric bilinear map obtained from the two slots of the quadratic polynomial. -/
def hessian (A : Matrix (Fin n) (Fin n) ℝ) : Coordinates n →L[ℝ] Coordinates n →L[ℝ] ℝ :=
  (-1 / 12 : ℝ) • (form A + (form A).flip)

/-- The two argument orders of the coefficient enter the actual quadratic Hessian. -/
theorem hessian_apply (A : Matrix (Fin n) (Fin n) ℝ) (u v : Coordinates n) :
    hessian A u v = -(form A u v + form A v u) / 12 := by
  simp only [hessian, smul_apply, add_apply, smul_eq_mul, flip_apply]
  ring

/-- The polynomial has value one at the RNC center. -/
theorem weight_zero (A : Matrix (Fin n) (Fin n) ℝ) : weight A 0 = 1 := by
  simp [weight]

/-- The first Fréchet derivative is the contraction of the constant Hessian with position. -/
theorem hasFDerivAt_weight (A : Matrix (Fin n) (Fin n) ℝ) (y : Coordinates n) :
    HasFDerivAt (weight A) (hessian A y) y := by
  have hs (u v : Coordinates n) : hessian A u v = hessian A v u := by
    rw [hessian_apply, hessian_apply, add_comm]
  have he : weight A = fun u => 1 + (1 / 2 : ℝ) * hessian A u u := by
    funext u
    rw [weight, hessian_apply]
    ring
  rw [he]
  exact (SecondOrderFrechet.hasFDerivAt_half_diagonal hs y).const_add 1

/-- The first derivative vanishes at the chart center. -/
theorem gradient_zero (A : Matrix (Fin n) (Fin n) ℝ) :
    fderiv ℝ (weight A) 0 = 0 := by
  rw [(hasFDerivAt_weight A 0).fderiv, map_zero]

/-- The derivative of the whole Fréchet differential is the constant symmetric Hessian. -/
theorem hasFDerivAt_gradient (A : Matrix (Fin n) (Fin n) ℝ) (y : Coordinates n) :
    HasFDerivAt (fderiv ℝ (weight A)) (hessian A) y := by
  have he : fderiv ℝ (weight A) = hessian A := funext fun z => (hasFDerivAt_weight A z).fderiv
  rw [he]
  exact (hessian A).hasFDerivAt

/-- Coordinate basis vectors extract the covariant tensor entry from the bilinear form. -/
theorem form_basis (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    form A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [form_apply, Pi.single_apply, mul_ite]

/-- The mixed Fréchet second partial is the symmetrized matrix coefficient times −1/12. -/
theorem mixed_partial (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    fderiv ℝ (fderiv ℝ (weight A)) 0 (Pi.single i 1) (Pi.single j 1) =
      -(A i j + A j i) / 12 := by
  rw [(hasFDerivAt_gradient A 0).fderiv, hessian_apply, form_basis, form_basis]

/-- A symmetric Ricci tensor has mixed half-density Hessian entry −Ricᵢⱼ/6. -/
theorem mixed_partial_symmetric (A : Matrix (Fin n) (Fin n) ℝ)
    (hs : ∀ i j, A i j = A j i) (i j : Fin n) :
    fderiv ℝ (fderiv ℝ (weight A)) 0 (Pi.single i 1) (Pi.single j 1) = -(A i j) / 6 := by
  rw [mixed_partial, hs j i]
  ring

/-- In any finite dimension, contracting the Hessian of the model against
the inverse metric gives minus one sixth of its contraction with Ricci. -/
theorem contracted_hessian (gInv A : Matrix (Fin n) (Fin n) ℝ) (hs : ∀ i j, A i j = A j i) :
    (∑ i, ∑ j, gInv i j * fderiv ℝ (fderiv ℝ (weight A)) 0 (Pi.single i 1) (Pi.single j 1)) =
      -(∑ i, ∑ j, gInv i j * A i j) / 6 := by
  simp only [mixed_partial_symmetric A hs, div_eq_mul_inv, neg_mul, mul_neg, ← mul_assoc,
    ← Finset.sum_mul, Finset.sum_neg_distrib]

/-- Scalar curvature in a four-dimensional Lorentz-orthonormal coordinate basis. -/
def scalarCurvature (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 0 0 - A 1 1 - A 2 2 - A 3 3

/-- The signed sum of the actual four directional second derivatives at the center is −ℛ/6. -/
theorem box_weight (A : Matrix (Fin 4) (Fin 4) ℝ) :
    PolarSecondDifferential.box (weight A) (fun i => Pi.single i 1) 0 =
      -scalarCurvature A / 6 := by
  have hd (v : Coordinates 4) :
      PolarSecondDifferential.directionalDerivative (weight A) v =
        fun z => (hessian A).flip v z := by
    funext z
    exact congrArg (fun L : Coordinates 4 →L[ℝ] ℝ => L v) (hasFDerivAt_weight A z).fderiv
  have hdd (i : Fin 4) : PolarSecondDifferential.secondDirectionalDerivative (weight A)
      (Pi.single i 1) 0 = -(A i i + A i i) / 12 := by
    rw [PolarSecondDifferential.secondDirectionalDerivative, hd, PolarSecondDifferential.directionalDerivative,
      ((hessian A).flip (Pi.single i 1)).hasFDerivAt.fderiv, flip_apply, hessian_apply, form_basis]
  simp only [PolarSecondDifferential.box, hdd, scalarCurvature]
  ring

end FoliationQM.RNCHalfDensityJet
