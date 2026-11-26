module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases

/-!
# Genuine exterior algebra on the seven-dimensional mass-shell chart

Source: v13 `thm:contact_period`, the contact-volume calculation. The ordered
coordinates are x0, x1, p1, x2, p2, x3, p3. Products below belong to the exterior
algebra of the actual dual space. Their evaluations are determinants of genuine
alternating maps; the volume is proved nonzero by evaluation on coordinate
tangent vectors.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ContactExteriorBasics

/-- Seven chart coordinates ordered x0, x1, p1, x2, p2, x3, p3. -/
abbrev Space := Fin 7 → ℝ

/-- Algebraic covectors on the chart tangent space. -/
abbrev Covectors := Module.Dual ℝ Space

/-- The genuine exterior algebra of chart covectors. -/
abbrev Forms := ExteriorAlgebra ℝ Covectors

/-- The coordinate projection covector. -/
def coordinate (i : Fin 7) : Covectors := LinearMap.proj i

/-- The coordinate tangent vector dual to a coordinate covector. -/
def tangent (i : Fin 7) : Space := Pi.single i 1

/-- A coordinate covector embedded in the exterior algebra. -/
def e (i : Fin 7) : Forms := ExteriorAlgebra.ι ℝ (coordinate i)

/-- The ordered sevenfold exterior volume element. -/
def volume : Forms := e 0 * e 1 * e 2 * e 3 * e 4 * e 5 * e 6

/-- Evaluation of a covector on each member of a tangent tuple is linear. -/
def covectorValues {n : ℕ} (v : Fin n → Space) : Covectors →ₗ[ℝ] (Fin n → ℝ) where
  toFun a i := a (v i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Determinant evaluation is alternating in the tuple of covector factors. -/
def determinantAlternating {n : ℕ} (v : Fin n → Space) :
    Covectors [⋀^Fin n]→ₗ[ℝ] ℝ :=
  Matrix.detRowAlternating.compLinearMap (covectorValues v)

/-- Degree-n evaluation on a tangent tuple, extended linearly to the full exterior algebra. -/
def evaluation (n : ℕ) (v : Fin n → Space) : Forms →ₗ[ℝ] ℝ :=
  ExteriorAlgebra.liftAlternating fun k =>
    if h : k = n then h.symm ▸ determinantAlternating v else 0

/-- Degree-one evaluation of an exterior form on one tangent vector. -/
def evalOne (F : Forms) (v : Space) : ℝ := evaluation 1 ![v] F

/-- Degree-two evaluation of an exterior form on an ordered tangent pair. -/
def evalTwo (F : Forms) (v w : Space) : ℝ := evaluation 2 ![v, w] F

/-- Coordinate covectors and tangent vectors have the Kronecker pairing. -/
theorem coordinate_tangent (i j : Fin 7) : coordinate i (tangent j) = if i = j then 1 else 0 := by
  simp [coordinate, tangent, Pi.single_apply]

/-- Evaluating a decomposable exterior product gives its determinant pairing. -/
theorem evaluation_ιMulti {n : ℕ} (v : Fin n → Space) (a : Fin n → Covectors) :
    evaluation n v (ExteriorAlgebra.ιMulti ℝ n a) = Matrix.det (fun i j => a i (v j)) := by
  simp only [evaluation, ExteriorAlgebra.liftAlternating_apply_ιMulti, dite_true]
  rfl

/-- One embedded covector evaluates as the covector itself. -/
theorem evalOne_ι (a : Covectors) (v : Space) :
    evalOne (ExteriorAlgebra.ι ℝ a) v = a v := by
  change evaluation 1 ![v] (ExteriorAlgebra.ι ℝ a) = a v
  have h := (evaluation_ιMulti ![v] ![a]).trans
    (Matrix.det_fin_one (fun i j => (![a] i) (![v] j)))
  simpa [ExteriorAlgebra.ιMulti_succ_apply] using h

/-- A product of two embedded covectors evaluates as the alternating bilinear pairing. -/
theorem evalTwo_ι_mul (a b : Covectors) (v w : Space) :
    evalTwo (ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ b) v w =
      a v * b w - a w * b v := by
  have h := (evaluation_ιMulti ![v, w] ![a, b]).trans
    (Matrix.det_fin_two (fun i j => (![a, b] i) (![v, w] j)))
  simpa [evalTwo, ExteriorAlgebra.ιMulti_succ_apply] using h

/-- Degree-one evaluation preserves sums of exterior forms. -/
@[simp]
theorem evalOne_add (F G : Forms) (v : Space) :
    evalOne (F + G) v = evalOne F v + evalOne G v :=
  map_add (evaluation 1 ![v]) F G

/-- Degree-one evaluation preserves scalar multiplication of exterior forms. -/
@[simp]
theorem evalOne_smul (r : ℝ) (F : Forms) (v : Space) :
    evalOne (r • F) v = r * evalOne F v :=
  map_smul (evaluation 1 ![v]) r F

/-- Degree-one evaluation sends the zero exterior form to zero. -/
@[simp]
theorem evalOne_zero (v : Space) : evalOne 0 v = 0 :=
  map_zero (evaluation 1 ![v])

/-- Degree-one evaluation changes sign under exterior-form negation. -/
@[simp]
theorem evalOne_neg (F : Forms) (v : Space) : evalOne (-F) v = -evalOne F v :=
  map_neg (evaluation 1 ![v]) F

/-- Degree-one evaluation of a coordinate generator is the corresponding component. -/
@[simp]
theorem evalOne_e (i : Fin 7) (v : Space) : evalOne (e i) v = v i :=
  evalOne_ι (coordinate i) v

/-- Degree-two evaluation preserves sums of exterior forms. -/
@[simp]
theorem evalTwo_add (F G : Forms) (v w : Space) :
    evalTwo (F + G) v w = evalTwo F v w + evalTwo G v w :=
  map_add (evaluation 2 ![v, w]) F G

/-- Degree-two evaluation preserves scalar multiplication of exterior forms. -/
@[simp]
theorem evalTwo_smul (r : ℝ) (F : Forms) (v w : Space) :
    evalTwo (r • F) v w = r * evalTwo F v w :=
  map_smul (evaluation 2 ![v, w]) r F

/-- Degree-two evaluation sends the zero exterior form to zero. -/
@[simp]
theorem evalTwo_zero (v w : Space) : evalTwo 0 v w = 0 :=
  map_zero (evaluation 2 ![v, w])

/-- Degree-two evaluation changes sign under exterior-form negation. -/
@[simp]
theorem evalTwo_neg (F : Forms) (v w : Space) :
    evalTwo (-F) v w = -evalTwo F v w :=
  map_neg (evaluation 2 ![v, w]) F

/-- Two coordinate generators evaluate as the corresponding alternating minor. -/
@[simp]
theorem evalTwo_e_mul_e (i j : Fin 7) (v w : Space) :
    evalTwo (e i * e j) v w = v i * w j - w i * v j :=
  evalTwo_ι_mul (coordinate i) (coordinate j) v w

/-- The ordered coordinate product is the universal alternating sevenfold product. -/
theorem volume_eq_ιMulti : volume = ExteriorAlgebra.ιMulti ℝ 7 coordinate := by
  simp [volume, e, ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail, mul_assoc]

/-- The actual exterior volume evaluates to one on the ordered coordinate tangents. -/
theorem evaluation_volume : evaluation 7 tangent volume = 1 := by
  rw [volume_eq_ιMulti, evaluation_ιMulti]
  have h : (fun i j : Fin 7 => coordinate i (tangent j)) = (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
    ext i j
    simp [coordinate_tangent, Matrix.one_apply]
  rw [h, Matrix.det_one]

/-- The genuine sevenfold volume element is nonzero, witnessed by determinant evaluation. -/
theorem volume_ne_zero : volume ≠ 0 := by
  intro h
  have hv := evaluation_volume
  rw [h, map_zero] at hv
  exact zero_ne_one hv

/-- Every degree-one generator has exterior square zero. -/
theorem generator_sq_zero (a : Covectors) :
    ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ a = 0 :=
  ExteriorAlgebra.ι_sq_zero a

/-- Any two degree-one generators anticommute. -/
theorem generator_anticomm (a b : Covectors) :
    ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ b =
      -(ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ a) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)

/-- A repeated degree-one factor separated by one factor annihilates the product. -/
theorem generator_mul_generator_mul_self (a b : Covectors) :
    ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ b * ExteriorAlgebra.ι ℝ a = 0 := by
  rw [generator_anticomm a b, neg_mul, mul_assoc, generator_sq_zero, mul_zero, neg_zero]

/-- Every coordinate generator has square zero. -/
theorem e_sq_zero (i : Fin 7) : e i * e i = 0 := generator_sq_zero (coordinate i)

/-- Coordinate generators anticommute in the exterior algebra. -/
theorem e_anticomm (i j : Fin 7) : e i * e j = -(e j * e i) :=
  generator_anticomm (coordinate i) (coordinate j)

end FoliationQM.ContactExteriorBasics
