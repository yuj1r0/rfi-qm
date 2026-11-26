module
public import FoliationQM.LorentzMatrixGroup
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Independent six-dimensional Lorentz Cayley coordinates

Source scope: the independent proper Lorentz frame target in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`.  The literal (+---)
metric-skew matrix equation defines a real submodule of the existing
four-by-four matrix space.  Three boost coordinates and three rotation
coordinates assemble every such matrix, with the inverse given by its
six strict upper triangular entries.  This proves a genuine continuous
linear equivalence and real dimension six without using a Spin image,
a transported group topology, or a supplied tangent-space conclusion.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.LorentzCayleyCoordinates
open LorentzMatrixGroup Matrix

/-- The six independent real boost and spatial rotation coordinates. -/
abbrev Coordinates := Fin 6 → ℝ

/-- The independent metric-skew matrices, with their inherited real submodule structure. -/
def skewSpace : Submodule ℝ Mat4 where
  carrier := {X | X.transpose * eta + eta * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    calc
      _ = (X.transpose * eta + eta * X) + (Y.transpose * eta + eta * Y) := by abel
      _ = 0 := by rw [hX, hY]; simp
  smul_mem' := by
    intro r X hX
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX]
    exact smul_zero _

/-- Membership in the independent submodule is exactly the literal source metric-skew equation. -/
theorem mem_skewSpace_iff (X : Mat4) :
    X ∈ skewSpace ↔ X.transpose * eta + eta * X = 0 := Iff.rfl

/-- Metric-skew membership is the entrywise signed antisymmetry relation in the fixed source basis. -/
theorem mem_skewSpace_iff_entries (X : Mat4) :
    X ∈ skewSpace ↔ ∀ i j, X j i * RealLorentzFrame.sign j +
      RealLorentzFrame.sign i * X i j = 0 := by
  rw [mem_skewSpace_iff]
  constructor
  · intro h i j
    have hij := congrArg (fun Y : Mat4 => Y i j) h
    simpa only [Matrix.add_apply, eta, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply, Matrix.zero_apply] using hij
  · intro h
    ext i j
    simpa only [Matrix.add_apply, eta, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply, Matrix.zero_apply] using h i j

/-- Assemble the six actual independent matrix entries by a real continuous-linear map. -/
def matrixOf : Coordinates →L[ℝ] Mat4 :=
  ({ toFun := fun v =>
      !![0, v 0, v 1, v 2;
         v 0, 0, v 3, v 4;
         v 1, -v 3, 0, v 5;
         v 2, -v 4, -v 5, 0]
     map_add' := by
       intro v w
       ext i j
       fin_cases i <;> fin_cases j <;> simp <;> ring
     map_smul' := by
       intro r v
       ext i j
       fin_cases i <;> fin_cases j <;> simp } :
    Coordinates →ₗ[ℝ] Mat4).toContinuousLinearMap

/-- The assembly map is exactly the fixed three-boost, three-rotation matrix formula. -/
theorem matrixOf_apply (v : Coordinates) : matrixOf v =
    !![0, v 0, v 1, v 2;
       v 0, 0, v 3, v 4;
       v 1, -v 3, 0, v 5;
       v 2, -v 4, -v 5, 0] := rfl

/-- Extract the six strict upper triangular entries by an ambient real continuous-linear map. -/
def coordinatesOf : Mat4 →L[ℝ] Coordinates :=
  ({ toFun := fun X => ![X 0 1, X 0 2, X 0 3, X 1 2, X 1 3, X 2 3]
     map_add' := by
       intro X Y
       ext i
       fin_cases i <;> rfl
     map_smul' := by
       intro r X
       ext i
       fin_cases i <;> rfl } : Mat4 →ₗ[ℝ] Coordinates).toContinuousLinearMap

/-- The extraction map is exactly the six prescribed actual matrix entries. -/
theorem coordinatesOf_apply (X : Mat4) :
    coordinatesOf X = ![X 0 1, X 0 2, X 0 3, X 1 2, X 1 3, X 2 3] := rfl

/-- Every assembled coordinate matrix satisfies the independent metric-skew equation. -/
theorem matrixOf_mem (v : Coordinates) : matrixOf v ∈ skewSpace := by
  rw [mem_skewSpace_iff_entries]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [matrixOf_apply, RealLorentzFrame.sign]

/-- Reading the six independent entries recovers every original coordinate tuple. -/
theorem coordinatesOf_matrixOf (v : Coordinates) : coordinatesOf (matrixOf v) = v := by
  ext i
  fin_cases i <;> simp [coordinatesOf_apply, matrixOf_apply]

/-- The six independent entries reconstruct every matrix satisfying the literal metric-skew equation. -/
theorem matrixOf_coordinatesOf (X : Mat4) (hX : X ∈ skewSpace) :
    matrixOf (coordinatesOf X) = X := by
  have h := (mem_skewSpace_iff_entries X).mp hX
  ext i j
  have hij := h i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOf_apply, coordinatesOf_apply, RealLorentzFrame.sign] at hij ⊢ <;> linarith

/-- Assembly and literal entry extraction give an actual real-linear equivalence onto the independent skew submodule. -/
def linearEquiv : Coordinates ≃ₗ[ℝ] skewSpace where
  toFun v := ⟨matrixOf v, matrixOf_mem v⟩
  invFun X := coordinatesOf X.val
  left_inv := coordinatesOf_matrixOf
  right_inv X := Subtype.ext (matrixOf_coordinatesOf X.val X.property)
  map_add' v w := Subtype.ext (map_add matrixOf v w)
  map_smul' r v := Subtype.ext (map_smul matrixOf r v)

/-- The independent six-coordinate linear equivalence is continuous in both directions in the existing matrix topology. -/
def continuousLinearEquiv : Coordinates ≃L[ℝ] skewSpace :=
  linearEquiv.toContinuousLinearEquiv

/-- The continuous equivalence has the prescribed actual ambient matrix value. -/
theorem continuousLinearEquiv_apply (v : Coordinates) :
    (continuousLinearEquiv v).val = matrixOf v := rfl

/-- The inverse continuous equivalence reads the six actual independent entries. -/
theorem continuousLinearEquiv_symm_apply (X : skewSpace) :
    continuousLinearEquiv.symm X = coordinatesOf X.val := rfl

/-- The independently defined real metric-skew matrix submodule has dimension six. -/
theorem finrank_skewSpace : Module.finrank ℝ skewSpace = 6 := by
  rw [← linearEquiv.finrank_eq]
  simp [Coordinates]

/-- The actual matrix assembly is smooth to every order in the established ambient matrix topology. -/
theorem contDiff_matrixOf (n : WithTop ℕ∞) : ContDiff ℝ n matrixOf := matrixOf.contDiff

/-- Literal entry extraction is smooth to every order on the full ambient matrix space. -/
theorem contDiff_coordinatesOf (n : WithTop ℕ∞) : ContDiff ℝ n coordinatesOf :=
  coordinatesOf.contDiff

/-- The coordinate parametrization of the independent skew submodule is smooth to every order. -/
theorem contDiff_continuousLinearEquiv (n : WithTop ℕ∞) :
    ContDiff ℝ n continuousLinearEquiv := continuousLinearEquiv.contDiff

/-- The independent skew-submodule coordinate inverse is smooth to every order. -/
theorem contDiff_continuousLinearEquiv_symm (n : WithTop ℕ∞) :
    ContDiff ℝ n continuousLinearEquiv.symm := continuousLinearEquiv.symm.contDiff

end FoliationQM.LorentzCayleyCoordinates
