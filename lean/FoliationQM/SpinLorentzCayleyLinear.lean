module
public import FoliationQM.SpecialLinearCharts
public import FoliationQM.LorentzManifold

/-!
# Explicit real linear coordinates for the Spin–Lorentz Cayley bridge

Source scope: the six-parameter Spin/Lorentz frame identification in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The actual three-complex-entry
special-linear chart and independent six-real-entry Lorentz Cayley model
are related here by an explicit real continuous-linear equivalence. Both
directions are proved from their literal coordinate formulas.

The coordinate order is (01,02,03,12,13,23), including the physical-frame
signs and the inverse Cayley factor one half. This file establishes the
linear algebra only. Its identification with an actual derivative is a
separate result, not an assumption in this construction.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.SpinLorentzCayleyLinear

/-- The source is the existing intrinsic three-complex-coordinate special-linear model. -/
abbrev SourceModel := SpecialLinearCharts.Model

/-- The target is the independently constructed six-real-coordinate Lorentz model. -/
abbrev TargetModel := LorentzManifold.Model

/-- The actual identity special-linear matrix has first-chart coordinates one, zero, zero. -/
def basePoint : SourceModel := ![1, 0, 0]

/-- The special-linear base coordinate has its literal nonzero first pivot. -/
theorem basePoint_zero_ne : basePoint 0 ≠ 0 := by
  norm_num [basePoint]

/-- The existing rational special-linear matrix formula reconstructs identity at the specified base coordinate. -/
theorem matrixA_basePoint : SpecialLinearCharts.matrixA basePoint = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearCharts.matrixA, basePoint]

/-- Three complex coordinate increments assemble the literal trace-zero two-by-two tangent matrix by a real continuous-linear map. -/
def tangentMatrix : SourceModel →L[ℝ] SpinorMatrix.Mat2 :=
  ({ toFun := fun v => !![v 0, v 1; v 2, -v 0]
     map_add' := by
       intro v w
       ext i j
       fin_cases i <;> fin_cases j <;> simp [add_comm]
     map_smul' := by
       intro r v
       ext i j
       fin_cases i <;> fin_cases j <;> simp } :
    SourceModel →ₗ[ℝ] SpinorMatrix.Mat2).toContinuousLinearMap

/-- The tangent assembly is exactly the independent upper-left, upper-right, lower-left entries and the negative upper-left entry. -/
theorem tangentMatrix_apply (v : SourceModel) :
    tangentMatrix v = !![v 0, v 1; v 2, -v 0] := rfl

/-- Every coordinate tangent assembled by the actual linear map has trace zero. -/
theorem tangentMatrix_trace (v : SourceModel) : Matrix.trace (tangentMatrix v) = 0 := by
  simp [tangentMatrix_apply, Matrix.trace, Fin.sum_univ_succ]

/-- The explicit six-real-coordinate linear equivalence retains the physical Lorentz signs and inverse Cayley factor one half. -/
def linearEquiv : SourceModel ≃ₗ[ℝ] TargetModel where
  toFun v := ![((v 1).re + (v 2).re) / 2,
    ((v 2).im - (v 1).im) / 2, (v 0).re, (v 0).im,
    ((v 2).re - (v 1).re) / 2, ((v 1).im + (v 2).im) / 2]
  invFun x := ![(x 2 : ℂ) + Complex.I * (x 3 : ℂ),
    ((x 0 - x 4 : ℝ) : ℂ) + Complex.I * ((x 5 - x 1 : ℝ) : ℂ),
    ((x 0 + x 4 : ℝ) : ℂ) + Complex.I * ((x 5 + x 1 : ℝ) : ℂ)]
  left_inv v := by
    ext i
    fin_cases i <;> apply Complex.ext <;> simp <;> ring
  right_inv x := by
    ext i
    fin_cases i <;> simp
  map_add' v w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r v := by
    ext i
    fin_cases i <;> simp <;> ring

/-- Finite-dimensional continuity upgrades the explicit coordinate equivalence to a real continuous-linear equivalence. -/
def jacobian : SourceModel ≃L[ℝ] TargetModel := linearEquiv.toContinuousLinearEquiv

/-- The coordinate equivalence reads precisely the six physical-frame Cayley linear coefficients in the order 01,02,03,12,13,23. -/
theorem jacobian_apply (v : SourceModel) :
    jacobian v = ![((v 1).re + (v 2).re) / 2,
      ((v 2).im - (v 1).im) / 2, (v 0).re, (v 0).im,
      ((v 2).re - (v 1).re) / 2, ((v 1).im + (v 2).im) / 2] := rfl

/-- The inverse coordinate equivalence reconstructs the three literal complex tangent entries from the independent real Cayley coordinates. -/
theorem jacobian_symm_apply (x : TargetModel) :
    jacobian.symm x = ![(x 2 : ℂ) + Complex.I * (x 3 : ℂ),
      ((x 0 - x 4 : ℝ) : ℂ) + Complex.I * ((x 5 - x 1 : ℝ) : ℂ),
      ((x 0 + x 4 : ℝ) : ℂ) + Complex.I * ((x 5 + x 1 : ℝ) : ℂ)] := rfl

end FoliationQM.SpinLorentzCayleyLinear
