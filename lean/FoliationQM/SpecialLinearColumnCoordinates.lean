module
public import FoliationQM.SpecialLinearCharts

/-!
# Global first-column coordinates for determinant-one complex matrices

Sources: the concrete determinant-one spin matrix component of v13
`prop:takabayasi` and `eq:takabayasi_polar`. Every such matrix has a
nonzero first column v=(a,c). With s=|a|²+|c|², its second column is
uniquely (-conj(c)/s,conj(a)/s)+zv. The positive denominator follows
from v≠0. The coefficient is z=(conj(a)b+conj(c)d)/s.

Both algebraic inverse identities and continuity in the existing matrix
subtype topology are proved. This gives a global homeomorphism with
(ℂ²\{0})×ℂ, with no square-root or phase choice and no topological
classification or simple-connectedness premise.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator
namespace FoliationQM.SpecialLinearColumnCoordinates
open SpinorMatrix SourcePolarDatum

/-- The literal first column of a two-by-two complex matrix. -/
abbrev Column := Fin 2 → ℂ
/-- Nonzero columns carry their inherited topology from the complex coordinate space. -/
abbrev PuncturedColumn := {u : Column // u ≠ 0}
/-- The sum of squared moduli of the two column entries. -/
def normSqColumn (u : Column) : ℝ := Complex.normSq (u 0) + Complex.normSq (u 1)
/-- A nonzero column has strictly positive squared Euclidean length. -/
theorem normSqColumn_pos (u : PuncturedColumn) : 0 < normSqColumn u.val := by
  have h0 := Complex.normSq_nonneg (u.val 0)
  have h1 := Complex.normSq_nonneg (u.val 1)
  have hne : normSqColumn u.val ≠ 0 := by
    intro h
    have e0 : u.val 0 = 0 := Complex.normSq_eq_zero.mp (by dsimp [normSqColumn] at h; linarith)
    have e1 : u.val 1 = 0 := Complex.normSq_eq_zero.mp (by dsimp [normSqColumn] at h; linarith)
    apply u.property
    ext i
    fin_cases i <;> assumption
  exact lt_of_le_of_ne (add_nonneg h0 h1) (Ne.symm hne)
/-- The complex scalar denominator in column reconstruction is nonzero. -/
theorem normSqColumn_cast_ne (u : PuncturedColumn) : (normSqColumn u.val : ℂ) ≠ 0 := by
  exact_mod_cast (normSqColumn_pos u).ne'
/-- The first column and one complex fiber coordinate reconstruct a determinant-one matrix without choosing a square root. -/
def matrixOf (u : PuncturedColumn) (z : ℂ) : Mat2 :=
  !![u.val 0, -(starRingEnd ℂ) (u.val 1) / (normSqColumn u.val : ℂ) + z * u.val 0;
     u.val 1, (starRingEnd ℂ) (u.val 0) / (normSqColumn u.val : ℂ) + z * u.val 1]
/-- The conjugate perpendicular column and the first-column multiple give determinant one. -/
theorem matrixOf_det (u : PuncturedColumn) (z : ℂ) : (matrixOf u z).det = 1 := by
  have hs := normSqColumn_cast_ne u
  rw [Matrix.det_fin_two]
  change u.val 0 * ((starRingEnd ℂ) (u.val 0) / (normSqColumn u.val : ℂ) + z * u.val 1) -
    (- (starRingEnd ℂ) (u.val 1) / (normSqColumn u.val : ℂ) + z * u.val 0) * u.val 1 = 1
  field_simp
  simp only [normSqColumn, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self]
  ring

/-- The first column of an actual determinant-one matrix is nonzero. -/
def column (A : SpecialLinearMatrix) : PuncturedColumn :=
  ⟨![A.val 0 0, A.val 1 0], by
    intro h
    have ha := congrFun h 0
    have hc := congrFun h 1
    have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using A.property
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.zero_apply] at ha hc
    rw [ha, hc] at hd
    norm_num at hd⟩
/-- The complex coefficient of the second column along the first column. -/
def fiber (A : SpecialLinearMatrix) : ℂ :=
  ((starRingEnd ℂ) (A.val 0 0) * A.val 0 1 + (starRingEnd ℂ) (A.val 1 0) * A.val 1 1) / (normSqColumn (column A).val : ℂ)
/-- Every actual determinant-one matrix is reconstructed from its first column and the explicit fiber coefficient. -/
theorem matrixOf_column_fiber (A : SpecialLinearMatrix) : matrixOf (column A) (fiber A) = A.val := by
  have hs := normSqColumn_cast_ne (column A)
  have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · change -(starRingEnd ℂ) (A.val 1 0) / (normSqColumn (column A).val : ℂ) +
      (((starRingEnd ℂ) (A.val 0 0)*A.val 0 1+(starRingEnd ℂ) (A.val 1 0)*A.val 1 1) /
        (normSqColumn (column A).val : ℂ)) * A.val 0 0 = A.val 0 1
    field_simp
    simp only [normSqColumn, column, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Complex.ofReal_add, Complex.normSq_eq_conj_mul_self]
    linear_combination (starRingEnd ℂ) (A.val 1 0) * hd
  · rfl
  · change (starRingEnd ℂ) (A.val 0 0) / (normSqColumn (column A).val : ℂ) +
      (((starRingEnd ℂ) (A.val 0 0)*A.val 0 1+(starRingEnd ℂ) (A.val 1 0)*A.val 1 1) /
        (normSqColumn (column A).val : ℂ)) * A.val 1 0 = A.val 1 1
    field_simp
    simp only [normSqColumn, column, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Complex.ofReal_add, Complex.normSq_eq_conj_mul_self]
    linear_combination -((starRingEnd ℂ) (A.val 0 0)) * hd

/-- The global coordinates consist of a nonzero first column and a complex fiber coefficient. -/
abbrev Coordinates := PuncturedColumn × ℂ

/-- The determinant-one matrix represented by the actual column coordinates. -/
def ofCoordinates (p : Coordinates) : SpecialLinearMatrix :=
  ⟨matrixOf p.1 p.2, matrixOf_det p.1 p.2⟩

/-- Reconstructing a matrix leaves the specified first column unchanged. -/
@[simp] theorem column_ofCoordinates (p : Coordinates) : column (ofCoordinates p) = p.1 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> rfl

/-- The literal fiber formula recovers the chosen complex coefficient. -/
@[simp] theorem fiber_ofCoordinates (p : Coordinates) : fiber (ofCoordinates p) = p.2 := by
  have hs := normSqColumn_cast_ne p.1
  unfold fiber
  rw [column_ofCoordinates]
  change ((starRingEnd ℂ) (p.1.val 0) *
      (-(starRingEnd ℂ) (p.1.val 1) / (normSqColumn p.1.val : ℂ) + p.2 * p.1.val 0) +
    (starRingEnd ℂ) (p.1.val 1) *
      ((starRingEnd ℂ) (p.1.val 0) / (normSqColumn p.1.val : ℂ) + p.2 * p.1.val 1)) /
        (normSqColumn p.1.val : ℂ) = p.2
  field_simp
  simp only [normSqColumn, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self]
  ring

/-- Reconstructing from the actual first column and fiber gives the original subtype element. -/
@[simp] theorem ofCoordinates_column_fiber (A : SpecialLinearMatrix) :
    ofCoordinates (column A, fiber A) = A :=
  Subtype.ext (matrixOf_column_fiber A)

private def entryCLM (i j : Fin 2) : Mat2 →L[ℝ] ℂ :=
  ({ toFun := fun A => A i j
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Mat2 →ₗ[ℝ] ℂ).toContinuousLinearMap

private def assembleCLM : (Fin 4 → ℂ) →L[ℝ] Mat2 :=
  ({ toFun := fun z => !![z 0, z 1; z 2, z 3]
     map_add' := by intros; ext i j; fin_cases i <;> fin_cases j <;> rfl
     map_smul' := by intros; ext i j; fin_cases i <;> fin_cases j <;> rfl } :
       (Fin 4 → ℂ) →ₗ[ℝ] Mat2).toContinuousLinearMap

/-- The squared column length is continuous in the existing coordinate topology. -/
theorem continuous_normSqColumn : Continuous normSqColumn :=
  (Complex.continuous_normSq.comp (continuous_apply 0)).add
    (Complex.continuous_normSq.comp (continuous_apply 1))

/-- Extracting the nonzero first column is continuous in the natural matrix subtype topology. -/
theorem continuous_column : Continuous column := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  fin_cases i
  · exact (entryCLM 0 0).continuous.comp continuous_subtype_val
  · exact (entryCLM 1 0).continuous.comp continuous_subtype_val

/-- The explicit complex fiber coefficient is continuous because the squared column length never vanishes. -/
theorem continuous_fiber : Continuous fiber := by
  have he (i j : Fin 2) : Continuous (fun A : SpecialLinearMatrix => A.val i j) :=
    (entryCLM i j).continuous.comp continuous_subtype_val
  exact ((Complex.continuous_conj.comp (he 0 0)).mul (he 0 1) |>.add
    ((Complex.continuous_conj.comp (he 1 0)).mul (he 1 1))).div
      (Complex.continuous_ofReal.comp
        (continuous_normSqColumn.comp (continuous_subtype_val.comp continuous_column)))
      (fun A => normSqColumn_cast_ne (column A))

/-- The reconstruction formula is continuous jointly in the nonzero column and complex coefficient. -/
theorem continuous_matrixOf : Continuous (fun p : Coordinates => matrixOf p.1 p.2) := by
  have hu (i : Fin 2) : Continuous (fun p : Coordinates => p.1.val i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
  have hs : Continuous (fun p : Coordinates => (normSqColumn p.1.val : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_normSqColumn.comp (continuous_subtype_val.comp continuous_fst))
  have hb : Continuous (fun p : Coordinates =>
      -(starRingEnd ℂ) (p.1.val 1) / (normSqColumn p.1.val : ℂ) + p.2 * p.1.val 0) :=
    (((Complex.continuous_conj.comp (hu 1)).neg).div hs
      (fun p => normSqColumn_cast_ne p.1)).add (continuous_snd.mul (hu 0))
  have hd : Continuous (fun p : Coordinates =>
      (starRingEnd ℂ) (p.1.val 0) / (normSqColumn p.1.val : ℂ) + p.2 * p.1.val 1) :=
    ((Complex.continuous_conj.comp (hu 0)).div hs
      (fun p => normSqColumn_cast_ne p.1)).add (continuous_snd.mul (hu 1))
  have hv : Continuous (fun p : Coordinates =>
      (![p.1.val 0,
          -(starRingEnd ℂ) (p.1.val 1) / (normSqColumn p.1.val : ℂ) + p.2 * p.1.val 0,
          p.1.val 1,
          (starRingEnd ℂ) (p.1.val 0) / (normSqColumn p.1.val : ℂ) + p.2 * p.1.val 1] :
        Fin 4 → ℂ)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact hu 0
    · exact hb
    · exact hu 1
    · exact hd
  exact assembleCLM.continuous.comp hv

/-- Reconstructing the actual determinant-one subtype element is continuous. -/
theorem continuous_ofCoordinates : Continuous ofCoordinates :=
  continuous_matrixOf.subtype_mk _

/-- The explicit column decomposition is a homeomorphism for the pre-existing natural topologies. -/
def columnHomeomorph : SpecialLinearMatrix ≃ₜ Coordinates where
  toFun A := (column A, fiber A)
  invFun := ofCoordinates
  left_inv := ofCoordinates_column_fiber
  right_inv p := by simp
  continuous_toFun := continuous_column.prodMk continuous_fiber
  continuous_invFun := continuous_ofCoordinates

/-- The global homeomorphism uses the literal first column and rational fiber coefficient. -/
theorem columnHomeomorph_apply (A : SpecialLinearMatrix) :
    columnHomeomorph A = (column A, fiber A) := rfl

/-- The inverse homeomorphism is the explicit determinant-one reconstruction. -/
theorem columnHomeomorph_symm_apply (p : Coordinates) :
    columnHomeomorph.symm p = ofCoordinates p := rfl

/-- The inverse homeomorphism has the stated ambient matrix, with no abstract matrix identification. -/
theorem columnHomeomorph_symm_matrix (p : Coordinates) :
    (columnHomeomorph.symm p).val = matrixOf p.1 p.2 := rfl

end FoliationQM.SpecialLinearColumnCoordinates
