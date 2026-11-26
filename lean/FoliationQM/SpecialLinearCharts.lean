module
public import FoliationQM.SourcePolarDatum
public import FoliationQM.SpinorMatrixSmooth
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Intrinsic rational charts for actual determinant-one complex matrices

Sources: the concrete six-parameter matrix component of v13
`prop:takabayasi` and `eq:takabayasi_polar`. The existing natural subtype
of complex two-by-two matrices with determinant one is covered by two
actual open partial homeomorphisms. The first retains entries (a,b,c)
where a is nonzero and recovers d=(1+bc)/a. The second retains (a,b,d)
where b is nonzero and recovers c=(ad-1)/b. The determinant equation
proves the inverse identities and that these two sources cover every
matrix in the subtype.

The matrix subtype topology is preserved. Both coordinate extractors
are genuine real continuous-linear maps on the ambient matrix space.
Both inverse matrix formulas, and the actual chart inverses on their
targets, are real-smooth to every order. Nonzero pivot domains are
explicit throughout the inverse proofs. The total inverse functions
use the identity matrix off their targets; only their target values
enter the charts and smoothness statements. These charts supply the
intrinsic atlas ingredients without selecting an abstract Spin model
or assigning a quotient manifold structure.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Set Topology
namespace FoliationQM.SpecialLinearCharts
open SpinorMatrix SourcePolarDatum

/-- Three complex coordinates form the real six-dimensional local model for the actual determinant-one matrix subtype. -/
abbrev Model := Fin 3 → ℂ

/-- The first chart extracts the first row and lower-left entry by an actual real continuous-linear map on matrices. -/
def coordinatesACLM : Mat2 →L[ℝ] Model :=
  ({ toFun := fun A => ![A 0 0, A 0 1, A 1 0]
     map_add' := by intros; ext i; fin_cases i <;> rfl
     map_smul' := by intros; ext i; fin_cases i <;> rfl } : Mat2 →ₗ[ℝ] Model).toContinuousLinearMap

/-- The second chart extracts the first row and lower-right entry by an actual real continuous-linear map on matrices. -/
def coordinatesBCLM : Mat2 →L[ℝ] Model :=
  ({ toFun := fun A => ![A 0 0, A 0 1, A 1 1]
     map_add' := by intros; ext i; fin_cases i <;> rfl
     map_smul' := by intros; ext i; fin_cases i <;> rfl } : Mat2 →ₗ[ℝ] Model).toContinuousLinearMap

/-- The first intrinsic chart coordinates retain the entries a, b and c of the actual matrix. -/
def coordinatesA (A : SpecialLinearMatrix) : Model := coordinatesACLM A.val

/-- The second intrinsic chart coordinates retain the entries a, b and d of the actual matrix. -/
def coordinatesB (A : SpecialLinearMatrix) : Model := coordinatesBCLM A.val

/-- The first rational inverse matrix reconstructs the lower-right entry from the determinant equation. -/
def matrixA (z : Model) : Mat2 := !![z 0, z 1; z 2, (1 + z 1 * z 2) / z 0]

/-- The second rational inverse matrix reconstructs the lower-left entry from the determinant equation. -/
def matrixB (z : Model) : Mat2 := !![z 0, z 1; (z 0 * z 2 - 1) / z 1, z 2]

/-- On its explicit nonzero first-pivot domain, the first reconstructed matrix has actual determinant one. -/
theorem matrixA_det {z : Model} (hz : z 0 ≠ 0) : (matrixA z).det = 1 := by
  simp [matrixA, Matrix.det_fin_two]
  field_simp
  ring

/-- On its explicit nonzero second-pivot domain, the second reconstructed matrix has actual determinant one. -/
theorem matrixB_det {z : Model} (hz : z 1 ≠ 0) : (matrixB z).det = 1 := by
  simp [matrixB, Matrix.det_fin_two]
  field_simp
  ring

/-- Every actual determinant-one matrix has a nonzero entry in its first row, so the two intrinsic chart sources cover the subtype. -/
theorem pivot_cover (A : SpecialLinearMatrix) : A.val 0 0 ≠ 0 ∨ A.val 0 1 ≠ 0 := by
  by_cases ha : A.val 0 0 ≠ 0
  · exact Or.inl ha
  · apply Or.inr
    intro hb
    have hd := A.property
    simp [Matrix.det_fin_two, not_ne_iff.mp ha, hb] at hd

/-- The first rational reconstruction returns the original matrix whenever its first pivot is nonzero. -/
theorem matrixA_coordinatesA (A : SpecialLinearMatrix) (ha : A.val 0 0 ≠ 0) :
    matrixA (coordinatesA A) = A.val := by
  have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have he : (1 + A.val 0 1 * A.val 1 0) / A.val 0 0 = A.val 1 1 := by
    apply (div_eq_iff ha).mpr
    linear_combination -hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixA, coordinatesA, coordinatesACLM, he]

/-- The second rational reconstruction returns the original matrix whenever its second pivot is nonzero. -/
theorem matrixB_coordinatesB (A : SpecialLinearMatrix) (hb : A.val 0 1 ≠ 0) :
    matrixB (coordinatesB A) = A.val := by
  have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have he : (A.val 0 0 * A.val 1 1 - 1) / A.val 0 1 = A.val 1 0 := by
    apply (div_eq_iff hb).mpr
    linear_combination hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixB, coordinatesB, coordinatesBCLM, he]

private def assembleCLM : (Fin 4 → ℂ) →L[ℝ] Mat2 :=
  ({ toFun := fun z => !![z 0, z 1; z 2, z 3]
     map_add' := by intros; ext i j; fin_cases i <;> fin_cases j <;> rfl
     map_smul' := by intros; ext i j; fin_cases i <;> fin_cases j <;> rfl } : (Fin 4 → ℂ) →ₗ[ℝ] Mat2).toContinuousLinearMap

/-- The actual first rational inverse matrix is real-smooth to every order on its nonzero pivot domain. -/
theorem contDiffOn_matrixA (n : WithTop ℕ∞) :
    ContDiffOn ℝ n matrixA {z : Model | z 0 ≠ 0} := by
  have hp (i : Fin 3) : ContDiffOn ℝ n (fun z : Model => z i) {z : Model | z 0 ≠ 0} :=
    (contDiff_apply ℝ (fun _ : Fin 3 => ℂ) i).contDiffOn
  have hr : ContDiffOn ℝ n (fun z : Model => (1+z 1*z 2)*(z 0)⁻¹) {z | z 0 ≠ 0} :=
    (contDiffOn_const.add ((hp 1).mul (hp 2))).mul ((hp 0).inv (fun _ hz => hz))
  have hv : ContDiffOn ℝ n (fun z : Model =>
      (![z 0, z 1, z 2, (1+z 1*z 2)*(z 0)⁻¹] : Fin 4 → ℂ)) {z | z 0 ≠ 0} := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact hp 0
    · exact hp 1
    · exact hp 2
    · exact hr
  convert! assembleCLM.contDiff.comp_contDiffOn hv using 1

/-- The actual second rational inverse matrix is real-smooth to every order on its nonzero pivot domain. -/
theorem contDiffOn_matrixB (n : WithTop ℕ∞) :
    ContDiffOn ℝ n matrixB {z : Model | z 1 ≠ 0} := by
  have hp (i : Fin 3) : ContDiffOn ℝ n (fun z : Model => z i) {z : Model | z 1 ≠ 0} :=
    (contDiff_apply ℝ (fun _ : Fin 3 => ℂ) i).contDiffOn
  have hr : ContDiffOn ℝ n (fun z : Model => (z 0*z 2-1)*(z 1)⁻¹) {z | z 1 ≠ 0} :=
    (((hp 0).mul (hp 2)).sub contDiffOn_const).mul ((hp 1).inv (fun _ hz => hz))
  have hv : ContDiffOn ℝ n (fun z : Model =>
      (![z 0, z 1, (z 0*z 2-1)*(z 1)⁻¹, z 2] : Fin 4 → ℂ)) {z | z 1 ≠ 0} := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact hp 0
    · exact hp 1
    · exact hr
    · exact hp 2
  convert! assembleCLM.contDiff.comp_contDiffOn hv using 1

/-- The first continuous-linear extractor evaluates to the three literal matrix entries used by the first chart. -/
theorem coordinatesACLM_apply (A : Mat2) :
    coordinatesACLM A = ![A 0 0, A 0 1, A 1 0] := rfl

/-- The second continuous-linear extractor evaluates to the three literal matrix entries used by the second chart. -/
theorem coordinatesBCLM_apply (A : Mat2) :
    coordinatesBCLM A = ![A 0 0, A 0 1, A 1 1] := rfl

/-- The first intrinsic coordinates are continuous in the existing natural matrix-subtype topology. -/
theorem continuous_coordinatesA : Continuous coordinatesA :=
  coordinatesACLM.continuous.comp continuous_subtype_val

/-- The second intrinsic coordinates are continuous in the existing natural matrix-subtype topology. -/
theorem continuous_coordinatesB : Continuous coordinatesB :=
  coordinatesBCLM.continuous.comp continuous_subtype_val

/-- The total first inverse returns the rational determinant-one matrix on its target and the identity off that target. -/
def inverseA (z : Model) : SpecialLinearMatrix :=
  if hz : z 0 ≠ 0 then ⟨matrixA z, matrixA_det hz⟩ else ⟨1, Matrix.det_one⟩

/-- The total second inverse returns the rational determinant-one matrix on its target and the identity off that target. -/
def inverseB (z : Model) : SpecialLinearMatrix :=
  if hz : z 1 ≠ 0 then ⟨matrixB z, matrixB_det hz⟩ else ⟨1, Matrix.det_one⟩

private theorem inverseA_val {z : Model} (hz : z 0 ≠ 0) : (inverseA z).val = matrixA z := by
  simp only [inverseA, dite_eq_left hz]

private theorem inverseB_val {z : Model} (hz : z 1 ≠ 0) : (inverseB z).val = matrixB z := by
  simp only [inverseB, dite_eq_left hz]

private theorem continuousOn_inverseA : ContinuousOn inverseA {z : Model | z 0 ≠ 0} := by
  apply IsInducing.subtypeVal.continuousOn_iff.mpr
  apply (contDiffOn_matrixA 0).continuousOn.congr
  intro z hz
  exact inverseA_val hz

private theorem continuousOn_inverseB : ContinuousOn inverseB {z : Model | z 1 ≠ 0} := by
  apply IsInducing.subtypeVal.continuousOn_iff.mpr
  apply (contDiffOn_matrixB 0).continuousOn.congr
  intro z hz
  exact inverseB_val hz

/-- The first intrinsic chart is an actual open partial homeomorphism on the natural determinant-one matrix subtype, with nonzero upper-left pivot. -/
def chartA : OpenPartialHomeomorph SpecialLinearMatrix Model where
  toFun := coordinatesA
  invFun := inverseA
  source := {A | A.val 0 0 ≠ 0}
  target := {z | z 0 ≠ 0}
  map_source' := fun _ ha => ha
  map_target' := by
    intro z hz
    change (inverseA z).val 0 0 ≠ 0
    rw [inverseA_val hz]
    exact hz
  left_inv' := by
    intro A ha
    apply Subtype.ext
    rw [inverseA_val (show coordinatesA A 0 ≠ 0 from ha)]
    exact matrixA_coordinatesA A ha
  right_inv' := by
    intro z hz
    change coordinatesACLM (inverseA z).val = z
    rw [inverseA_val hz]
    ext i
    fin_cases i <;> simp [coordinatesACLM, matrixA]
  continuousOn_toFun := continuous_coordinatesA.continuousOn
  continuousOn_invFun := by exact continuousOn_inverseA
  open_source := by
    change IsOpen {A : SpecialLinearMatrix | coordinatesA A 0 ≠ 0}
    exact isOpen_ne.preimage ((continuous_apply 0).comp continuous_coordinatesA)
  open_target := isOpen_ne.preimage (continuous_apply 0)

/-- The second intrinsic chart is an actual open partial homeomorphism on the natural determinant-one matrix subtype, with nonzero upper-right pivot. -/
def chartB : OpenPartialHomeomorph SpecialLinearMatrix Model where
  toFun := coordinatesB
  invFun := inverseB
  source := {A | A.val 0 1 ≠ 0}
  target := {z | z 1 ≠ 0}
  map_source' := fun _ hb => hb
  map_target' := by
    intro z hz
    change (inverseB z).val 0 1 ≠ 0
    rw [inverseB_val hz]
    exact hz
  left_inv' := by
    intro A hb
    apply Subtype.ext
    rw [inverseB_val (show coordinatesB A 1 ≠ 0 from hb)]
    exact matrixB_coordinatesB A hb
  right_inv' := by
    intro z hz
    change coordinatesBCLM (inverseB z).val = z
    rw [inverseB_val hz]
    ext i
    fin_cases i <;> simp [coordinatesBCLM, matrixB]
  continuousOn_toFun := continuous_coordinatesB.continuousOn
  continuousOn_invFun := by exact continuousOn_inverseB
  open_source := by
    change IsOpen {A : SpecialLinearMatrix | coordinatesB A 1 ≠ 0}
    exact isOpen_ne.preimage ((continuous_apply 1).comp continuous_coordinatesB)
  open_target := isOpen_ne.preimage (continuous_apply 1)

/-- The first chart source consists exactly of determinant-one matrices with nonzero upper-left entry. -/
theorem chartA_source : chartA.source = {A : SpecialLinearMatrix | A.val 0 0 ≠ 0} := rfl

/-- The second chart source consists exactly of determinant-one matrices with nonzero upper-right entry. -/
theorem chartB_source : chartB.source = {A : SpecialLinearMatrix | A.val 0 1 ≠ 0} := rfl

/-- The first chart target is exactly the open set of three complex coordinates with nonzero first coordinate. -/
theorem chartA_target : chartA.target = {z : Model | z 0 ≠ 0} := rfl

/-- The second chart target is exactly the open set of three complex coordinates with nonzero second coordinate. -/
theorem chartB_target : chartB.target = {z : Model | z 1 ≠ 0} := rfl

/-- The actual first chart evaluates to its literal three-entry coordinate extractor. -/
theorem chartA_apply (A : SpecialLinearMatrix) : chartA A = coordinatesA A := rfl

/-- The actual second chart evaluates to its literal three-entry coordinate extractor. -/
theorem chartB_apply (A : SpecialLinearMatrix) : chartB A = coordinatesB A := rfl

/-- On the first chart target, the actual inverse chart has exactly the stated rational inverse matrix. -/
theorem chartA_symm_val {z : Model} (hz : z 0 ≠ 0) :
    (chartA.symm z).val = matrixA z := inverseA_val hz

/-- On the second chart target, the actual inverse chart has exactly the stated rational inverse matrix. -/
theorem chartB_symm_val {z : Model} (hz : z 1 ≠ 0) :
    (chartB.symm z).val = matrixB z := inverseB_val hz

/-- The two actual chart sources cover the entire determinant-one matrix subtype. -/
theorem chart_sources_cover : chartA.source ∪ chartB.source = Set.univ := by
  ext A
  simp only [mem_union, chartA_source, chartB_source, mem_ofPred_eq, mem_univ, iff_true]
  exact pivot_cover A

/-- The actual first chart inverse, viewed as an ambient matrix, is real-smooth to every order throughout its target. -/
theorem contDiffOn_chartA_symm_val (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun z => (chartA.symm z).val) chartA.target := by
  apply (contDiffOn_matrixA n).congr
  intro z hz
  exact chartA_symm_val hz

/-- The actual second chart inverse, viewed as an ambient matrix, is real-smooth to every order throughout its target. -/
theorem contDiffOn_chartB_symm_val (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun z => (chartB.symm z).val) chartB.target := by
  apply (contDiffOn_matrixB n).congr
  intro z hz
  exact chartB_symm_val hz

end FoliationQM.SpecialLinearCharts
