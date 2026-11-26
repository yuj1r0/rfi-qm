module
public import FoliationQM.LorentzMatrixTopology
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Independent proper Lorentz matrix domains for Cayley coordinates

Source scope: the real Lorentz-frame component of v13 `prop:takabayasi`.
The proper future component is an open subset of the independently defined
Lorentz group, because metric preservation forces determinant square one
and future orientation is the strict temporal-entry inequality. The
existing natural subgroup topology agrees with the literal real-matrix
locus. The nonsingular M+1 domain contains the identity, and its left
translates cover the whole proper future group.

These are independent matrix and topological facts. No Spin lift, quotient
atlas, smoothness convention, or simple-connectivity premise is used to
define the domains or matrix reconstruction.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Set Topology
namespace FoliationQM.LorentzCayleyDomain
open LorentzMatrixGroup

/-- Positive determinant within the independently defined Lorentz group is exactly determinant one. -/
theorem det_pos_iff (L : Lorentz) : 0 < (matrix L).det ↔ (matrix L).det = 1 := by
  have h := det_sq_of_metric (matrix L) (metric L)
  constructor
  · intro hp
    rcases sq_eq_one_iff.mp h with h | h
    · exact h
    · rw [h] at hp
      norm_num at hp
  · intro h
    rw [h]
    norm_num

/-- The proper future subgroup is the intersection of the two strict matrix-coordinate orientation conditions. -/
theorem properFutureGroup_eq_open_locus : (properFutureGroup : Set Lorentz) =
    {L | 0 < (matrix L).det} ∩ {L | 0 < matrix L 0 0} := by
  ext L
  change ((matrix L).det = 1 ∧ preservesFutureCone (matrix L)) ↔ _
  rw [LorentzFutureCone.preserves_futureCone_iff_time_pos (matrix L) (metric L)]
  exact and_congr (det_pos_iff L).symm Iff.rfl

/-- The actual proper future component is open in the existing full Lorentz group topology. -/
theorem isOpen_properFutureGroup : IsOpen (properFutureGroup : Set Lorentz) := by
  rw [properFutureGroup_eq_open_locus]
  exact (isOpen_lt continuous_const continuous_matrix.matrix_det).inter
    (isOpen_lt continuous_const
      ((continuous_apply 0).comp ((continuous_apply 0).comp continuous_matrix)))

/-- Inclusion of the actual proper future component into the full Lorentz group is an open embedding. -/
theorem isOpenEmbedding_inclusion :
    IsOpenEmbedding (fun L : ProperFutureLorentz => L.val) :=
  isOpen_properFutureGroup.isOpenEmbedding_subtypeVal

/-- Literal metric-preserving real matrices with determinant one and positive temporal entry. -/
abbrev MatrixLocus := {M : Mat4 // M.transpose * eta * M = eta ∧ M.det = 1 ∧ 0 < M 0 0}

/-- Construct the actual proper future group element from the independent matrix equations; invertibility and cone preservation are derived. -/
def ofMatrix (M : Mat4) (hm : M.transpose * eta * M = eta)
    (hd : M.det = 1) (ht : 0 < M 0 0) : ProperFutureLorentz :=
  ⟨⟨⟨M, eta * M.transpose * eta,
    mul_eq_one_comm.mp (signedTranspose_mul_of_metric M hm),
    signedTranspose_mul_of_metric M hm⟩, hm⟩,
    hd, (LorentzFutureCone.preserves_futureCone_iff_time_pos M hm).mpr ht⟩

/-- Matrix reconstruction retains the exact original matrix entries. -/
theorem matrix_ofMatrix (M : Mat4) (hm : M.transpose * eta * M = eta)
    (hd : M.det = 1) (ht : 0 < M 0 0) : matrix (ofMatrix M hm hd ht).val = M := rfl

/-- The temporal entry of every actual proper future Lorentz matrix is positive. -/
theorem time_pos (L : ProperFutureLorentz) : 0 < matrix L.val 0 0 :=
  (LorentzFutureCone.preserves_futureCone_iff_time_pos _ (metric L.val)).mp L.property.2

/-- The literal real-matrix locus and the actual proper future group have the same natural topology. -/
def matrixHomeomorph : ProperFutureLorentz ≃ₜ MatrixLocus where
  toFun L := ⟨matrix L.val, metric L.val, L.property.1, time_pos L⟩
  invFun M := ofMatrix M.val M.property.1 M.property.2.1 M.property.2.2
  left_inv L := by
    apply Subtype.ext
    apply matrix_injective
    rfl
  right_inv M := by
    apply Subtype.ext
    rfl
  continuous_toFun :=
    (continuous_matrix.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply LorentzMatrixTopology.isClosedEmbedding_properMatrix.isEmbedding.isInducing.continuous_iff.mpr
    exact continuous_subtype_val

/-- The matrix-locus homeomorphism reads exactly the original real matrix. -/
theorem matrixHomeomorph_apply (L : ProperFutureLorentz) :
    (matrixHomeomorph L).val = matrix L.val := rfl

/-- The inverse matrix-locus homeomorphism reconstructs precisely the displayed real matrix. -/
theorem matrixHomeomorph_symm_apply (M : MatrixLocus) :
    matrix (matrixHomeomorph.symm M).val = M.val := rfl

/-- The independent Cayley chart source is the nonsingular M+1 locus in the actual proper future group. -/
def source : Set ProperFutureLorentz := {L | (matrix L.val + 1).det ≠ 0}

/-- The Cayley source is equivalently the domain where the actual matrix denominator is a unit. -/
theorem mem_source_iff (L : ProperFutureLorentz) :
    L ∈ source ↔ IsUnit (matrix L.val + 1) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rfl

/-- The actual Cayley source is open in the unchanged Lorentz subgroup topology. -/
theorem isOpen_source : IsOpen source :=
  isOpen_ne_fun ((continuous_matrix.comp continuous_subtype_val).add continuous_const).matrix_det
    continuous_const

/-- The identity lies in the nonsingular Cayley source, so the chart domain is nonempty. -/
theorem one_mem_source : (1 : ProperFutureLorentz) ∈ source := by
  change ((1 : Mat4) + 1).det ≠ 0
  have he : (1 : Mat4) + 1 = (2 : ℝ) • (1 : Mat4) := by simp [two_smul]
  rw [he, Matrix.det_smul]
  norm_num

/-- The translated Cayley domain around a prescribed Lorentz element is specified by its actual relative group matrix. -/
def translatedSource (L : ProperFutureLorentz) : Set ProperFutureLorentz :=
  {K | L⁻¹ * K ∈ source}

/-- Every translated Cayley domain is open in the original proper future group topology. -/
theorem isOpen_translatedSource (L : ProperFutureLorentz) : IsOpen (translatedSource L) :=
  isOpen_source.preimage (continuous_const.mul continuous_id)

/-- Each Lorentz element belongs to its own translated Cayley domain. -/
theorem mem_translatedSource (L : ProperFutureLorentz) : L ∈ translatedSource L := by
  change L⁻¹ * L ∈ source
  simpa using one_mem_source

/-- The actual translated matrix Cayley domains cover the whole proper future Lorentz group. -/
theorem translatedSource_cover : (⋃ L : ProperFutureLorentz, translatedSource L) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro L
  exact Set.mem_iUnion.mpr ⟨L, mem_translatedSource L⟩

end FoliationQM.LorentzCayleyDomain
