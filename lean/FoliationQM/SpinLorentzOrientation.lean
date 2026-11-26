module
public import FoliationQM.SpinLorentzAction
public import FoliationQM.LorentzFutureCone
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Proper and future orientation of the actual spin-matrix action

Source scope: v13 `prop:takabayasi` and `eq:tetrad_rotor_map`, in the existing concrete
special-linear matrix representation. The natural determinant-one matrix space is path
connected through its two genuine rational charts and their explicit overlap. Continuity,
the independently proved Lorentz metric equation, and the value at the identity then force
the actual physical matrix determinant to be one. The independent future-cone criterion
and the proved time component refine the actual continuous Lorentz homomorphism into the
independently defined proper future subgroup.

The signed transpose relating physical columns and upper-gamma frame rows is explicit.
No orientation or determinant conclusion is supplied as a premise. This module does not
assert a kernel classification, surjectivity, a covering theorem, or an identification
with an abstract Clifford spin group.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.SpinLorentzOrientation
open SourcePolarDatum SpinorMatrix SpecialLinearCharts

/-- Each nonzero-pivot coordinate domain is path connected in its actual complex coordinate topology. -/
theorem isPathConnected_pivot (i : Fin 3) : IsPathConnected {z : Model | z i ≠ 0} := by
  have hc : IsPathConnected ({0}ᶜ : Set ℂ) :=
    isPathConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 0
  have he : {z : Model | z i ≠ 0} = Set.univ.pi
      (fun j : Fin 3 => if j = i then ({0}ᶜ : Set ℂ) else Set.univ) := by
    ext z
    simp only [mem_ofPred_eq, mem_pi, mem_univ, forall_const]
    constructor
    · intro hz j
      by_cases hj : j = i
      · subst j
        simpa using hz
      · simp [hj]
    · intro hz
      simpa using hz i
  rw [he]
  apply IsPathConnected.pi
  intro j
  split_ifs
  · exact hc
  · exact isPathConnected_univ

/-- The actual first rational chart source is path connected by the genuine continuous inverse chart. -/
theorem isPathConnected_chartA_source : IsPathConnected chartA.source := by
  rw [← chartA.symm_image_target_eq_source]
  exact (isPathConnected_pivot 0).image' chartA.continuousOn_symm

/-- The actual second rational chart source is likewise path connected in the original matrix subtype topology. -/
theorem isPathConnected_chartB_source : IsPathConnected chartB.source := by
  rw [← chartB.symm_image_target_eq_source]
  exact (isPathConnected_pivot 1).image' chartB.continuousOn_symm

/-- The two genuine rational chart sources overlap at an explicit determinant-one upper triangular matrix. -/
theorem chart_sources_overlap : (chartA.source ∩ chartB.source).Nonempty := by
  let A : SpecialLinearMatrix := ⟨!![1, 1; 0, 1], by norm_num [Matrix.det_fin_two]⟩
  refine ⟨A, ?_, ?_⟩
  · change (1 : ℂ) ≠ 0
    exact one_ne_zero
  · change (1 : ℂ) ≠ 0
    exact one_ne_zero

/-- The actual determinant-one complex matrix group is path connected: its two path-connected rational chart sources cover it and have genuine nonempty overlap. -/
instance instPathConnectedSpecialLinearMatrix : PathConnectedSpace SpecialLinearMatrix := by
  apply pathConnectedSpace_iff_univ.mpr
  rw [← chart_sources_cover]
  exact isPathConnected_chartA_source.union isPathConnected_chartB_source chart_sources_overlap

private theorem continuous_sq_one_eq_one {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (f : X → ℝ) (hf : Continuous f)
    (hsq : ∀ x, f x ^ 2 = 1) (x₀ : X) (h₀ : f x₀ = 1) (x : X) : f x = 1 := by
  rcases (sq_eq_one_iff.mp (hsq x)) with h | h
  · exact h
  · have hz : (0 : ℝ) ∈ Set.range f :=
      intermediate_value_univ x x₀ hf (by simp [h, h₀])
    obtain ⟨y, hy⟩ := hz
    have hs := hsq y
    rw [hy] at hs
    norm_num at hs

open SpinLorentzAction LorentzMatrixGroup

/-- The actual physical Lorentz matrix has determinant one for every determinant-one complex representative, derived from genuine connectedness, continuity, and the independent metric equation. -/
theorem lorentzMatrix_det (A : Mat2) (hA : A.det = 1) : (lorentzMatrix A).det = 1 := by
  let f : SpecialLinearMatrix → ℝ := fun B => (lorentzMatrix B.val).det
  have hf : Continuous f :=
    (continuous_lorentzMatrix.comp continuous_subtype_val).matrix_det
  have hs : ∀ B : SpecialLinearMatrix, f B ^ 2 = 1 :=
    fun B => det_sq_of_metric (lorentzMatrix B.val) (lorentzMatrix_metric B.val B.property)
  have h₁ : f 1 = 1 := by
    simp only [f, SpecialLinearGroupManifold.coe_one, lorentzMatrix_one, Matrix.det_one]
  exact continuous_sq_one_eq_one f hf hs 1 h₁ ⟨A, hA⟩

/-- Properness also holds for the source upper-gamma row-frame convention, with the two metric determinants and transpose accounted for explicitly. -/
theorem frameMatrix_det (A : Mat2) (hA : A.det = 1) :
    (SpecialLinearFrameLaws.frameMatrix A).det = 1 := by
  have hd := lorentzMatrix_det A hA
  simp only [lorentzMatrix, Matrix.det_mul, Matrix.det_transpose, eta_det] at hd
  nlinarith

/-- The already constructed Lorentz-valued homomorphism has determinant one at every actual special linear input. -/
theorem lorentzHom_det (A : SpecialLinearMatrix) : (matrix (lorentzHom A)).det = 1 := by
  rw [lorentzHom_matrix]
  exact lorentzMatrix_det A.val A.property

/-- The actual physical matrix preserves the independently specified future timelike cone, by its derived time component and the independently proved Lorentz cone criterion. -/
theorem lorentzMatrix_preservesFutureCone (A : Mat2) (hA : A.det = 1) :
    preservesFutureCone (lorentzMatrix A) :=
  (LorentzFutureCone.preserves_futureCone_iff_time_ge_one (lorentzMatrix A)
    (lorentzMatrix_metric A hA)).mpr (lorentzMatrix_time_ge_one A hA)

/-- Every actual special linear representative maps into the independently defined proper future Lorentz subgroup, without a supplied orientation premise. -/
theorem lorentzHom_mem_properFutureGroup (A : SpecialLinearMatrix) :
    lorentzHom A ∈ properFutureGroup := by
  change (matrix (lorentzHom A)).det = 1 ∧ preservesFutureCone (matrix (lorentzHom A))
  rw [lorentzHom_matrix]
  exact ⟨lorentzMatrix_det A.val A.property,
    lorentzMatrix_preservesFutureCone A.val A.property⟩

/-- The actual physical spin-matrix action refines to a genuine group homomorphism into the independently specified full proper future Lorentz target. -/
def properFutureHom : SpecialLinearMatrix →* ProperFutureLorentz where
  toFun A := ⟨lorentzHom A, lorentzHom_mem_properFutureGroup A⟩
  map_one' := Subtype.ext (lorentzHom.map_one)
  map_mul' A B := Subtype.ext (lorentzHom.map_mul A B)

/-- Forgetting proper-future membership recovers exactly the original actual Lorentz-valued homomorphism. -/
theorem properFutureHom_toLorentz (A : SpecialLinearMatrix) :
    (properFutureHom A).val = lorentzHom A := rfl

/-- The refined homomorphism retains exactly the physical signed-transpose matrix of the original Dirac sandwich. -/
theorem properFutureHom_matrix (A : SpecialLinearMatrix) :
    matrix (properFutureHom A).val = lorentzMatrix A.val := lorentzHom_matrix A

/-- The refined physical homomorphism is continuous for the natural special linear and independent Lorentz subgroup topologies. -/
theorem continuous_properFutureHom : Continuous properFutureHom :=
  continuous_lorentzHom.subtype_mk lorentzHom_mem_properFutureGroup

end FoliationQM.SpinLorentzOrientation
