module
public import FoliationQM.SpinLorentzSurjective
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Natural locally compact topologies of the independent Lorentz groups

Source scope: the concrete spin-frame and Lorentz-group correspondence in
v13 `prop:takabayasi` and `eq:tetrad_rotor_map`. The special linear source is
the closed determinant-one locus in its actual finite-dimensional complex
matrix space. The independent Lorentz target is a closed subgroup of real
matrix units, and its proper future subgroup is closed by the previously
proved equivalence between future-cone preservation and time entry at least
one. These facts give natural local compactness, sigma compactness of the
source, and the usual Baire consequence for the target.

The inverse of every Lorentz matrix is its actual metric-signed transpose.
Its continuous inverse-pair graph proves that the inherited unit/subgroup
topology agrees with the actual closed matrix locus. The existing continuous
surjection additionally gives target path connectedness. No topology is
replaced by one from the represented image, and no covering result is used.
-/

@[expose] public section

noncomputable section
open Topology
namespace FoliationQM.LorentzMatrixTopology
open LorentzMatrixGroup SourcePolarDatum SpinorMatrix

/-- The actual determinant-one source is a closed subset of complex matrix space. -/
theorem isClosed_specialLinearMatrix : IsClosed {A : Mat2 | A.det = 1} :=
  isClosed_eq continuous_id.matrix_det continuous_const

/-- The natural determinant-one subtype is locally compact; the local ambient
instance is the existing finite-product matrix topology. -/
instance instLocallyCompactSpecialLinearMatrix : LocallyCompactSpace SpecialLinearMatrix := by
  let _ : LocallyCompactSpace Mat2 :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℂ))
  exact isClosed_specialLinearMatrix.locallyCompactSpace

/-- The actual special linear source is sigma compact as a closed matrix locus. -/
instance instSigmaCompactSpecialLinearMatrix : SigmaCompactSpace SpecialLinearMatrix := by
  let _ : SigmaCompactSpace Mat2 :=
    inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → ℂ))
  exact isClosed_specialLinearMatrix.sigmaCompactSpace

/-- The independent metric equation defines a closed subgroup of actual matrix units. -/
theorem isClosed_lorentzGroup : IsClosed (lorentzGroup : Set Mat4ˣ) := by
  apply isClosed_eq _ continuous_const
  exact (Units.continuous_val.matrix_transpose.mul continuous_const).mul Units.continuous_val

/-- The independent Lorentz group is locally compact in its existing unit-subgroup topology. -/
instance instLocallyCompactLorentz : LocallyCompactSpace Lorentz := by
  let _ : LocallyCompactSpace Mat4 :=
    inferInstanceAs (LocallyCompactSpace (Fin 4 → Fin 4 → ℝ))
  exact isClosed_lorentzGroup.locallyCompactSpace

/-- Within the independent Lorentz group, proper future membership is exactly
an actual determinant equation and a closed temporal-entry inequality. -/
theorem properFutureGroup_eq_closed_locus : (properFutureGroup : Set Lorentz) =
    {L | (matrix L).det = 1} ∩ {L | 1 ≤ matrix L 0 0} := by
  ext L
  change ((matrix L).det = 1 ∧ preservesFutureCone (matrix L)) ↔ _
  rw [LorentzFutureCone.preserves_futureCone_iff_time_ge_one (matrix L) (metric L)]
  rfl

/-- The independently defined proper future component is closed in the Lorentz group. -/
theorem isClosed_properFutureGroup : IsClosed (properFutureGroup : Set Lorentz) := by
  rw [properFutureGroup_eq_closed_locus]
  exact (isClosed_eq continuous_matrix.matrix_det continuous_const).inter
    (isClosed_le continuous_const ((continuous_apply 0).comp ((continuous_apply 0).comp continuous_matrix)))

/-- The actual proper future Lorentz group is locally compact; its inherited
Hausdorff topology therefore also gives the Baire property. -/
instance instLocallyCompactProperFutureLorentz : LocallyCompactSpace ProperFutureLorentz :=
  isClosed_properFutureGroup.locallyCompactSpace



/-- The actual proper future target is path connected by the proved continuous
surjection from the naturally path-connected special linear source. -/
instance instPathConnectedProperFutureLorentz : PathConnectedSpace ProperFutureLorentz :=
  SpinLorentzSurjective.properFutureHom_surjective.pathConnectedSpace
    SpinLorentzOrientation.continuous_properFutureHom


private theorem matrix_inverse_pair (L : Lorentz) :
    (L.val⁻¹).val = eta * (matrix L).transpose * eta :=
  (matrix_inv L).trans (inverse_formula_of_metric _ (metric L))

/-- The actual underlying matrix map embeds the natural Lorentz unit-subgroup
topology, because its inverse coordinate is the continuous signed transpose. -/
theorem isEmbedding_matrix : IsEmbedding matrix := by
  let g : Mat4 → Mat4 × Mat4ᵐᵒᵖ := fun M => (M, MulOpposite.op (eta*M.transpose*eta))
  have hg : Continuous g := by
    apply Continuous.prodMk continuous_id
    exact MulOpposite.continuous_op.comp
      ((continuous_const.mul continuous_id.matrix_transpose).mul continuous_const)
  have he : g ∘ matrix = Units.embedProduct Mat4 ∘ (fun L : Lorentz => L.val) := by
    funext L
    apply Prod.ext
    · rfl
    · exact congrArg MulOpposite.op (matrix_inverse_pair L).symm
  apply IsEmbedding.of_comp continuous_matrix hg
  rw [he]
  exact Units.isEmbedding_embedProduct.comp IsEmbedding.subtypeVal

/-- The underlying matrices of the independent Lorentz group are exactly the
actual solutions of its metric equation; invertibility is derived from that equation. -/
theorem range_matrix : Set.range matrix = {M : Mat4 | M.transpose*eta*M=eta} := by
  ext M
  constructor
  · rintro ⟨L,rfl⟩
    exact metric L
  · intro hm
    let U : Mat4ˣ := ⟨M,eta*M.transpose*eta,
      mul_eq_one_comm.mp (signedTranspose_mul_of_metric M hm),
      signedTranspose_mul_of_metric M hm⟩
    exact ⟨⟨U,hm⟩,rfl⟩

/-- The natural Lorentz group is a closed embedded subspace of actual real matrix space. -/
theorem isClosedEmbedding_matrix : IsClosedEmbedding matrix := by
  refine ⟨isEmbedding_matrix, ?_⟩
  rw [range_matrix]
  exact isClosed_eq
    ((continuous_id.matrix_transpose.mul continuous_const).mul continuous_id) continuous_const

/-- The independently defined proper future group is also closed embedded by its
actual matrix coordinates, with its existing subgroup topology. -/
theorem isClosedEmbedding_properMatrix :
    IsClosedEmbedding (fun L : ProperFutureLorentz => matrix L.val) :=
  isClosedEmbedding_matrix.comp isClosed_properFutureGroup.isClosedEmbedding_subtypeVal

end FoliationQM.LorentzMatrixTopology
