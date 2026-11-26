module
public import FoliationQM.DensityFrameFields
public import FoliationQM.SpecialLinearSpin
public import FoliationQM.SpecialLinearGroupManifold
public import FoliationQM.DensityFrameAction

/-!
# The actual smooth determinant-one action on regular Dirac spinors

Sources: the concrete determinant-one representation in v13
`prop:takabayasi` and `eq:takabayasi_polar`. The action is defined directly
by the actual four-by-four Dirac matrix acting on the spinor. Its matrix
encoding is left multiplication by the determinant-one two-by-two
matrix, so the bilinear invariant density and strict regularity are
preserved. Actual matrix multiplication proves the group action laws.

Joint manifold smoothness follows from the independently verified
spinor matrix encoding and actual polynomial matrix multiplication.
Every fixed group element acts by a genuine diffeomorphism, with the
actual inverse matrix action as inverse. These statements use the
existing intrinsic group and regular-spinor atlases.

The density-frame action is separately defined by left multiplication
on quotient representatives. Its agreement with the actual spinor
action is proved from the concrete encoded polar expression, followed
by quotient descent. The inverse reconstruction is therefore equivariant
as well, with invariant density unchanged and the recovered frame class
transforming by the actual quotient action. No action is defined by
conjugating a realization equivalence, and no abstract Spin or twisted
bundle identification is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology Function
namespace FoliationQM.RegularSpinorAction
open DiracMatrices SpinorMatrix SpinorRegularity SpecialLinearSpin
open PolarSignQuotient SourcePolarDatum

/-- The actual determinant-one Dirac matrix action preserves the bilinear invariant density of every spinor, by its genuine determinant encoding. -/
theorem invariantDensity_spin (g : SpecialLinearMatrix) (psi : Spinor) :
    invariantDensity ((spin g).mulVec psi) = invariantDensity psi := by
  rw [← norm_det_toMatrix, spin_action, Matrix.det_mul, g.property, one_mul, norm_det_toMatrix]

/-- The actual determinant-one Dirac matrix action preserves strict invariant regularity. -/
theorem regular_spin (g : SpecialLinearMatrix) {psi : Spinor} (hpsi : Regular psi) :
    Regular ((spin g).mulVec psi) := by
  simpa only [Regular, invariantDensity_spin] using hpsi

/-- The actual regular-spinor action is direct multiplication by the concrete four-by-four Dirac spin matrix. -/
def act (g : SpecialLinearMatrix) (q : RegularSpinor) : RegularSpinor :=
  ⟨(spin g).mulVec q.val, regular_spin g q.property⟩

/-- The underlying spinor of the regular action is exactly the actual Dirac matrix-vector product. -/
theorem act_val (g : SpecialLinearMatrix) (q : RegularSpinor) :
    (act g q).val = (spin g).mulVec q.val := rfl

/-- The actual spinor action encodes as left multiplication by the actual determinant-one two-by-two matrix. -/
theorem toMatrix_act (g : SpecialLinearMatrix) (q : RegularSpinor) :
    toMatrix (act g q).val = (g : Mat2) * toMatrix q.val := spin_action g q.val

/-- The directly defined matrix-vector action also equals the inverse encoding of the actual left matrix product. -/
theorem act_val_eq_ofMatrix (g : SpecialLinearMatrix) (q : RegularSpinor) :
    (act g q).val = ofMatrix ((g : Mat2) * toMatrix q.val) := by
  rw [← toMatrix_act, ofMatrix_toMatrix]

/-- The actual regular-spinor action preserves the actual bilinear invariant density exactly. -/
theorem invariantDensity_act (g : SpecialLinearMatrix) (q : RegularSpinor) :
    invariantDensity (act g q).val = invariantDensity q.val := invariantDensity_spin g q.val

/-- The actual action is jointly manifold-smooth in the intrinsic determinant-one group and strict regular spinor, independently through polynomial matrix coordinates. -/
theorem contMDiff_act (n : WithTop ℕ∞) :
    ContMDiff ((𝓘(ℝ, SpecialLinearCharts.Model)).prod 𝓘(ℝ, Spinor)) 𝓘(ℝ, Spinor) n
      (fun p : SpecialLinearMatrix × RegularSpinor => act p.1 p.2) := by
  apply ContMDiff.of_comp_isOpenEmbedding RegularSpinorManifold.isOpenEmbedding_value
  have hpoly : ContDiff ℝ n (fun z : Mat2 × Spinor => ofMatrix (z.1 * toMatrix z.2)) :=
    (SpinorMatrixSmooth.contDiff_ofMatrix n).comp
      (contDiff_fst.mul ((SpinorMatrixSmooth.contDiff_toMatrix n).comp contDiff_snd))
  have hm := hpoly.contMDiff.comp
    (((SpecialLinearManifold.contMDiff_value n).comp contMDiff_fst).prodMk_space
      ((RegularSpinorManifold.contMDiff_value n).comp contMDiff_snd))
  simpa only [Function.comp_def, act_val_eq_ofMatrix] using hm

/-- The actual group identity acts as the identity on every strict regular spinor. -/
theorem act_one (q : RegularSpinor) : act (1 : SpecialLinearMatrix) q = q := by
  apply Subtype.ext
  change (spin (1 : Mat2)).mulVec q.val = q.val
  rw [spin_one, Matrix.one_mulVec]

/-- The actual matrix product acts by composition in the left-action order. -/
theorem act_mul (g h : SpecialLinearMatrix) (q : RegularSpinor) :
    act (g * h) q = act g (act h q) := by
  apply Subtype.ext
  change (spin ((g : Mat2) * (h : Mat2))).mulVec q.val =
    (spin g).mulVec ((spin h).mulVec q.val)
  rw [spin_mul, Matrix.mulVec_mulVec]

/-- Acting by the actual inverse after the matrix itself recovers every strict regular spinor. -/
theorem act_inv_act (g : SpecialLinearMatrix) (q : RegularSpinor) :
    act g⁻¹ (act g q) = q := by
  rw [← act_mul, inv_mul_cancel, act_one]

/-- Acting by the matrix after its actual inverse recovers every strict regular spinor. -/
theorem act_act_inv (g : SpecialLinearMatrix) (q : RegularSpinor) :
    act g (act g⁻¹ q) = q := by
  rw [← act_mul, mul_inv_cancel, act_one]

/-- The directly defined Dirac matrix action gives a genuine action of the actual determinant-one matrix group on strict regular spinors. -/
instance instMulActionRegularSpinor : MulAction SpecialLinearMatrix RegularSpinor where
  smul := act
  one_smul := act_one
  mul_smul := act_mul

/-- Each fixed actual determinant-one matrix acts smoothly on the strict regular-spinor manifold. -/
theorem contMDiff_act_fixed (n : WithTop ℕ∞) (g : SpecialLinearMatrix) :
    ContMDiff 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) n (act g) := by
  have hg : ContMDiff 𝓘(ℝ, Spinor) 𝓘(ℝ, SpecialLinearCharts.Model) n
      (fun _ : RegularSpinor => g) := contMDiff_const
  have hi : ContMDiff 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) n
      (fun q : RegularSpinor => q) := contMDiff_id
  have hp := hg.prodMk hi
  simpa only [Function.comp_def] using (contMDiff_act n).comp hp

/-- Each actual determinant-one matrix acts by a genuine regular-spinor diffeomorphism, with inverse given by the actual inverse matrix action. -/
def actionDiffeomorph (n : WithTop ℕ∞) (g : SpecialLinearMatrix) :
    Diffeomorph 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) RegularSpinor RegularSpinor n where
  toFun := act g
  invFun := act g⁻¹
  left_inv := act_inv_act g
  right_inv := act_act_inv g
  contMDiff_toFun := contMDiff_act_fixed n g
  contMDiff_invFun := contMDiff_act_fixed n g⁻¹

/-- The fixed-matrix diffeomorphism is exactly the directly defined Dirac matrix action. -/
theorem actionDiffeomorph_apply (n : WithTop ℕ∞) (g : SpecialLinearMatrix) (q : RegularSpinor) :
    actionDiffeomorph n g q = act g q := rfl

/-- The inverse fixed-matrix diffeomorphism is exactly the directly defined action of the actual inverse group matrix. -/
theorem actionDiffeomorph_symm_apply (n : WithTop ℕ∞) (g : SpecialLinearMatrix) (q : RegularSpinor) :
    (actionDiffeomorph n g).symm q = act g⁻¹ q := rfl

/-- Actual Dirac matrix action on the encoded polar spinor is the literal left matrix product with its complex amplitude unchanged. -/
theorem spin_parameterSpinor (g : SpecialLinearMatrix) (t : ℂ) (A : Mat2) :
    (spin g).mulVec (PolarMatrixFibers.parameterSpinor t A) =
      PolarMatrixFibers.parameterSpinor t ((g : Mat2) * A) := by
  apply toMatrix_injective
  rw [spin_action, PolarMatrixFibers.toMatrix_parameterSpinor,
    PolarMatrixFibers.toMatrix_parameterSpinor, Matrix.mul_smul]

/-- Actual action on each literal density-angle-matrix representative agrees with left multiplication of its determinant-one matrix and leaves density and angle unchanged. -/
theorem act_realizeSource (g : SpecialLinearMatrix)
    (rho : PolarAmplitudeTopology.PositiveDensity) (p : SourcePolarProductQuotient.FrameDatum) :
    act g (SourcePolarRealization.realizeSource (rho, p)) =
      SourcePolarRealization.realizeSource (rho, p.1, g * p.2) := by
  apply Subtype.ext
  change (spin g).mulVec (SourcePolarRealization.realizeSource (rho, p)).val = _
  simp only [SourcePolarRealization.realizeSource_parameterSpinor, spin_parameterSpinor]
  rfl

/-- The independently defined density-frame quotient action realizes as the directly defined Dirac matrix action on strict regular spinors. -/
theorem realization_equivariant (g : SpecialLinearMatrix) (p : DensityFrameManifold.Product) :
    SourcePolarProductQuotient.productRegularHomeomorph (DensityFrameAction.productAction g p) =
      act g (SourcePolarProductQuotient.productRegularHomeomorph p) := by
  rcases p with ⟨rho, q⟩
  induction q using Quotient.inductionOn with
  | h p =>
    rw [DensityFrameAction.productAction_mk,
      SourcePolarProductQuotient.productRegularHomeomorph_mk,
      SourcePolarProductQuotient.productRegularHomeomorph_mk]
    exact (act_realizeSource g rho p).symm

/-- The actual inverse density-frame reconstruction intertwines the direct spinor action with the independently defined quotient action. -/
theorem reconstruction_equivariant (g : SpecialLinearMatrix) (q : RegularSpinor) :
    SourcePolarProductQuotient.productRegularHomeomorph.symm (act g q) =
      DensityFrameAction.productAction g (SourcePolarProductQuotient.productRegularHomeomorph.symm q) := by
  apply SourcePolarProductQuotient.productRegularHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, realization_equivariant, Homeomorph.apply_symm_apply]

/-- The positive-density coordinate recovered from the acted spinor is exactly the original recovered positive density. -/
theorem density_act (g : SpecialLinearMatrix) (q : RegularSpinor) :
    DensityFrameFields.density (act g q) = DensityFrameFields.density q := by
  apply Subtype.ext
  simp only [DensityFrameFields.density_value_eq_invariantDensity, invariantDensity_act]

/-- The frame class recovered from the acted spinor is exactly the actual left action on its original recovered frame class. -/
theorem frameClass_act (g : SpecialLinearMatrix) (q : RegularSpinor) :
    DensityFrameFields.frameClass (act g q) =
      DensityFrameAction.frameAction g (DensityFrameFields.frameClass q) :=
  congrArg Prod.snd (reconstruction_equivariant g q)

end FoliationQM.RegularSpinorAction
