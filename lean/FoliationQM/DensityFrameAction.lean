module
public import FoliationQM.SpecialLinearGroupManifold
public import FoliationQM.DensityFrameManifold
public import FoliationQM.SmoothLocalDescent

/-!
# The actual smooth special linear action on polar density and frame data

Sources: the concrete determinant-one matrix factor in v13
`prop:takabayasi` and `eq:takabayasi_polar`. Left multiplication acts on
the actual angle-matrix representative by `(beta, A) ↦ (beta, g * A)`.
This map commutes with the independently defined simultaneous two-pi
shift and matrix negation, so it descends to the existing natural frame
sign quotient. The positive density is unchanged.

Identity, multiplication and both inverse laws use the actual inherited
matrix group. Joint smoothness of the representative action follows
from actual matrix multiplication. Joint smoothness of the quotient
action is then derived by descent through identity times the actual
smooth frame covering. The independent intrinsic factor and quotient
atlases are retained. Each fixed matrix therefore acts by a genuine
diffeomorphism, whose inverse is the action of the actual group inverse.
No spinor realization is used to define or infer this action, and no
abstract Spin identification, global individual representative, or
twisted-bundle structure is asserted here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.DensityFrameAction
open SourcePolarDatum SourcePolarProductQuotient PolarAmplitudeTopology SpinorMatrix

/-- The acting matrix group uses its independently established intrinsic six-dimensional real model. -/
abbrev groupModel := 𝓘(ℝ, SpecialLinearCharts.Model)

/-- The actual left matrix action on an angle-matrix representative, with its angle unchanged. -/
def datumAction (g : SpecialLinearMatrix) (p : FrameDatum) : FrameDatum :=
  (p.1, g * p.2)

/-- Actual left multiplication commutes with the literal simultaneous two-pi angle shift and matrix negation. -/
theorem datumAction_shift (g : SpecialLinearMatrix) (p : FrameDatum) :
    datumAction g (frameShift p) = frameShift (datumAction g p) := by
  apply Prod.ext
  · rfl
  apply Subtype.ext
  change (g : Mat2) * (-(p.2 : Mat2)) = -((g : Mat2) * (p.2 : Mat2))
  exact mul_neg _ _

/-- The actual left matrix action descends to the existing frame sign quotient using its independently proved relation. -/
def frameAction (g : SpecialLinearMatrix) : FrameQuotient → FrameQuotient :=
  Quotient.lift (fun p => Quotient.mk frameSetoid (datumAction g p)) (by
    intro p q hpq
    rcases hpq with h | h
    · rw [h]
    · rw [h, datumAction_shift]
      exact frame_mk_shift _)

/-- The quotient action sends an actual representative to the class of its literal left matrix product. -/
theorem frameAction_mk (g : SpecialLinearMatrix) (p : FrameDatum) :
    frameAction g (Quotient.mk frameSetoid p) =
      Quotient.mk frameSetoid (p.1, g * p.2) := rfl

/-- The actual density-frame action preserves density and acts by left multiplication on its frame sign class. -/
def productAction (g : SpecialLinearMatrix) (p : DensityFrameManifold.Product) :
    DensityFrameManifold.Product := (p.1, frameAction g p.2)

/-- On a density and actual frame representative, the product action is exactly the unchanged density and the class of the left matrix product. -/
theorem productAction_mk (g : SpecialLinearMatrix) (rho : PositiveDensity) (p : FrameDatum) :
    productAction g (rho, Quotient.mk frameSetoid p) =
      (rho, Quotient.mk frameSetoid (p.1, g * p.2)) := rfl

/-- The actual density-frame action preserves the positive-density coordinate exactly. -/
theorem productAction_density (g : SpecialLinearMatrix) (p : DensityFrameManifold.Product) :
    (productAction g p).1 = p.1 := rfl

/-- The actual identity matrix acts as the identity on every frame sign class. -/
theorem frameAction_one (q : FrameQuotient) :
    frameAction (1 : SpecialLinearMatrix) q = q := by
  induction q using Quotient.inductionOn with | h p =>
    rw [frameAction_mk, one_mul]

/-- Actual matrix multiplication acts by composition in the left-action order on the natural frame quotient. -/
theorem frameAction_mul (g h : SpecialLinearMatrix) (q : FrameQuotient) :
    frameAction (g * h) q = frameAction g (frameAction h q) := by
  induction q using Quotient.inductionOn with | h p =>
    simp only [frameAction_mk, mul_assoc]

/-- The actual identity matrix acts as the identity on the literal density-frame product. -/
theorem productAction_one (p : DensityFrameManifold.Product) :
    productAction (1 : SpecialLinearMatrix) p = p := by
  exact Prod.ext rfl (frameAction_one p.2)

/-- Actual matrix multiplication acts by composition in the left-action order on density-frame data. -/
theorem productAction_mul (g h : SpecialLinearMatrix) (p : DensityFrameManifold.Product) :
    productAction (g * h) p = productAction g (productAction h p) :=
  Prod.ext rfl (frameAction_mul g h p.2)

/-- Acting by the actual inverse after the matrix itself recovers every frame class. -/
theorem frameAction_inv_left (g : SpecialLinearMatrix) (q : FrameQuotient) :
    frameAction g⁻¹ (frameAction g q) = q := by
  rw [← frameAction_mul, inv_mul_cancel, frameAction_one]

/-- Acting by the matrix after its actual inverse recovers every frame class. -/
theorem frameAction_inv_right (g : SpecialLinearMatrix) (q : FrameQuotient) :
    frameAction g (frameAction g⁻¹ q) = q := by
  rw [← frameAction_mul, mul_inv_cancel, frameAction_one]

/-- Acting by the actual inverse after the matrix itself recovers all density-frame data. -/
theorem productAction_inv_left (g : SpecialLinearMatrix) (p : DensityFrameManifold.Product) :
    productAction g⁻¹ (productAction g p) = p :=
  Prod.ext rfl (frameAction_inv_left g p.2)

/-- Acting by the matrix after its actual inverse recovers all density-frame data. -/
theorem productAction_inv_right (g : SpecialLinearMatrix) (p : DensityFrameManifold.Product) :
    productAction g (productAction g⁻¹ p) = p :=
  Prod.ext rfl (frameAction_inv_right g p.2)

/-- The actual representative action is jointly smooth in the group element and angle-matrix datum for their intrinsic product atlases. -/
theorem contMDiff_datumAction (n : WithTop ℕ∞) :
    ContMDiff (groupModel.prod FrameDatumManifold.model) FrameDatumManifold.model n
      (fun p : SpecialLinearMatrix × FrameDatum => datumAction p.1 p.2) :=
  (contMDiff_fst.comp contMDiff_snd).prodMk
    ((SpecialLinearGroupManifold.contMDiff_mul n).comp
      (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)))

/-- The actual frame-quotient action is jointly smooth by descent through identity times the genuine smooth frame covering. -/
theorem contMDiff_frameAction (n : WithTop ℕ∞) :
    ContMDiff (groupModel.prod FrameQuotientManifold.model) FrameQuotientManifold.model n
      (fun p : SpecialLinearMatrix × FrameQuotient => frameAction p.1 p.2) := by
  have hc := SmoothLocalDescent.isLocalDiffeomorph_id_prodMap
    (P := groupModel) (X := SpecialLinearMatrix)
    (FrameQuotientManifold.quotient_mk_isLocalDiffeomorph n)
  have hs : Surjective (Prod.map (id : SpecialLinearMatrix → SpecialLinearMatrix)
      (Quotient.mk frameSetoid : FrameDatum → FrameQuotient)) := by
    rintro ⟨g, q⟩
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
    exact ⟨(g, p), rfl⟩
  apply (SmoothLocalDescent.contMDiff_comp_iff hc hs).mp
  exact (FrameQuotientManifold.contMDiff_quotient_mk n).comp (contMDiff_datumAction n)

/-- The actual density-frame action is jointly smooth in the group element and density-frame datum, with density unchanged. -/
theorem contMDiff_productAction (n : WithTop ℕ∞) :
    ContMDiff (groupModel.prod DensityFrameManifold.model) DensityFrameManifold.model n
      (fun p : SpecialLinearMatrix × DensityFrameManifold.Product => productAction p.1 p.2) :=
  (contMDiff_fst.comp contMDiff_snd).prodMk
    ((contMDiff_frameAction n).comp
      (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)))

/-- Each fixed actual determinant-one matrix acts as a genuine diffeomorphism of the intrinsic frame sign quotient. -/
def frameActionDiffeomorph (n : WithTop ℕ∞) (g : SpecialLinearMatrix) :
    Diffeomorph FrameQuotientManifold.model FrameQuotientManifold.model
      FrameQuotient FrameQuotient n where
  toFun := frameAction g
  invFun := frameAction g⁻¹
  left_inv := frameAction_inv_left g
  right_inv := frameAction_inv_right g
  contMDiff_toFun := (contMDiff_frameAction n).comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := (contMDiff_frameAction n).comp (contMDiff_const.prodMk contMDiff_id)

/-- Each fixed actual determinant-one matrix acts as a genuine density-preserving diffeomorphism of the intrinsic density-frame product. -/
def productActionDiffeomorph (n : WithTop ℕ∞) (g : SpecialLinearMatrix) :
    Diffeomorph DensityFrameManifold.model DensityFrameManifold.model
      DensityFrameManifold.Product DensityFrameManifold.Product n where
  toFun := productAction g
  invFun := productAction g⁻¹
  left_inv := productAction_inv_left g
  right_inv := productAction_inv_right g
  contMDiff_toFun := (contMDiff_productAction n).comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := (contMDiff_productAction n).comp (contMDiff_const.prodMk contMDiff_id)

/-- The fixed-matrix frame diffeomorphism is exactly the actual descended left action. -/
theorem frameActionDiffeomorph_apply (n : WithTop ℕ∞) (g : SpecialLinearMatrix) (q : FrameQuotient) :
    frameActionDiffeomorph n g q = frameAction g q := rfl

/-- The fixed-matrix density-frame diffeomorphism is exactly the actual left action. -/
theorem productActionDiffeomorph_apply (n : WithTop ℕ∞) (g : SpecialLinearMatrix)
    (p : DensityFrameManifold.Product) : productActionDiffeomorph n g p = productAction g p := rfl

/-- The inverse fixed-matrix density-frame diffeomorphism is exactly the action of the actual matrix-group inverse. -/
theorem productActionDiffeomorph_symm_apply (n : WithTop ℕ∞) (g : SpecialLinearMatrix)
    (p : DensityFrameManifold.Product) :
    (productActionDiffeomorph n g).symm p = productAction g⁻¹ p := rfl

end FoliationQM.DensityFrameAction
