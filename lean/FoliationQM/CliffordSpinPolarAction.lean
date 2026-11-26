module
public import FoliationQM.CliffordSpinPolarReconstruction
public import FoliationQM.SpinLorentzPolarCompatibility

/-!
# Actual smooth Clifford Spin action on polar classes and regular spinors

Source scope: the Spin frame action underlying v13 `prop:takabayasi`,
`eq:takabayasi_polar`, and `eq:tetrad_rotor_map`. Literal Clifford
multiplication acts on full-angle/Spin representatives while preserving
their angle. The genuine negative Clifford identity is central, so this
action respects the independently defined simultaneous sign relation and
descends to the natural frame quotient, with positive density unchanged.
Joint smoothness follows from actual Spin multiplication and descent
through the genuine smooth frame projection.

The regular-spinor action is defined directly by the universal Clifford
Dirac representation acting on the spinor. Actual Pauli compatibility
proves its smoothness and the exact agreement with independent polar
realization and inverse reconstruction. The actual frame Lorentz
projection and its action equivariance are also retained, with smooth
ambient matrix entries. No Lorentz target atlas, global individual polar
representative, spacetime Spin-bundle identification, or differentiated
field-equation covariance is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CliffordSpinPolarAction
open CliffordSpinMap CliffordSpinPolarDatum CliffordSpinPolarQuotient
open CliffordSpinPolarReconstruction PolarAmplitudeTopology PolarSignQuotient DiracMatrices

/-- The acting actual Clifford Spin group uses its compatible six-dimensional real model. -/
abbrev groupModel := 𝓘(ℝ, CliffordSpinManifold.Model)

/-- The actual Clifford negative identity commutes with every genuine Spin element. -/
theorem negativeOne_mul_comm (g : Spin) :
    CliffordSpinEquivalence.negativeOne * g = g * CliffordSpinEquivalence.negativeOne := by
  apply Subtype.ext
  change CliffordSpinEquivalence.negativeOne.val * g.val =
    g.val * CliffordSpinEquivalence.negativeOne.val
  rw [CliffordSpinEquivalence.negativeOne_coe]
  simp

/-- Actual Clifford multiplication acts on a full-angle/Spin representative with its angle unchanged. -/
def datumAction (g : Spin) (p : FrameDatum) : FrameDatum := (p.1, g * p.2)

/-- Actual left Clifford multiplication commutes with the literal simultaneous two-pi angle shift and negative Clifford identity. -/
theorem datumAction_shift (g : Spin) (p : FrameDatum) :
    datumAction g (frameShift p) = frameShift (datumAction g p) := by
  apply Prod.ext
  · rfl
  change g * (CliffordSpinEquivalence.negativeOne * p.2) =
    CliffordSpinEquivalence.negativeOne * (g * p.2)
  rw [← mul_assoc, ← negativeOne_mul_comm, mul_assoc]

/-- Actual left Clifford multiplication descends through the independently defined genuine frame sign relation. -/
def frameAction (g : Spin) : FrameQuotient → FrameQuotient :=
  Quotient.lift (fun p => Quotient.mk frameSetoid (datumAction g p)) (by
    intro p q hpq
    rcases hpq with h | h
    · rw [h]
    · rw [h, datumAction_shift]
      exact frame_mk_shift _)

/-- The genuine quotient action takes the class of a representative to the class of its literal left Clifford product. -/
theorem frameAction_mk (g : Spin) (p : FrameDatum) :
    frameAction g (Quotient.mk frameSetoid p) =
      Quotient.mk frameSetoid (p.1, g * p.2) := rfl

/-- The actual density/frame action keeps density fixed and acts on its actual Clifford frame class. -/
def productAction (g : Spin) (p : Product) : Product := (p.1, frameAction g p.2)

/-- On an actual representative, the genuine product action is exactly the unchanged density and the class of its left Clifford product. -/
theorem productAction_mk (g : Spin) (rho : PositiveDensity) (p : FrameDatum) :
    productAction g (rho, Quotient.mk frameSetoid p) =
      (rho, Quotient.mk frameSetoid (p.1, g * p.2)) := rfl

/-- Actual Clifford action preserves the positive-density coordinate exactly. -/
theorem productAction_density (g : Spin) (p : Product) : (productAction g p).1 = p.1 := rfl

/-- The actual Clifford identity fixes every genuine frame sign class. -/
theorem frameAction_one (q : FrameQuotient) : frameAction (1 : Spin) q = q := by
  induction q using Quotient.inductionOn with | h p =>
    rw [frameAction_mk, one_mul]

/-- Actual Clifford multiplication acts by composition in the left-action order on the genuine frame quotient. -/
theorem frameAction_mul (g h : Spin) (q : FrameQuotient) :
    frameAction (g * h) q = frameAction g (frameAction h q) := by
  induction q using Quotient.inductionOn with | h p =>
    simp only [frameAction_mk, mul_assoc]

/-- The actual Clifford identity fixes every density/frame datum. -/
theorem productAction_one (p : Product) : productAction (1 : Spin) p = p :=
  Prod.ext rfl (frameAction_one p.2)

/-- Actual Clifford multiplication acts by composition in the left-action order on the genuine density/frame product. -/
theorem productAction_mul (g h : Spin) (p : Product) :
    productAction (g * h) p = productAction g (productAction h p) :=
  Prod.ext rfl (frameAction_mul g h p.2)

/-- Acting by the genuine Clifford inverse after its element recovers every frame class. -/
theorem frameAction_inv_left (g : Spin) (q : FrameQuotient) :
    frameAction g⁻¹ (frameAction g q) = q := by
  rw [← frameAction_mul, inv_mul_cancel, frameAction_one]

/-- Acting by a genuine Clifford element after its inverse recovers every frame class. -/
theorem frameAction_inv_right (g : Spin) (q : FrameQuotient) :
    frameAction g (frameAction g⁻¹ q) = q := by
  rw [← frameAction_mul, mul_inv_cancel, frameAction_one]

/-- Acting by the genuine Clifford inverse after its element recovers every density/frame datum. -/
theorem productAction_inv_left (g : Spin) (p : Product) :
    productAction g⁻¹ (productAction g p) = p :=
  Prod.ext rfl (frameAction_inv_left g p.2)

/-- Acting by a genuine Clifford element after its inverse recovers every density/frame datum. -/
theorem productAction_inv_right (g : Spin) (p : Product) :
    productAction g (productAction g⁻¹ p) = p :=
  Prod.ext rfl (frameAction_inv_right g p.2)

/-- The independently defined genuine Clifford action intertwines the actual frame quotient identification with the established matrix quotient action. -/
theorem frameQuotientHomeomorph_action (g : Spin) (q : FrameQuotient) :
    frameQuotientHomeomorph (frameAction g q) =
      DensityFrameAction.frameAction (CliffordSpinMap.toMatrix g) (frameQuotientHomeomorph q) := by
  induction q using Quotient.inductionOn with | h p =>
    rw [frameAction_mk, frameQuotientHomeomorph_mk, frameQuotientHomeomorph_mk,
      DensityFrameAction.frameAction_mk]
    change Quotient.mk SourcePolarProductQuotient.frameSetoid
      (p.1, CliffordSpinMap.toMatrix (g * p.2)) = _
    rw [map_mul]
    rfl

/-- Actual Pauli product coordinates intertwine the independently defined genuine Clifford and matrix polar actions exactly. -/
theorem productMatrixDiffeomorph_action (n : WithTop ℕ∞) (g : Spin) (p : Product) :
    productMatrixDiffeomorph n (productAction g p) =
      DensityFrameAction.productAction (CliffordSpinMap.toMatrix g) (productMatrixDiffeomorph n p) :=
  Prod.ext rfl (frameQuotientHomeomorph_action g p.2)

/-- Actual Clifford multiplication is jointly smooth on full-angle/Spin representatives in their independent factor atlases. -/
theorem contMDiff_datumAction (n : WithTop ℕ∞) :
    ContMDiff (groupModel.prod frameModel) frameModel n
      (fun p : Spin × FrameDatum => datumAction p.1 p.2) :=
  (contMDiff_fst.comp contMDiff_snd).prodMk
    ((CliffordSpinManifold.contMDiff_mul n).comp
      (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)))

/-- The genuine Clifford frame quotient action is jointly smooth by descent through identity times the actual smooth frame covering. -/
theorem contMDiff_frameAction (n : WithTop ℕ∞) :
    ContMDiff (groupModel.prod CliffordSpinPolarManifold.model) CliffordSpinPolarManifold.model n
      (fun p : Spin × FrameQuotient => frameAction p.1 p.2) := by
  have hc := SmoothLocalDescent.isLocalDiffeomorph_id_prodMap
    (P := groupModel) (X := Spin) (CliffordSpinPolarManifold.quotient_mk_isLocalDiffeomorph n)
  have hs : Surjective (Prod.map (id : Spin → Spin)
      (Quotient.mk frameSetoid : FrameDatum → FrameQuotient)) := by
    rintro ⟨g, q⟩
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective q
    exact ⟨(g, p), rfl⟩
  apply (SmoothLocalDescent.contMDiff_comp_iff hc hs).mp
  exact (CliffordSpinPolarManifold.contMDiff_quotient_mk n).comp (contMDiff_datumAction n)

/-- Actual Clifford action is jointly smooth on the independently charted positive-density/frame product. -/
theorem contMDiff_productAction (n : WithTop ℕ∞) :
    ContMDiff (groupModel.prod model) model n (fun p : Spin × Product => productAction p.1 p.2) :=
  (contMDiff_fst.comp contMDiff_snd).prodMk
    ((contMDiff_frameAction n).comp
      (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)))

/-- Every fixed genuine Clifford Spin element acts by a density-preserving diffeomorphism, with its actual group inverse giving the inverse map. -/
def productActionDiffeomorph (n : WithTop ℕ∞) (g : Spin) :
    Diffeomorph model model Product Product n where
  toFun := productAction g
  invFun := productAction g⁻¹
  left_inv := productAction_inv_left g
  right_inv := productAction_inv_right g
  contMDiff_toFun := (contMDiff_productAction n).comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := (contMDiff_productAction n).comp (contMDiff_const.prodMk contMDiff_id)

/-- The universal Clifford Dirac representation preserves strict invariant regularity of every regular spinor. -/
theorem regular_dirac (g : Spin) {psi : Spinor} (hpsi : SpinorRegularity.Regular psi) :
    SpinorRegularity.Regular ((CliffordMinkowski.dirac g.val).mulVec psi) := by
  rw [CliffordSpinMap.dirac_eq_spin]
  exact RegularSpinorAction.regular_spin (CliffordSpinMap.toMatrix g) hpsi

/-- The actual Clifford action on a regular spinor is directly its universal Dirac matrix acting on the spinor. -/
def act (g : Spin) (q : RegularSpinor) : RegularSpinor :=
  ⟨(CliffordMinkowski.dirac g.val).mulVec q.val, regular_dirac g q.property⟩

/-- The genuine regular-spinor action has exactly the literal universal Dirac matrix-vector value. -/
theorem act_val (g : Spin) (q : RegularSpinor) :
    (act g q).val = (CliffordMinkowski.dirac g.val).mulVec q.val := rfl

/-- The direct actual Clifford spinor action agrees with the established matrix action through its genuine Pauli representative. -/
theorem act_eq_matrix (g : Spin) (q : RegularSpinor) :
    act g q = RegularSpinorAction.act (CliffordSpinMap.toMatrix g) q := by
  apply Subtype.ext
  rw [act_val, CliffordSpinMap.dirac_eq_spin]
  rfl

/-- The genuine Clifford identity acts as the identity on every regular spinor. -/
theorem act_one (q : RegularSpinor) : act (1 : Spin) q = q := by
  rw [act_eq_matrix, map_one, RegularSpinorAction.act_one]

/-- Actual Clifford multiplication acts by composition in the left-action order on regular spinors. -/
theorem act_mul (g h : Spin) (q : RegularSpinor) : act (g * h) q = act g (act h q) := by
  simp only [act_eq_matrix, map_mul, RegularSpinorAction.act_mul]

/-- Actual inverse Clifford action after its element recovers every regular spinor. -/
theorem act_inv_act (g : Spin) (q : RegularSpinor) : act g⁻¹ (act g q) = q := by
  rw [← act_mul, inv_mul_cancel, act_one]

/-- Actual Clifford action after its inverse recovers every regular spinor. -/
theorem act_act_inv (g : Spin) (q : RegularSpinor) : act g (act g⁻¹ q) = q := by
  rw [← act_mul, mul_inv_cancel, act_one]

/-- Actual universal Clifford Dirac action preserves the scalar-pseudoscalar invariant density exactly. -/
theorem invariantDensity_act (g : Spin) (q : RegularSpinor) :
    SpinorRegularity.invariantDensity (act g q).val = SpinorRegularity.invariantDensity q.val := by
  rw [act_eq_matrix]
  exact RegularSpinorAction.invariantDensity_act (CliffordSpinMap.toMatrix g) q

/-- The direct universal Clifford action is jointly smooth in the actual Spin and regular-spinor manifolds. -/
theorem contMDiff_act (n : WithTop ℕ∞) :
    ContMDiff (groupModel.prod 𝓘(ℝ, Spinor)) 𝓘(ℝ, Spinor) n
      (fun p : Spin × RegularSpinor => act p.1 p.2) := by
  have h := (RegularSpinorAction.contMDiff_act n).comp
    (((CliffordSpinManifold.contMDiff_toMatrix n).comp contMDiff_fst).prodMk contMDiff_snd)
  simpa only [Function.comp_def, act_eq_matrix] using h

/-- Every fixed genuine Clifford Spin element acts by a regular-spinor diffeomorphism, with its actual inverse giving the inverse action. -/
def actionDiffeomorph (n : WithTop ℕ∞) (g : Spin) :
    Diffeomorph 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) RegularSpinor RegularSpinor n where
  toFun := act g
  invFun := act g⁻¹
  left_inv := act_inv_act g
  right_inv := act_act_inv g
  contMDiff_toFun := (contMDiff_act n).comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := (contMDiff_act n).comp (contMDiff_const.prodMk contMDiff_id)

/-- Direct universal Clifford spinor action on every literal source representative equals its actual left Clifford frame product, preserving density and angle. -/
theorem act_realizeSource (g : Spin) (rho : PositiveDensity) (p : FrameDatum) :
    act g (CliffordSpinPolarRealization.realizeSource (rho, p)) =
      CliffordSpinPolarRealization.realizeSource (rho, p.1, g * p.2) := by
  rw [act_eq_matrix]
  change RegularSpinorAction.act (CliffordSpinMap.toMatrix g)
    (SourcePolarRealization.realizeSource (rho, frameHomeomorph p)) = _
  rw [RegularSpinorAction.act_realizeSource]
  change SourcePolarRealization.realizeSource
    (rho, p.1, CliffordSpinMap.toMatrix g * CliffordSpinMap.toMatrix p.2) =
      SourcePolarRealization.realizeSource (rho, p.1, CliffordSpinMap.toMatrix (g * p.2))
  rw [map_mul]

/-- The independently defined genuine Clifford quotient action realizes as the directly defined universal Dirac spinor action. -/
theorem realization_equivariant (g : Spin) (p : Product) :
    productRegularHomeomorph (productAction g p) = act g (productRegularHomeomorph p) := by
  rcases p with ⟨rho, q⟩
  induction q using Quotient.inductionOn with | h p =>
    rw [productAction_mk, productRegularHomeomorph_mk, productRegularHomeomorph_mk]
    exact (act_realizeSource g rho p).symm

/-- Actual inverse smooth polar reconstruction intertwines direct Clifford spinor action with the independently defined genuine frame quotient action. -/
theorem reconstruction_equivariant (g : Spin) (q : RegularSpinor) :
    productRegularHomeomorph.symm (act g q) = productAction g (productRegularHomeomorph.symm q) := by
  apply productRegularHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, realization_equivariant, Homeomorph.apply_symm_apply]

/-- The actual Clifford negative identity has trivial proper future Lorentz image. -/
theorem lorentz_negativeOne :
    CliffordSpinLorentz.lorentzHom CliffordSpinEquivalence.negativeOne = 1 :=
  (CliffordSpinLorentz.lorentzHom_eq_one_iff _).mpr (Or.inr rfl)

/-- Forgetting the full chiral angle projects an actual Clifford frame class to the physical proper future Lorentz homomorphism of its genuine Spin factor. -/
def frameLorentz : FrameQuotient → LorentzMatrixGroup.ProperFutureLorentz :=
  Quotient.lift (fun p : FrameDatum => CliffordSpinLorentz.lorentzHom p.2) (by
    intro p q hpq
    rcases hpq with h | h
    · rw [h]
    · rw [h]
      change CliffordSpinLorentz.lorentzHom (CliffordSpinEquivalence.negativeOne * q.2) = _
      rw [map_mul, lorentz_negativeOne, one_mul])

/-- The actual frame Lorentz projection is precisely the physical homomorphism of each genuine Clifford representative. -/
theorem frameLorentz_mk (p : FrameDatum) :
    frameLorentz (Quotient.mk frameSetoid p) = CliffordSpinLorentz.lorentzHom p.2 := rfl

/-- The independently defined actual Clifford frame projection agrees with the previously established matrix-frame projection through exact quotient coordinates. -/
theorem frameLorentz_eq_matrix (q : FrameQuotient) :
    frameLorentz q = SpinLorentzPolarCompatibility.frameLorentz (frameQuotientHomeomorph q) := by
  induction q using Quotient.inductionOn with | h p => rfl

/-- Actual Clifford action on the genuine chiral frame quotient projects to the correct ordered physical Lorentz multiplication. -/
theorem frameLorentz_action (g : Spin) (q : FrameQuotient) :
    frameLorentz (frameAction g q) = CliffordSpinLorentz.lorentzHom g * frameLorentz q := by
  induction q using Quotient.inductionOn with | h p =>
    exact CliffordSpinLorentz.lorentzHom.map_mul g p.2

/-- The actual physical Lorentz matrix entries of a genuine Clifford frame class are smooth for its independently specified seven-dimensional quotient atlas. -/
theorem contMDiff_frameLorentz_matrix (n : WithTop ℕ∞) :
    ContMDiff CliffordSpinPolarManifold.model 𝓘(ℝ, LorentzMatrixGroup.Mat4) n
      (fun q : FrameQuotient => LorentzMatrixGroup.matrix (frameLorentz q).val) := by
  have h := (SpinLorentzPolarCompatibility.contMDiff_frameLorentz_matrix n).comp
    (CliffordSpinPolarManifold.frameQuotientDiffeomorph n).contMDiff
  simpa only [Function.comp_def, frameLorentz_eq_matrix,
    CliffordSpinPolarManifold.frameQuotientDiffeomorph_apply] using h

/-- Actual Clifford polar realization recovers exactly the Lorentz projection of its genuine frame class, independently of density. -/
theorem regularLorentz_product (p : Product) :
    SpinLorentzPolarCompatibility.regularLorentz (productRegularHomeomorph p) = frameLorentz p.2 := by
  rcases p with ⟨rho, q⟩
  induction q using Quotient.inductionOn with | h p =>
    rw [productRegularHomeomorph_mk, frameLorentz_mk]
    exact SpinLorentzPolarCompatibility.regularLorentz_realizeSource (sourceHomeomorph (rho, p))

/-- Direct actual Clifford Dirac action transforms the recovered physical Lorentz frame by its genuine ordered Lorentz homomorphism. -/
theorem regularLorentz_action (g : Spin) (q : RegularSpinor) :
    SpinLorentzPolarCompatibility.regularLorentz (act g q) =
      CliffordSpinLorentz.lorentzHom g * SpinLorentzPolarCompatibility.regularLorentz q := by
  rw [act_eq_matrix]
  exact SpinLorentzPolarCompatibility.regularLorentz_action (CliffordSpinMap.toMatrix g) q

end FoliationQM.CliffordSpinPolarAction
