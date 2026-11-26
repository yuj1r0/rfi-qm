module
public import FoliationQM.CocycleGaugeTransform
public import FoliationQM.CocycleDensityGluing

/-!
# Compatible local smooth families under frame changes

Source: coordinate independence of the supplied-cocycle interpretation of
v13 `prop:takabayasi`. A supplied determinant-one matrix frame change is
smooth only on each actual open domain. Its genuine restriction is a bundled
smooth matrix field there. The actual chartwise polar and represented-spinor
actions preserve the independently stated compatibility relations for the
transformed cocycle G'_ij = h_j G_ij h_i⁻¹.

Actual inverse matrix actions give genuine bijections of compatible smooth
local families. They commute with the prior fiber realization and inverse
reconstruction, preserve local positive and bilinear invariant densities,
and preserve the previously constructed global glued density fields. No
regularity outside the chart domains or of a chosen chart index is required.
No covariance of a differentiated field equation, global individual polar
representative, or abstract spacetime Spin identification is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CocycleGaugeFamilies
open DiracMatrices PolarSignQuotient SourcePolarDatum SourcePolarProductQuotient
open CocyclePolarFields

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {ι : Type*} {n : WithTop ℕ∞}
  (D : PolarTransitionCocycle.Data I B ι n) (h : CocycleGaugeTransform.FrameChange D)

/-- The supplied frame change restricts to a genuine bundled smooth matrix field on each actual open domain, requiring no regularity outside that domain. -/
def localGauge (i : ι) : C^n⟮I, D.domain i; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯ :=
  ⟨fun x => h.value i x.val, fun x => contMDiffAt_subtype_iff.mpr
    ((h.smooth_value i).contMDiffAt ((D.domain i).isOpen.mem_nhds x.property))⟩

/-- The restricted smooth gauge field has the literal supplied matrix value at every local point. -/
theorem localGauge_apply (i : ι) (x : D.domain i) :
    localGauge D h i x = h.value i x.val := rfl

/-- Acting in each chart preserves polar compatibility for the genuinely transformed transition cocycle. -/
theorem polar_compatible {f : RawPolarFamily D} (hf : PolarCompatible D f) :
    PolarCompatible (CocycleGaugeTransform.transformed D h)
      (fun i => GaugePolarFields.polarGaugeEquiv (localGauge D h i) (f i)) := by
  intro i j x hi hj
  change DensityFrameAction.productAction (h.value j x) (f j ⟨x, hj⟩) =
    DensityFrameAction.productAction
      ((h.value j x * D.transition i j x) * (h.value i x)⁻¹)
      (DensityFrameAction.productAction (h.value i x) (f i ⟨x, hi⟩))
  rw [hf i j x hi hj]
  simp only [← DensityFrameAction.productAction_mul]
  congr 1
  simp [mul_assoc]

/-- The actual inverse matrix action reconstructs polar compatibility for the original cocycle from compatibility for its transformed cocycle. -/
theorem polar_inverse_compatible
    {f : RawPolarFamily (CocycleGaugeTransform.transformed D h)}
    (hf : PolarCompatible (CocycleGaugeTransform.transformed D h) f) :
    PolarCompatible D
      (fun i => (GaugePolarFields.polarGaugeEquiv (localGauge D h i)).symm (f i)) := by
  intro i j x hi hj
  change DensityFrameAction.productAction ((h.value j x)⁻¹) (f j ⟨x, hj⟩) =
    DensityFrameAction.productAction (D.transition i j x)
      (DensityFrameAction.productAction ((h.value i x)⁻¹) (f i ⟨x, hi⟩))
  rw [hf i j x hi hj]
  change DensityFrameAction.productAction ((h.value j x)⁻¹)
      (DensityFrameAction.productAction
        ((h.value j x * D.transition i j x) * (h.value i x)⁻¹) (f i ⟨x, hi⟩)) = _
  simp only [← DensityFrameAction.productAction_mul]
  congr 1
  simp [mul_assoc]

/-- Actual chartwise represented matrix action preserves the independently stated spinor compatibility for the transformed cocycle. -/
theorem spinor_compatible {f : RawSpinorFamily D} (hf : SpinorCompatible D f) :
    SpinorCompatible (CocycleGaugeTransform.transformed D h)
      (fun i => GaugePolarFields.spinorGaugeEquiv (localGauge D h i) (f i)) := by
  intro i j x hi hj
  change RegularSpinorAction.act (h.value j x) (f j ⟨x, hj⟩) =
    RegularSpinorAction.act ((h.value j x * D.transition i j x) * (h.value i x)⁻¹)
      (RegularSpinorAction.act (h.value i x) (f i ⟨x, hi⟩))
  rw [hf i j x hi hj]
  simp only [← RegularSpinorAction.act_mul]
  congr 1
  simp [mul_assoc]

/-- Actual represented inverse matrix action recovers the independently defined spinor compatibility for the original cocycle. -/
theorem spinor_inverse_compatible
    {f : RawSpinorFamily (CocycleGaugeTransform.transformed D h)}
    (hf : SpinorCompatible (CocycleGaugeTransform.transformed D h) f) :
    SpinorCompatible D
      (fun i => (GaugePolarFields.spinorGaugeEquiv (localGauge D h i)).symm (f i)) := by
  intro i j x hi hj
  change RegularSpinorAction.act ((h.value j x)⁻¹) (f j ⟨x, hj⟩) =
    RegularSpinorAction.act (D.transition i j x)
      (RegularSpinorAction.act ((h.value i x)⁻¹) (f i ⟨x, hi⟩))
  rw [hf i j x hi hj]
  change RegularSpinorAction.act ((h.value j x)⁻¹)
      (RegularSpinorAction.act
        ((h.value j x * D.transition i j x) * (h.value i x)⁻¹) (f i ⟨x, hi⟩)) = _
  simp only [← RegularSpinorAction.act_mul]
  congr 1
  simp [mul_assoc]

/-- Chartwise actual gauge action is a genuine bijection of compatible smooth polar families for the original and transformed cocycles. -/
def polarFamilyEquiv : SmoothPolarFamily D ≃
    SmoothPolarFamily (CocycleGaugeTransform.transformed D h) where
  toFun f := ⟨fun i => GaugePolarFields.polarGaugeEquiv (localGauge D h i) (f.val i),
    polar_compatible D h f.property⟩
  invFun f := ⟨fun i => (GaugePolarFields.polarGaugeEquiv (localGauge D h i)).symm (f.val i),
    polar_inverse_compatible D h f.property⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact (GaugePolarFields.polarGaugeEquiv (localGauge D h i)).symm_apply_apply (f.val i)
  right_inv f := by
    apply Subtype.ext
    funext i
    exact (GaugePolarFields.polarGaugeEquiv (localGauge D h i)).apply_symm_apply (f.val i)

/-- The actual represented matrix field similarly gives a genuine bijection of compatible smooth regular-spinor families. -/
def spinorFamilyEquiv : SmoothSpinorFamily D ≃
    SmoothSpinorFamily (CocycleGaugeTransform.transformed D h) where
  toFun f := ⟨fun i => GaugePolarFields.spinorGaugeEquiv (localGauge D h i) (f.val i),
    spinor_compatible D h f.property⟩
  invFun f := ⟨fun i => (GaugePolarFields.spinorGaugeEquiv (localGauge D h i)).symm (f.val i),
    spinor_inverse_compatible D h f.property⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact (GaugePolarFields.spinorGaugeEquiv (localGauge D h i)).symm_apply_apply (f.val i)
  right_inv f := by
    apply Subtype.ext
    funext i
    exact (GaugePolarFields.spinorGaugeEquiv (localGauge D h i)).apply_symm_apply (f.val i)

/-- Forward polar family transformation evaluates to the literal actual local matrix action. -/
theorem polarFamilyEquiv_apply (f : SmoothPolarFamily D) (i : ι) (x : D.domain i) :
    (polarFamilyEquiv D h f).val i x =
      DensityFrameAction.productAction (h.value i x.val) (f.val i x) := rfl

/-- Inverse polar family transformation evaluates to the actual inverse matrix action on the same open domain. -/
theorem polarFamilyEquiv_symm_apply
    (f : SmoothPolarFamily (CocycleGaugeTransform.transformed D h)) (i : ι) (x : D.domain i) :
    ((polarFamilyEquiv D h).symm f).val i x =
      DensityFrameAction.productAction ((h.value i x.val)⁻¹) (f.val i x) := rfl

/-- Forward spinor family transformation is the actual represented local matrix action. -/
theorem spinorFamilyEquiv_apply (f : SmoothSpinorFamily D) (i : ι) (x : D.domain i) :
    (spinorFamilyEquiv D h f).val i x =
      RegularSpinorAction.act (h.value i x.val) (f.val i x) := rfl

/-- Inverse spinor family transformation is the represented actual inverse local matrix action. -/
theorem spinorFamilyEquiv_symm_apply
    (f : SmoothSpinorFamily (CocycleGaugeTransform.transformed D h)) (i : ι) (x : D.domain i) :
    ((spinorFamilyEquiv D h).symm f).val i x =
      RegularSpinorAction.act ((h.value i x.val)⁻¹) (f.val i x) := rfl

/-- Actual family realization commutes with the chartwise frame change and its transformed cocycle. -/
theorem realization_commutes (f : SmoothPolarFamily D) :
    realizationEquiv (CocycleGaugeTransform.transformed D h) (polarFamilyEquiv D h f) =
      spinorFamilyEquiv D h (realizationEquiv D f) := by
  apply Subtype.ext
  funext i
  exact GaugePolarFields.realization_commutes (localGauge D h i) (f.val i)

/-- Actual inverse family reconstruction commutes with the same frame change. -/
theorem reconstruction_commutes (f : SmoothSpinorFamily D) :
    (realizationEquiv (CocycleGaugeTransform.transformed D h)).symm (spinorFamilyEquiv D h f) =
      polarFamilyEquiv D h ((realizationEquiv D).symm f) := by
  apply (realizationEquiv (CocycleGaugeTransform.transformed D h)).injective
  rw [Equiv.apply_symm_apply, realization_commutes, Equiv.apply_symm_apply]

/-- The actual positive-density coordinate is preserved by a possibly varying frame change in every available chart. -/
theorem polarFamilyEquiv_density (f : SmoothPolarFamily D) (i : ι) (x : D.domain i) :
    ((polarFamilyEquiv D h f).val i x).1 = (f.val i x).1 := rfl

/-- The actual original spinor bilinear invariant density is preserved by every local represented frame change. -/
theorem spinorFamilyEquiv_density (f : SmoothSpinorFamily D) (i : ι) (x : D.domain i) :
    SpinorRegularity.invariantDensity ((spinorFamilyEquiv D h f).val i x).val =
      SpinorRegularity.invariantDensity (f.val i x).val :=
  RegularSpinorAction.invariantDensity_act _ _


/-- The globally glued positive-density field is unchanged by the actual local frame change. -/
theorem polarDensity_eq (f : SmoothPolarFamily D) :
    CocycleDensityGluing.polarDensity (CocycleGaugeTransform.transformed D h)
      (polarFamilyEquiv D h f) = CocycleDensityGluing.polarDensity D f := rfl

/-- The globally glued actual spinor invariant density is independent of the local frame change, by its exact local values and uniqueness. -/
theorem spinorDensity_eq (f : SmoothSpinorFamily D) :
    CocycleDensityGluing.spinorDensity (CocycleGaugeTransform.transformed D h)
      (spinorFamilyEquiv D h f) = CocycleDensityGluing.spinorDensity D f := by
  symm
  apply CocycleDensityGluing.spinorDensity_unique
  intro i x
  rw [spinorFamilyEquiv_density]
  exact CocycleDensityGluing.spinorDensity_value_eq_local D f i x x.property

end FoliationQM.CocycleGaugeFamilies
