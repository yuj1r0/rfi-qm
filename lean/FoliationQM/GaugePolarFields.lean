module
public import FoliationQM.RegularSpinorAction
public import FoliationQM.DensityFrameFields

/-!
# Actual smooth matrix-field transformations of polar and spinor fields

Source: the fixed determinant-one representation in v13 `prop:takabayasi`.
A supplied smooth matrix field acts pointwise by the independently proved
intrinsic quotient and actual Dirac-matrix actions. Their joint smoothness
and genuine inverse group elements give bijections of bundled smooth fields.
The polar realization commutes with these actual transformations, and the
invariant density is unchanged. These statements supply coordinate-change
infrastructure; they assert no covariance of a differentiated field equation
and no abstract spin-bundle or variational identification.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
namespace FoliationQM.GaugePolarFields
open DiracMatrices PolarSignQuotient SourcePolarDatum SourcePolarProductQuotient

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

/-- The actual pointwise inverse of a supplied smooth determinant-one matrix field is a smooth matrix field. -/
def inverseGauge (g : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯) :
    C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯ :=
  ⟨fun x => (g x)⁻¹, (SpecialLinearGroupManifold.contMDiff_inv n).comp g.contMDiff⟩

/-- The smooth inverse field evaluates to the actual inverse group element at each point. -/
theorem inverseGauge_apply
    (g : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯) (x : M) :
    inverseGauge g x = (g x)⁻¹ := rfl

/-- The actual pointwise product of two supplied smooth determinant-one matrix fields is smooth. -/
def multiplyGauge
    (g h : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯) :
    C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯ :=
  ⟨fun x => g x * h x,
    (SpecialLinearGroupManifold.contMDiff_mul n).comp (g.contMDiff.prodMk h.contMDiff)⟩

/-- Pointwise multiplication of smooth matrix fields retains its actual matrix-group order. -/
theorem multiplyGauge_apply
    (g h : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯) (x : M) :
    multiplyGauge g h x = g x * h x := rfl

/-- A supplied smooth matrix field induces an actual bijection of density/frame-quotient smooth fields, with pointwise inverse-matrix action as inverse. -/
def polarGaugeEquiv
    (g : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯) :
    C^n⟮I, M; DensityFrameManifold.model, DensityFrameManifold.Product⟯ ≃
      C^n⟮I, M; DensityFrameManifold.model, DensityFrameManifold.Product⟯ where
  toFun f := ⟨fun x => DensityFrameAction.productAction (g x) (f x),
    (DensityFrameAction.contMDiff_productAction n).comp (g.contMDiff.prodMk f.contMDiff)⟩
  invFun f := ⟨fun x => DensityFrameAction.productAction ((g x)⁻¹) (f x),
    (DensityFrameAction.contMDiff_productAction n).comp
      ((inverseGauge g).contMDiff.prodMk f.contMDiff)⟩
  left_inv f := by
    apply ContMDiffMap.ext
    intro x
    change DensityFrameAction.productAction ((g x)⁻¹)
      (DensityFrameAction.productAction (g x) (f x)) = f x
    rw [← DensityFrameAction.productAction_mul, inv_mul_cancel,
      DensityFrameAction.productAction_one]
  right_inv f := by
    apply ContMDiffMap.ext
    intro x
    change DensityFrameAction.productAction (g x)
      (DensityFrameAction.productAction ((g x)⁻¹) (f x)) = f x
    rw [← DensityFrameAction.productAction_mul, mul_inv_cancel,
      DensityFrameAction.productAction_one]

/-- A supplied smooth matrix field induces an actual bijection of regular-spinor smooth fields through the independently defined Dirac-matrix action. -/
def spinorGaugeEquiv
    (g : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯) :
    C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯ ≃ C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯ where
  toFun f := ⟨fun x => RegularSpinorAction.act (g x) (f x), by
    have hp : ContMDiff I ((𝓘(ℝ, SpecialLinearCharts.Model)).prod 𝓘(ℝ, Spinor)) n
        (fun x => (g x, f x)) := g.contMDiff.prodMk f.contMDiff
    have h := (RegularSpinorAction.contMDiff_act n).comp hp
    simpa only [Function.comp_def] using h⟩
  invFun f := ⟨fun x => RegularSpinorAction.act ((g x)⁻¹) (f x), by
    have hp : ContMDiff I ((𝓘(ℝ, SpecialLinearCharts.Model)).prod 𝓘(ℝ, Spinor)) n
        (fun x => (inverseGauge g x, f x)) := (inverseGauge g).contMDiff.prodMk f.contMDiff
    have h := (RegularSpinorAction.contMDiff_act n).comp hp
    simpa only [Function.comp_def, inverseGauge_apply] using h⟩
  left_inv f := by
    apply ContMDiffMap.ext
    intro x
    exact RegularSpinorAction.act_inv_act (g x) (f x)
  right_inv f := by
    apply ContMDiffMap.ext
    intro x
    exact RegularSpinorAction.act_act_inv (g x) (f x)

/-- The density/frame field bijection acts pointwise by the literal matrix action on its quotient class. -/
theorem polarGaugeEquiv_apply
    (g : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, M; DensityFrameManifold.model, DensityFrameManifold.Product⟯) (x : M) :
    polarGaugeEquiv g f x = DensityFrameAction.productAction (g x) (f x) := rfl

/-- The inverse density/frame field bijection uses the actual inverse matrix field. -/
theorem polarGaugeEquiv_symm_apply
    (g : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, M; DensityFrameManifold.model, DensityFrameManifold.Product⟯) (x : M) :
    (polarGaugeEquiv g).symm f x = DensityFrameAction.productAction ((g x)⁻¹) (f x) := rfl

/-- The regular-spinor field bijection acts pointwise by the actual represented matrix. -/
theorem spinorGaugeEquiv_apply
    (g : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) (x : M) :
    spinorGaugeEquiv g f x = RegularSpinorAction.act (g x) (f x) := rfl

/-- The inverse regular-spinor field bijection acts pointwise by the represented inverse matrix. -/
theorem spinorGaugeEquiv_symm_apply
    (g : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) (x : M) :
    (spinorGaugeEquiv g).symm f x = RegularSpinorAction.act ((g x)⁻¹) (f x) := rfl

/-- Actual polar field realization commutes with any supplied smooth, possibly position-dependent determinant-one matrix transformation. -/
theorem realization_commutes
    (g : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, M; DensityFrameManifold.model, DensityFrameManifold.Product⟯) :
    DensityFrameFields.fieldEquiv n (polarGaugeEquiv g f) =
      spinorGaugeEquiv g (DensityFrameFields.fieldEquiv n f) := by
  apply ContMDiffMap.ext
  intro x
  exact RegularSpinorAction.realization_equivariant (g x) (f x)

/-- The actual positive-density coordinate is unchanged by any supplied smooth matrix-field transformation. -/
theorem polarGaugeEquiv_density
    (g : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, M; DensityFrameManifold.model, DensityFrameManifold.Product⟯) (x : M) :
    (polarGaugeEquiv g f x).1 = (f x).1 := rfl

/-- The actual bilinear invariant density of a regular-spinor field is unchanged by a supplied smooth matrix-field transformation. -/
theorem spinorGaugeEquiv_density
    (g : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) (x : M) :
    SpinorRegularity.invariantDensity (spinorGaugeEquiv g f x).val =
      SpinorRegularity.invariantDensity (f x).val :=
  RegularSpinorAction.invariantDensity_act (g x) (f x)

/-- Successive density/frame field transformations compose in the actual matrix multiplication order. -/
theorem polarGaugeEquiv_mul
    (g h : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, M; DensityFrameManifold.model, DensityFrameManifold.Product⟯) :
    polarGaugeEquiv (multiplyGauge g h) f = polarGaugeEquiv g (polarGaugeEquiv h f) := by
  apply ContMDiffMap.ext
  intro x
  exact DensityFrameAction.productAction_mul (g x) (h x) (f x)

/-- Successive actual spinor field transformations compose in the same matrix multiplication order. -/
theorem spinorGaugeEquiv_mul
    (g h : C^n⟮I, M; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, Spinor), RegularSpinor⟯) :
    spinorGaugeEquiv (multiplyGauge g h) f = spinorGaugeEquiv g (spinorGaugeEquiv h f) := by
  apply ContMDiffMap.ext
  intro x
  exact RegularSpinorAction.act_mul (g x) (h x) (f x)

end FoliationQM.GaugePolarFields
