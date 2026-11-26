module
public import FoliationQM.CocycleBundleDensity
public import FoliationQM.CocyclePullbackSections

/-!
# Actual section density and its independently glued local description

Source: the positive invariant density in the supplied-cocycle section
interpretation of v13 `prop:takabayasi`. Each independently graph-smooth
polar or represented-spinor section gives a bundled positive-density field
by genuine composition with the actual smooth total-space density map.

Actual chart identities prove agreement with every available local-family
density and with the earlier independently glued density field. Agreement
with the original local values determines the field uniquely, even among
arbitrary competing positive-density maps. Actual realization, local frame
changes, and smooth base pullback preserve these identities as equalities
of bundled smooth fields. The real represented density remains the original
scalar-pseudoscalar bilinear invariant. No smooth selection of chart indices,
global individual frame, or abstract spacetime Spin identification is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CocycleSectionDensity
open DiracMatrices PolarSignQuotient PolarAmplitudeTopology SourcePolarProductQuotient
open PolarTransitionCocycle PolarCocycleBundles PolarCocycleSections

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  (D : Data I B ι n) [IsManifold I n B]

/-- An actual graph-smooth polar section has a bundled smooth positive-density field obtained by composing its genuine total graph with the actual smooth total density. -/
def polarDensityField (s : PolarSection D) : C^n⟮I, B; 𝓘(ℝ, ℝ), PositiveDensity⟯ :=
  ⟨fun x => CocycleBundleDensity.polarDensity D (⟨x, s.val x⟩ : PolarTotal D),
    (CocycleBundleDensity.contMDiff_polarDensity D).comp s.property⟩

/-- A graph-smooth represented-spinor section gives a bundled positive-density field by composition of its actual total graph with the actual smooth total density. -/
def spinorDensityField (s : SpinorSection D) : C^n⟮I, B; 𝓘(ℝ, ℝ), PositiveDensity⟯ :=
  ⟨fun x => CocycleBundleDensity.spinorDensity D (⟨x, s.val x⟩ : SpinorTotal D),
    (CocycleBundleDensity.contMDiff_spinorDensity D).comp s.property⟩

/-- The composed polar section density has exactly its actual selected-fiber positive-density value. -/
theorem polarDensityField_apply (s : PolarSection D) (x : B) :
    polarDensityField D s x = (s.val x).1 := rfl

/-- The composed represented-spinor density is actual positive-density recovery from the original section fiber. -/
theorem spinorDensityField_apply (s : SpinorSection D) (x : B) :
    spinorDensityField D s x = DensityFrameFields.density (s.val x) := rfl

/-- The real scalar value of the composed spinor density is exactly the original scalar-pseudoscalar bilinear invariant density. -/
theorem spinorDensityField_value (s : SpinorSection D) (x : B) :
    (spinorDensityField D s x : ℝ) = SpinorRegularity.invariantDensity (s.val x).val :=
  CocycleBundleDensity.spinorDensity_value D (⟨x, s.val x⟩ : SpinorTotal D)

/-- The actual composed section density agrees with every available local polar-family density, independently of the chosen chart index. -/
theorem polarDensityField_local (s : PolarSection D) (i : ι) (x : B)
    (hx : x ∈ D.domain i) :
    polarDensityField D s x = ((polarFamilyEquiv D s).val i ⟨x, hx⟩).1 :=
  (CocycleBundleDensity.localTriv_polarDensity D i (⟨x, s.val x⟩ : PolarTotal D)).symm

/-- Actual represented section density agrees with positive-density recovery from every available original local spinor field. -/
theorem spinorDensityField_local (s : SpinorSection D) (i : ι) (x : B)
    (hx : x ∈ D.domain i) :
    spinorDensityField D s x =
      DensityFrameFields.density ((spinorFamilyEquiv D s).val i ⟨x, hx⟩) :=
  (CocycleBundleDensity.localTriv_spinorDensity D i (⟨x, s.val x⟩ : SpinorTotal D)).symm

/-- The actual section density is the original bilinear invariant of every available represented local field. -/
theorem spinorDensityField_value_local (s : SpinorSection D) (i : ι) (x : B)
    (hx : x ∈ D.domain i) :
    (spinorDensityField D s x : ℝ) =
      SpinorRegularity.invariantDensity ((spinorFamilyEquiv D s).val i ⟨x, hx⟩).val := by
  rw [spinorDensityField_local D s i x hx, DensityFrameFields.density_value_eq_invariantDensity]

/-- Density obtained from the actual smooth polar section graph equals the independently glued local-family density as a bundled smooth field. -/
theorem polarDensityField_eq_glued (s : PolarSection D) :
    polarDensityField D s =
      CocycleDensityGluing.polarDensityField D (polarFamilyEquiv D s) := by
  apply ContMDiffMap.ext
  intro x
  obtain ⟨i, hx⟩ := D.covers x
  exact (polarDensityField_local D s i x hx).trans
    (CocycleDensityGluing.polarDensity_eq_local D (polarFamilyEquiv D s) i x hx).symm

/-- Density from the actual represented section graph equals the independently glued original local-spinor invariant density as a bundled smooth field. -/
theorem spinorDensityField_eq_glued (s : SpinorSection D) :
    spinorDensityField D s =
      CocycleDensityGluing.spinorDensityField D (spinorFamilyEquiv D s) := by
  apply ContMDiffMap.ext
  intro x
  obtain ⟨i, hx⟩ := D.covers x
  exact (spinorDensityField_local D s i x hx).trans
    (CocycleDensityGluing.spinorDensity_eq_local D (spinorFamilyEquiv D s) i x hx).symm

/-- Any positive-density map agreeing with the actual local coordinates of the polar section is the composed section density; no regularity of the competing map is assumed. -/
theorem polarDensityField_unique (s : PolarSection D) (r : B → PositiveDensity)
    (hr : ∀ (i : ι) (x : D.domain i), r x = ((polarFamilyEquiv D s).val i x).1) :
    r = (polarDensityField D s : B → PositiveDensity) := by
  funext x
  obtain ⟨i, hx⟩ := D.covers x
  exact (hr i ⟨x, hx⟩).trans (polarDensityField_local D s i x hx).symm

/-- Any positive-density map whose real values equal the actual local spinor invariants is exactly the density of the original graph-smooth spinor section. -/
theorem spinorDensityField_unique (s : SpinorSection D) (r : B → PositiveDensity)
    (hr : ∀ (i : ι) (x : D.domain i),
      (r x : ℝ) = SpinorRegularity.invariantDensity ((spinorFamilyEquiv D s).val i x).val) :
    r = (spinorDensityField D s : B → PositiveDensity) := by
  funext x
  obtain ⟨i, hx⟩ := D.covers x
  apply Subtype.ext
  exact (hr i ⟨x, hx⟩).trans (spinorDensityField_value_local D s i x hx).symm

/-- Actual smooth-section realization preserves the composed positive-density field as an equality of bundled smooth maps. -/
theorem spinorDensityField_realization (s : PolarSection D) :
    spinorDensityField D (sectionEquiv D s) = polarDensityField D s := by
  apply ContMDiffMap.ext
  intro x
  exact CocycleBundleDensity.spinorDensity_realization D (⟨x, s.val x⟩ : PolarTotal D)

/-- A supplied local matrix frame change preserves the actual polar section density as a bundled smooth field. -/
theorem polarDensityField_gauge (h : CocycleGaugeTransform.FrameChange D) (s : PolarSection D) :
    polarDensityField (CocycleGaugeTransform.transformed D h)
      (CocycleGaugeSections.polarSectionEquiv D h s) = polarDensityField D s := by
  apply ContMDiffMap.ext
  intro x
  exact CocycleBundleDensity.polarDensity_gauge D h (⟨x, s.val x⟩ : PolarTotal D)

/-- Actual represented local frame changes preserve the original spinor section's positive invariant-density field. -/
theorem spinorDensityField_gauge (h : CocycleGaugeTransform.FrameChange D) (s : SpinorSection D) :
    spinorDensityField (CocycleGaugeTransform.transformed D h)
      (CocycleGaugeSections.spinorSectionEquiv D h s) = spinorDensityField D s := by
  apply ContMDiffMap.ext
  intro x
  exact CocycleBundleDensity.spinorDensity_gauge D h (⟨x, s.val x⟩ : SpinorTotal D)

variable {E' H' B' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace B'] [ChartedSpace H' B'] [IsManifold J n B']
  (f : C^n⟮J, B'; I, B⟯)

/-- Actual polar section density commutes with smooth base pullback as the genuine bundled composition with the base map. -/
theorem polarDensityField_pullback (s : PolarSection D) :
    polarDensityField (CocyclePullback.pullback D f)
      (CocyclePullbackSections.polarSectionPullback D f s) = (polarDensityField D s).comp f := by
  apply ContMDiffMap.ext
  intro x
  rw [ContMDiffMap.comp_apply, polarDensityField_apply, polarDensityField_apply,
    CocyclePullbackSections.polarSectionPullback_apply]

/-- The actual represented-spinor positive invariant-density field commutes with smooth base pullback as a bundled smooth-field equality. -/
theorem spinorDensityField_pullback (s : SpinorSection D) :
    spinorDensityField (CocyclePullback.pullback D f)
      (CocyclePullbackSections.spinorSectionPullback D f s) = (spinorDensityField D s).comp f := by
  apply ContMDiffMap.ext
  intro x
  rw [ContMDiffMap.comp_apply, spinorDensityField_apply, spinorDensityField_apply,
    CocyclePullbackSections.spinorSectionPullback_apply]

end FoliationQM.CocycleSectionDensity
