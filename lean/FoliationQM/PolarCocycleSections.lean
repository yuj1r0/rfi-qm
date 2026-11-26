module
public import FoliationQM.PolarCocycleManifold
public import FoliationQM.SmoothCocycleSections
public import FoliationQM.CocyclePolarFields
public import FoliationQM.PolarCocycleExamples

/-!
# Actual smooth sections of the supplied polar cocycle bundles

Source: the quotient-bundle section assertion of v13 `prop:takabayasi`.
The independently constructed actual cocycle total-space atlases define
smooth sections by smoothness of their total-space graphs. The generic
section theorem identifies them with the previously defined compatible
smooth local families on the true open chart domains. Actual total-space
polar realization induces a bijection of these graph-defined sections,
and its local expression agrees with the earlier local-family realization.

These statements use the supplied determinant-one transition cocycle and
explicit smoothness of the base. They neither identify an abstract Spin
structure nor select a global individual angle or frame representative.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.PolarCocycleSections
open DiracMatrices PolarSignQuotient SourcePolarProductQuotient
open PolarCocycleBundles

attribute [local instance] SmoothCocycleBundle.totalChartedSpace

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {ι : Type*} {n : WithTop ℕ∞}
  (D : PolarTransitionCocycle.Data I B ι n) [IsManifold I n B]

/-- Actual polar cocycle-bundle sections whose total-space graphs are smooth in the independently constructed cocycle atlas. -/
abbrev PolarSection :=
  SmoothCocycleSections.SmoothSection I DensityFrameManifold.model (polarCore D) n

/-- Actual regular-spinor cocycle-bundle sections defined independently by smoothness of their total-space graphs. -/
abbrev SpinorSection :=
  SmoothCocycleSections.SmoothSection I 𝓘(ℝ, Spinor) (spinorCore D) n

/-- Actual graph-smooth polar sections correspond exactly to the pre-existing compatible local smooth polar families. -/
def polarFamilyEquiv : PolarSection D ≃ CocyclePolarFields.SmoothPolarFamily D :=
  SmoothCocycleSections.sectionEquiv I DensityFrameManifold.model (polarCore D) n
    (PolarTransitionCocycle.contMDiffOn_polarChange D)

/-- Actual graph-smooth spinor sections correspond exactly to the pre-existing compatible local represented-spinor families. -/
def spinorFamilyEquiv : SpinorSection D ≃ CocyclePolarFields.SmoothSpinorFamily D :=
  SmoothCocycleSections.sectionEquiv I 𝓘(ℝ, Spinor) (spinorCore D) n
    (PolarTransitionCocycle.contMDiffOn_spinorChange D)

/-- Local polar coordinates of a graph-smooth section are exactly the actual core-trivialization coordinates on the original open domain. -/
theorem polarFamilyEquiv_apply (s : PolarSection D) (i : ι) (x : D.domain i) :
    (polarFamilyEquiv D s).val i x =
      ((polarCore D).localTriv i (⟨x.val, s.val x.val⟩ : PolarTotal D)).2 := rfl

/-- Local represented-spinor coordinates of a graph-smooth section are exactly the actual original core-trivialization coordinates. -/
theorem spinorFamilyEquiv_apply (s : SpinorSection D) (i : ι) (x : D.domain i) :
    (spinorFamilyEquiv D s).val i x =
      ((spinorCore D).localTriv i (⟨x.val, s.val x.val⟩ : SpinorTotal D)).2 := rfl

/-- Reconstructing a polar section from a compatible local family gives its prescribed value in every actual available chart. -/
theorem polarFamilyEquiv_symm_localTriv (f : CocyclePolarFields.SmoothPolarFamily D)
    (i : ι) (x : D.domain i) :
    (polarCore D).localTriv i
      (⟨x.val, ((polarFamilyEquiv D).symm f).val x.val⟩ : PolarTotal D) =
      (x.val, f.val i x) :=
  SmoothCocycleSections.sectionEquiv_symm_localTriv I DensityFrameManifold.model
    (polarCore D) n (PolarTransitionCocycle.contMDiffOn_polarChange D) f i x.val x.property

/-- Reconstructing a represented-spinor section gives its prescribed compatible field in every actual available chart. -/
theorem spinorFamilyEquiv_symm_localTriv (f : CocyclePolarFields.SmoothSpinorFamily D)
    (i : ι) (x : D.domain i) :
    (spinorCore D).localTriv i
      (⟨x.val, ((spinorFamilyEquiv D).symm f).val x.val⟩ : SpinorTotal D) =
      (x.val, f.val i x) :=
  SmoothCocycleSections.sectionEquiv_symm_localTriv I 𝓘(ℝ, Spinor)
    (spinorCore D) n (PolarTransitionCocycle.contMDiffOn_spinorChange D) f i x.val x.property

/-- The actual total-space polar diffeomorphism gives a bijection of independently graph-defined smooth sections. -/
def sectionEquiv : PolarSection D ≃ SpinorSection D where
  toFun s := ⟨fun x => productRegularHomeomorph (s.val x),
    (PolarCocycleManifold.totalRealizationDiffeomorph D).contMDiff.comp s.property⟩
  invFun s := ⟨fun x => productRegularHomeomorph.symm (s.val x),
    (PolarCocycleManifold.totalRealizationDiffeomorph D).symm.contMDiff.comp s.property⟩
  left_inv s := Subtype.ext (funext fun x => productRegularHomeomorph.symm_apply_apply (s.val x))
  right_inv s := Subtype.ext (funext fun x => productRegularHomeomorph.apply_symm_apply (s.val x))

/-- The actual smooth-section correspondence acts by the existing polar realization in the fiber at the same base point. -/
theorem sectionEquiv_apply (s : PolarSection D) (x : B) :
    (sectionEquiv D s).val x = productRegularHomeomorph (s.val x) := rfl

/-- Inverse smooth-section reconstruction uses the existing quotient-valued polar inverse in each fiber. -/
theorem sectionEquiv_symm_apply (s : SpinorSection D) (x : B) :
    ((sectionEquiv D).symm s).val x = productRegularHomeomorph.symm (s.val x) := rfl

/-- Actual total-space realization commutes with the total-space graph of each smooth polar section. -/
theorem sectionEquiv_graph (s : PolarSection D) (x : B) :
    PolarCocycleManifold.totalRealizationDiffeomorph D (⟨x, s.val x⟩ : PolarTotal D) =
      (⟨x, (sectionEquiv D s).val x⟩ : SpinorTotal D) := rfl

/-- Reading the actual local coordinates after section realization gives exactly the previously proved compatible-local-family realization. -/
theorem sectionEquiv_family (s : PolarSection D) :
    spinorFamilyEquiv D (sectionEquiv D s) =
      CocyclePolarFields.realizationEquiv D (polarFamilyEquiv D s) := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  exact (PolarTransitionCocycle.change_equivariant D
    (PolarTransitionCocycle.indexAt D x.val) i x.val (s.val x.val)).symm

/-- The inverse section reconstruction has exactly the previous local quotient-valued reconstruction in every chart. -/
theorem sectionEquiv_symm_family (s : SpinorSection D) :
    polarFamilyEquiv D ((sectionEquiv D).symm s) =
      (CocyclePolarFields.realizationEquiv D).symm (spinorFamilyEquiv D s) := by
  apply (CocyclePolarFields.realizationEquiv D).injective
  rw [← sectionEquiv_family, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The represented section's actual bilinear invariant density is exactly the positive-density coordinate of its polar section. -/
theorem sectionEquiv_density (s : PolarSection D) (x : B) :
    SpinorRegularity.invariantDensity ((sectionEquiv D s).val x).val =
      ((s.val x).1 : ℝ) := density_productRegularHomeomorph (s.val x)

/-- Inverse section reconstruction recovers the actual original spinor invariant density. -/
theorem sectionEquiv_symm_density (s : SpinorSection D) (x : B) :
    ((((sectionEquiv D).symm s).val x).1 : ℝ) =
      SpinorRegularity.invariantDensity (s.val x).val :=
  productRegularHomeomorph_symm_density (s.val x)

/-- Every actual graph-smooth regular-spinor section has exactly one actual graph-smooth quotient-valued polar section with its pointwise realization. -/
theorem existsUnique_polarSection (s : SpinorSection D) :
    ∃! t : PolarSection D, ∀ x, productRegularHomeomorph (t.val x) = s.val x := by
  refine ⟨(sectionEquiv D).symm s, ?_, ?_⟩
  · intro x
    exact productRegularHomeomorph.apply_symm_apply (s.val x)
  · intro t ht
    apply Subtype.ext
    funext x
    apply productRegularHomeomorph.injective
    exact (ht x).trans (productRegularHomeomorph.apply_symm_apply (s.val x)).symm

/-- A cocycle constructed from supplied global smooth matrix fields has an actual graph-smooth polar section, obtained from the explicit constant reference polar class. -/
theorem nonempty_coboundaryPolarSection
    (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SourcePolarDatum.SpecialLinearMatrix⟯) :
    Nonempty (PolarSection (PolarCocycleExamples.coboundaryData U hU g)) :=
  ⟨(polarFamilyEquiv _).symm (PolarCocycleExamples.coboundaryPolarFamily U hU g
    (ContMDiffMap.const PolarCocycleExamples.unitPolar))⟩

/-- The same constructed cocycle has an actual graph-smooth strict regular-spinor section; this asserts existence for the explicit coboundary construction, not arbitrary cocycles. -/
theorem nonempty_coboundarySpinorSection
    (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SourcePolarDatum.SpecialLinearMatrix⟯) :
    Nonempty (SpinorSection (PolarCocycleExamples.coboundaryData U hU g)) :=
  ⟨(spinorFamilyEquiv _).symm (PolarCocycleExamples.coboundarySpinorFamily U hU g
    (ContMDiffMap.const PolarCocycleExamples.unitPolar))⟩

end FoliationQM.PolarCocycleSections
