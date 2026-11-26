module
public import FoliationQM.CocyclePolarFields

/-!
# Constructed smooth cocycles and compatible local families

Source: consistency checks for the supplied-transition scope of v13
`prop:takabayasi`. An actual open cover and a family of smooth determinant-one
matrix fields give the explicit coboundary transitions G_ij = h_j h_i⁻¹.
The identity, composition and regularity conditions are proved from genuine
group operations. Any global smooth polar field then supplies compatible
local fields by the actual h_i action. The represented spinor family is
exactly its chartwise polar realization.

A fixed explicit positive-density/frame class gives an actual inhabited
example for every such coboundary construction. This verifies that the
transition and compatibility premises can be realized. It does not assert
that every supplied cocycle is a coboundary or admits a regular section.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.PolarCocycleExamples
open SourcePolarDatum SourcePolarProductQuotient PolarAmplitudeTopology
open PolarSignQuotient DiracMatrices

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {ι : Type*} {n : WithTop ℕ∞}

/-- Actual smooth matrix fields on an actual open cover construct an oriented smooth cocycle by G_ij = h_j h_i⁻¹, with all cocycle conditions proved. -/
def coboundaryData (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯) :
    PolarTransitionCocycle.Data I B ι n where
  domain := U
  covers := hU
  transition i j x := g j x * (g i x)⁻¹
  smooth_transition i j :=
    (GaugePolarFields.multiplyGauge (g j) (GaugePolarFields.inverseGauge (g i))).contMDiff.contMDiffOn
  identity i x _ := mul_inv_cancel _
  comp i j k x _ _ _ := by simp [mul_assoc]

/-- The constructed cocycle uses exactly the supplied open domains. -/
theorem coboundaryData_domain (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯) :
    (coboundaryData U hU g).domain = U := rfl

/-- The actual cocycle transition has the explicitly ordered h_j h_i⁻¹ matrix formula. -/
theorem coboundaryData_transition (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (i j : ι) (x : B) :
    (coboundaryData U hU g).transition i j x = g j x * (g i x)⁻¹ := rfl

/-- The identity matrix fields construct an actual trivial smooth transition cocycle on any supplied open cover. -/
def trivialData (U : ι → TopologicalSpace.Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i)
    (n : WithTop ℕ∞) : PolarTransitionCocycle.Data I B ι n :=
  coboundaryData U hU (fun _ => ContMDiffMap.const (1 : SpecialLinearMatrix))

/-- Every transition of the constructed trivial cocycle is the actual identity matrix. -/
theorem trivialData_transition (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i) (n : WithTop ℕ∞) (i j : ι) (x : B) :
    (trivialData (I := I) U hU n).transition i j x = 1 := by
  change (1 : SpecialLinearMatrix) * 1⁻¹ = 1
  simp

/-- Acting by each supplied matrix field on a global smooth polar field and restricting to the actual chart domains gives a compatible local family for the constructed cocycle. -/
def coboundaryPolarFamily (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, B; DensityFrameManifold.model, DensityFrameManifold.Product⟯) :
    CocyclePolarFields.SmoothPolarFamily (coboundaryData U hU g) := by
  refine ⟨fun i => ⟨fun x => DensityFrameAction.productAction (g i x.val) (f x.val), ?_⟩, ?_⟩
  · exact (GaugePolarFields.polarGaugeEquiv (g i) f).contMDiff.comp contMDiff_subtype_val
  · intro i j x hi hj
    change DensityFrameAction.productAction (g j x) (f x) =
      DensityFrameAction.productAction (g j x * (g i x)⁻¹)
        (DensityFrameAction.productAction (g i x) (f x))
    rw [← DensityFrameAction.productAction_mul, mul_assoc, inv_mul_cancel, mul_one]

/-- The constructed local polar family is the actual matrix action on the supplied global field at each local point. -/
theorem coboundaryPolarFamily_apply (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, B; DensityFrameManifold.model, DensityFrameManifold.Product⟯)
    (i : ι) (x : U i) :
    (coboundaryPolarFamily U hU g f).val i x =
      DensityFrameAction.productAction (g i x.val) (f x.val) := rfl

/-- Actual pointwise polar realization gives a compatible represented-spinor family for the constructed cocycle. -/
def coboundarySpinorFamily (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, B; DensityFrameManifold.model, DensityFrameManifold.Product⟯) :
    CocyclePolarFields.SmoothSpinorFamily (coboundaryData U hU g) :=
  CocyclePolarFields.realizationEquiv _ (coboundaryPolarFamily U hU g f)

/-- The constructed local spinor family is exactly the actual represented matrix action on the original realized global field. -/
theorem coboundarySpinorFamily_apply (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, B; DensityFrameManifold.model, DensityFrameManifold.Product⟯)
    (i : ι) (x : U i) :
    (coboundarySpinorFamily U hU g f).val i x =
      RegularSpinorAction.act (g i x.val) (productRegularHomeomorph (f x.val)) :=
  RegularSpinorAction.realization_equivariant _ _

/-- The local actual invariant densities in the constructed example equal the density of the supplied global polar field. -/
theorem coboundarySpinorFamily_density (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯)
    (f : C^n⟮I, B; DensityFrameManifold.model, DensityFrameManifold.Product⟯)
    (i : ι) (x : U i) :
    SpinorRegularity.invariantDensity ((coboundarySpinorFamily U hU g f).val i x).val =
      ((f x.val).1 : ℝ) := by
  rw [coboundarySpinorFamily_apply, RegularSpinorAction.invariantDensity_act]
  exact density_productRegularHomeomorph (f x.val)

/-- A concrete reference polar class uses positive density one, angle zero and the actual identity matrix. -/
def unitPolar : DensityFrameManifold.Product :=
  (⟨1, by norm_num⟩, Quotient.mk frameSetoid ((0 : ChiralAngleCircle.Angle), (1 : SpecialLinearMatrix)))

/-- Every constructed coboundary cocycle admits an actual compatible smooth polar family, obtained from the explicit constant reference class. -/
theorem nonempty_coboundaryPolarFamily (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯) :
    Nonempty (CocyclePolarFields.SmoothPolarFamily (coboundaryData U hU g)) :=
  ⟨coboundaryPolarFamily U hU g (ContMDiffMap.const unitPolar)⟩

/-- Every constructed coboundary cocycle also admits a compatible strict regular-spinor family, by actual realization of the explicit polar example. -/
theorem nonempty_coboundarySpinorFamily (U : ι → TopologicalSpace.Opens B)
    (hU : ∀ x : B, ∃ i, x ∈ U i)
    (g : ι → C^n⟮I, B; 𝓘(ℝ, SpecialLinearCharts.Model), SpecialLinearMatrix⟯) :
    Nonempty (CocyclePolarFields.SmoothSpinorFamily (coboundaryData U hU g)) :=
  ⟨coboundarySpinorFamily U hU g (ContMDiffMap.const unitPolar)⟩

end FoliationQM.PolarCocycleExamples
