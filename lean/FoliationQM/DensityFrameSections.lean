module
public import FoliationQM.DensityFrameManifold
public import FoliationQM.PolarBundleSections
public import FoliationQM.SmoothTrivialBundle

/-!
# Smooth sections in literal density and frame-quotient coordinates

Source: the fixed-representation section content of v13
`prop:takabayasi`. The fiber is the independently constructed natural
positive-density times intrinsic frame-sign quotient. Its genuine
regular-spinor diffeomorphism induces a base-preserving diffeomorphism
between the actual `Bundle.Trivial` total spaces over any supplied real
charted base. A smooth base gives a smooth total manifold.

The existing `Bundle.Trivial.topologicalSpace` is selected locally and
explicitly because a product fiber also matches Mathlib's product-bundle
instance. The explicit local total atlas is exactly the previously
proved `SmoothTrivialBundle.totalChartedSpace`; no topology is generated
or changed. Smooth sections retain their independent definition by
smoothness of their actual total-space graphs.

The induced section equivalence preserves the actual realization,
recovers the bilinear invariant density, and agrees exactly with the
previous source-quotient section correspondence through the genuine
density-product diffeomorphism. These are fixed trivial-bundle results;
no individual global angle/matrix representative or nontrivial spin
bundle is selected or identified.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.DensityFrameSections
open DiracMatrices PolarSignQuotient SourcePolarDatum PolarAmplitudeTopology
open SourcePolarProductQuotient

/-- The actual total space of the fixed trivial bundle with positive-density and frame-sign-quotient fiber. -/
abbrev DensityTotal (B : Type*) :=
  Bundle.TotalSpace DensityFrameManifold.Product (Bundle.Trivial B DensityFrameManifold.Product)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (B : Type*) [TopologicalSpace B] [ChartedSpace H B]

attribute [local instance] SmoothTrivialBundle.totalChartedSpace

/-- Select the existing standard trivial-bundle topology locally, resolving the product-fiber instance overlap without defining a new topology. -/
local instance instTopologicalSpaceDensityTotal : TopologicalSpace (DensityTotal B) :=
  Bundle.Trivial.topologicalSpace B DensityFrameManifold.Product

variable (n : WithTop ℕ∞)

/-- A smooth real base gives the actual density-frame trivial-bundle total space its explicit smooth product-pullback atlas. -/
theorem isManifold_densityTotal [IsManifold I n B] :
    IsManifold (I.prod DensityFrameManifold.model) n (DensityTotal B) :=
  SmoothTrivialBundle.isManifold_total I DensityFrameManifold.model B DensityFrameManifold.Product n

/-- The actual density-frame fiber diffeomorphism induces a genuine base-preserving diffeomorphism of the fixed trivial-bundle total spaces. -/
def totalRealization :
    Diffeomorph (I.prod DensityFrameManifold.model) (I.prod 𝓘(ℝ, Spinor))
      (DensityTotal B) (PolarBundleSections.SpinorTotal B) n :=
  SmoothTrivialBundle.totalMapDiffeomorph I B (DensityFrameManifold.productRegularDiffeomorph n)

/-- The total-space diffeomorphism applies precisely the existing density-frame realization and leaves the base point unchanged. -/
theorem totalRealization_apply (p : DensityTotal B) :
    totalRealization I B n p = ⟨p.proj, productRegularHomeomorph p.snd⟩ := rfl

/-- The inverse total-space diffeomorphism applies precisely the existing inverse density-frame realization and leaves the base point unchanged. -/
theorem totalRealization_symm_apply (p : PolarBundleSections.SpinorTotal B) :
    (totalRealization I B n).symm p = ⟨p.proj, productRegularHomeomorph.symm p.snd⟩ := rfl

/-- The genuine total-space realization preserves the actual bundle projection. -/
theorem totalRealization_proj (p : DensityTotal B) :
    (totalRealization I B n p).proj = p.proj := rfl

/-- The genuine total-space reconstruction preserves the actual bundle projection. -/
theorem totalRealization_symm_proj (p : PolarBundleSections.SpinorTotal B) :
    ((totalRealization I B n).symm p).proj = p.proj := rfl

/-- On literal positive-density, real-angle and determinant-one matrix representatives, total-space realization is exactly the source polar spinor formula. -/
theorem totalRealization_mk_real (b : B) (rho : PositiveDensity) (beta : ℝ)
    (A : SpecialLinearMatrix) :
    (totalRealization I B n
      ⟨b, rho, Quotient.mk frameSetoid ((beta : ChiralAngleCircle.Angle), A)⟩).snd.val =
      PolarSpinorBilinears.polarSpinor rho beta (SpecialLinearSpin.spin A) :=
  DensityFrameManifold.productRegularDiffeomorph_mk_real n rho beta A

/-- Actual total-space reconstruction recovers the bilinear invariant density as its positive-density coordinate. -/
theorem totalRealization_symm_density (p : PolarBundleSections.SpinorTotal B) :
    ((((totalRealization I B n).symm p).snd).1 : ℝ) =
      SpinorRegularity.invariantDensity p.snd.val :=
  productRegularHomeomorph_symm_density p.snd

/-- Dependent sections of the actual density-frame trivial bundle whose actual total-space graphs are smooth. -/
abbrev DensitySection :=
  SmoothTrivialBundle.SmoothSection I DensityFrameManifold.model B DensityFrameManifold.Product n

/-- The genuine fiber diffeomorphism gives an exact equivalence between graph-defined smooth density-frame sections and regular-spinor sections. -/
def sectionEquiv : DensitySection I B n ≃ PolarBundleSections.SpinorSection I B n :=
  SmoothTrivialBundle.sectionCongr I B (DensityFrameManifold.productRegularDiffeomorph n)

/-- The smooth-section equivalence evaluates pointwise by the actual density-frame realization. -/
theorem sectionEquiv_apply (s : DensitySection I B n) (b : B) :
    (sectionEquiv I B n s).val b = productRegularHomeomorph (s.val b) := rfl

/-- The inverse smooth-section equivalence evaluates pointwise by actual density-frame reconstruction. -/
theorem sectionEquiv_symm_apply (s : PolarBundleSections.SpinorSection I B n) (b : B) :
    ((sectionEquiv I B n).symm s).val b = productRegularHomeomorph.symm (s.val b) := rfl

/-- Inverse smooth-section reconstruction recovers exactly the original spinor section's bilinear invariant density at every base point. -/
theorem sectionEquiv_symm_density (s : PolarBundleSections.SpinorSection I B n) (b : B) :
    ((((sectionEquiv I B n).symm s).val b).1 : ℝ) =
      SpinorRegularity.invariantDensity (s.val b).val :=
  productRegularHomeomorph_symm_density (s.val b)

/-- The realized spinor section has exactly the original positive-density coordinate as its bilinear invariant density. -/
theorem sectionEquiv_density (s : DensitySection I B n) (b : B) :
    SpinorRegularity.invariantDensity ((sectionEquiv I B n s).val b).val =
      ((s.val b).1 : ℝ) :=
  density_productRegularHomeomorph (s.val b)

/-- The actual total-space diffeomorphism maps the whole graph of a smooth density-frame section to the graph of its corresponding spinor section. -/
theorem sectionEquiv_graph (s : DensitySection I B n) :
    (totalRealization I B n) ∘ (fun b => (⟨b, s.val b⟩ : DensityTotal B)) =
      (fun b => (⟨b, (sectionEquiv I B n s).val b⟩ : PolarBundleSections.SpinorTotal B)) := rfl

/-- The genuine density-product diffeomorphism gives an equivalence from the previous source-quotient sections to the literal density-frame sections. -/
def sourceSectionEquiv : PolarBundleSections.SourceSection I B n ≃ DensitySection I B n :=
  SmoothTrivialBundle.sectionCongr I B (DensityFrameManifold.densityProductDiffeomorph n)

/-- Conversion from source-quotient sections to density-frame sections is exactly the existing density-product homeomorphism pointwise. -/
theorem sourceSectionEquiv_apply (s : PolarBundleSections.SourceSection I B n) (b : B) :
    (sourceSectionEquiv I B n s).val b = densityProductHomeomorph (s.val b) := rfl

/-- Separating density in a smooth source-quotient section and then realizing it gives exactly the previous smooth spinor-section correspondence. -/
theorem sourceSectionEquiv_realization (s : PolarBundleSections.SourceSection I B n) :
    sectionEquiv I B n (sourceSectionEquiv I B n s) =
      PolarBundleSections.sectionEquiv I B n s := by
  apply Subtype.ext
  funext b
  change SourcePolarQuotient.regularHomeomorph
    (densityProductHomeomorph.symm (densityProductHomeomorph (s.val b))) =
    SourcePolarQuotient.regularHomeomorph (s.val b)
  rw [Homeomorph.symm_apply_apply]

/-- Every smooth regular-spinor section has a unique smooth density/frame-quotient section with its actual pointwise realization; no individual global representative is chosen. -/
theorem existsUnique_densitySection (s : PolarBundleSections.SpinorSection I B n) :
    ∃! t : DensitySection I B n, ∀ b, productRegularHomeomorph (t.val b) = s.val b := by
  refine ⟨(sectionEquiv I B n).symm s, ?_, ?_⟩
  · intro b
    rw [sectionEquiv_symm_apply, Homeomorph.apply_symm_apply]
  · intro t ht
    apply Subtype.ext
    funext b
    apply productRegularHomeomorph.injective
    rw [ht b, sectionEquiv_symm_apply, Homeomorph.apply_symm_apply]

end FoliationQM.DensityFrameSections
