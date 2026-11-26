module

public import FoliationQM.EmbeddedNodalCoordinates
public import FoliationQM.SmoothCoordinateTubeCutoff
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Coordinate nullity of an embedded nodal surface

Source: v13 `thm:wallstrom` Part(c), the step "Since `𝒩` has measure zero",
component kind B. The image of a smooth embedding of a real two-dimensional
manifold into a real four-dimensional manifold has zero coordinate volume in
every smooth chart, and hence zero measure for every density-weighted
coordinate measure. Nullity is derived from the adapted charts; it is not a
hypothesis. The statements concern chart-coordinate volume only: no intrinsic
manifold measure, closedness of the image or normal-distance formula is asserted.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.EmbeddedNodalNullity

open RealLorentzFrame Set Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

variable {S M : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
  [TopologicalSpace M] [ChartedSpace Covector M]
  [IsManifold 𝓘(ℝ, Covector) ∞ M]

/-- In any smooth chart of the ambient four-manifold, the part of an embedded
surface lying in the chart domain has zero coordinate volume. -/
theorem volume_chart_image_eq_zero {f : S → M}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f)
    {c : OpenPartialHomeomorph M Covector}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M) :
    volume (c '' (range f ∩ c.source)) = 0 := by
  refine measure_null_of_locally_null _ ?_
  rintro _ ⟨_, ⟨⟨x, rfl⟩, hxc⟩, rfl⟩
  obtain ⟨e, hxe, he, haxis⟩ := EmbeddedNodalCoordinates.exists_adapted_chart hf x
  refine ⟨c '' (range f ∩ (c.source ∩ e.source)), ?_, ?_⟩
  · have hopen : IsOpen (c '' (c.source ∩ e.source)) :=
      c.isOpen_image_of_subset_source (c.open_source.inter e.open_source) inter_subset_left
    have hmem : c (f x) ∈ c '' (c.source ∩ e.source) := mem_image_of_mem _ ⟨hxc, hxe⟩
    refine Filter.mem_of_superset (inter_mem_nhdsWithin _ (hopen.mem_nhds hmem)) ?_
    rintro _ ⟨⟨y, ⟨hyf, hyc⟩, rfl⟩, ⟨z, ⟨hzc, hze⟩, hzy⟩⟩
    obtain rfl : z = y := c.injOn hzc hyc hzy
    exact ⟨z, ⟨hyf, hzc, hze⟩, rfl⟩
  · let t : Set Covector := (e.target ∩ e.symm ⁻¹' c.source) ∩ {v | v 2 = 0 ∧ v 3 = 0}
    have hdiff : DifferentiableOn ℝ (c ∘ e.symm) t :=
      (((contMDiffOn_of_mem_maximalAtlas hc).comp'
        (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn.differentiableOn
          (by simp)).mono inter_subset_left
    have hnull : volume t = 0 :=
      measure_mono_null inter_subset_right SmoothCoordinateTubeCutoff.axis_null
    refine measure_mono_null ?_
      (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hnull)
    rintro _ ⟨y, ⟨hyf, hyc, hye⟩, rfl⟩
    refine ⟨e y, ⟨⟨e.map_source hye, ?_⟩, (haxis y hye).mp hyf⟩, ?_⟩
    · change e.symm (e y) ∈ c.source
      rwa [e.left_inv hye]
    · simp [e.left_inv hye]

/-- A smooth embedded surface in coordinate four-space has zero volume. -/
theorem volume_range_eq_zero {f : S → Covector}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) : volume (range f) = 0 := by
  have hc : OpenPartialHomeomorph.refl Covector ∈
      IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ Covector := by
    simpa [chartAt_self_eq] using
      IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Covector)) (n := ∞) (0 : Covector)
  simpa using volume_chart_image_eq_zero hf hc

/-- The embedded surface is null for every measure absolutely continuous with
respect to coordinate volume. -/
theorem measure_range_eq_zero {f : S → Covector}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f)
    {μ : Measure Covector} (hμ : μ ≪ volume) : μ (range f) = 0 :=
  hμ (volume_range_eq_zero hf)

/-- In particular it is null for every density-weighted coordinate volume,
such as the volume of a positive auxiliary metric. -/
theorem withDensity_range_eq_zero {f : S → Covector}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (w : Covector → ℝ≥0∞) :
    (volume.withDensity w) (range f) = 0 :=
  measure_range_eq_zero hf (withDensity_absolutelyContinuous volume w)

end FoliationQM.EmbeddedNodalNullity
