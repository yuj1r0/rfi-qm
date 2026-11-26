module

public import FoliationQM.CodimensionTwoCoordinates
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Adapted coordinates for an embedded nodal surface

Source: v13 `thm:wallstrom` Part(c), geometric prerequisite, component kind B.
A smooth embedding of a real two-dimensional manifold into a real
four-dimensional manifold admits a smooth ambient chart in which its image
is exactly the coordinate plane with the last two coordinates zero.
The ambient chart is shrunk using the topological embedding, so the assertion
concerns the entire image in its source, not only one parametrized branch.
This local statement does not assert closedness or a metric normal-distance formula.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.EmbeddedNodalCoordinates

open RealLorentzFrame Set Manifold
open scoped Topology Manifold ContDiff

variable {S M : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
  [TopologicalSpace M] [ChartedSpace Covector M]
  [IsManifold 𝓘(ℝ, Covector) ∞ M]

private theorem linear_postcomposition_mem_atlas (c : OpenPartialHomeomorph M Covector)
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M)
    (A : Covector ≃L[ℝ] Covector) :
    c.transHomeomorph A.toHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact A.toContinuousLinearMap.contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas hc)
  · exact (contMDiffOn_symm_of_mem_maximalAtlas hc).comp
      A.symm.toContinuousLinearMap.contMDiff.contMDiffOn (fun _ hy => hy)

/-- Every point of an embedded surface has a smooth ambient chart identifying
the whole image in that chart with the standard codimension-two axis. -/
theorem exists_adapted_chart {f : S → M}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (x : S) :
    ∃ e : OpenPartialHomeomorph M Covector,
      f x ∈ e.source ∧ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M ∧
      ∀ y ∈ e.source, y ∈ range f ↔ (e y) 2 = 0 ∧ (e y) 3 = 0 := by
  let h := hf.isImmersion.isImmersionAt x
  let a := h.domChart
  let b := h.codChart
  let L := h.equiv
  obtain ⟨A, hAaxis, _⟩ := CodimensionTwoCoordinates.exists_normalization L
  have hchart (z : S) (hz : z ∈ a.source) : b (f z) = L (a z, 0) := by
    have hw := h.writtenInCharts (by simpa [a] using a.map_source hz)
    simpa [a, b, L, Function.comp_def, h.domChart.left_inv hz] using hw
  obtain ⟨O, hO, himage⟩ :=
    hf.isEmbedding.isInducing.image_eq_isOpen_inter_range a.open_source
  let T : Set Covector := {v | (L.symm v).1 ∈ a.target}
  have hT : IsOpen T := a.open_target.preimage (continuous_fst.comp L.symm.continuous)
  let U := O ∩ (b.source ∩ b ⁻¹' T)
  have hU : IsOpen U := hO.inter (b.continuousOn.isOpen_inter_preimage b.open_source hT)
  have hx : x ∈ a.source := h.mem_domChart_source
  have hfx : f x ∈ b.source := h.mem_codChart_source
  have hxO : f x ∈ O := (himage ▸ (show f x ∈ f '' a.source from ⟨x, hx, rfl⟩)).1
  have hxT : b (f x) ∈ T := by
    change (L.symm (b (f x))).1 ∈ a.target
    rw [hchart x hx, L.symm_apply_apply]
    exact a.map_source hx
  let c := b.restr U
  let e := c.transHomeomorph A.toHomeomorph
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M :=
    restr_mem_maximalAtlas _ h.codChart_mem_maximalAtlas hU
  refine ⟨e, ?_, linear_postcomposition_mem_atlas c hc A, ?_⟩
  · change f x ∈ (b.restr U).source
    rw [b.restr_source' U hU]
    exact ⟨hfx, hxO, hfx, hxT⟩
  · intro y hy
    have hy' : y ∈ b.source ∩ U := by
      change y ∈ (b.restr U).source at hy
      rwa [b.restr_source' U hU] at hy
    change y ∈ range f ↔ (A (b y)) 2 = 0 ∧ (A (b y)) 3 = 0
    rw [hAaxis]
    constructor
    · intro hyr
      obtain ⟨z, hz, rfl⟩ := himage.symm ▸ (show y ∈ O ∩ range f from ⟨hy'.2.1, hyr⟩)
      rw [hchart z hz, L.symm_apply_apply]
    · intro hyn
      let u := (L.symm (b y)).1
      have hu : u ∈ a.target := hy'.2.2.2
      have hz : a.symm u ∈ a.source := a.map_target hu
      have hb : b (f (a.symm u)) = b y := by
        rw [hchart _ hz, a.right_inv hu]
        have heq : (u, (0 : h.complement)) = L.symm (b y) :=
          Prod.ext rfl hyn.symm
        rw [heq, L.apply_symm_apply]
      exact ⟨a.symm u, b.injOn (h.source_subset_preimage_source hz) hy'.1 hb⟩

/-- In adapted coordinates the image of the local nodal set is precisely the
intersection of the chart target with the standard axis. -/
theorem exists_adapted_chart_image {f : S → M}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (x : S) :
    ∃ e : OpenPartialHomeomorph M Covector,
      f x ∈ e.source ∧ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M ∧
      e '' (range f ∩ e.source) = e.target ∩ {v | v 2 = 0 ∧ v 3 = 0} := by
  obtain ⟨e, hx, he, haxis⟩ := exists_adapted_chart hf x
  refine ⟨e, hx, he, ?_⟩
  ext v
  constructor
  · rintro ⟨y, ⟨hyf, hys⟩, rfl⟩
    exact ⟨e.map_source hys, (haxis y hys).mp hyf⟩
  · rintro ⟨hvt, hvaxis⟩
    have hys := e.map_target hvt
    refine ⟨e.symm v, ⟨(haxis _ hys).mpr ?_, hys⟩, e.right_inv hvt⟩
    simpa only [e.right_inv hvt] using (show v 2 = 0 ∧ v 3 = 0 from hvaxis)

end FoliationQM.EmbeddedNodalCoordinates
