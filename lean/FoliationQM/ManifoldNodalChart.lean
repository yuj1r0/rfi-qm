module

public import FoliationQM.LocallyFlatWeakKG

/-!
# The nodal surface in the charts of a four-manifold

Source: v13 `thm:wallstrom` Part(c), the weak-derivative, `H¹_loc` and weak
equation conclusions "across all of `𝓜`", component kinds C and D. Let `𝓜` be
a smooth four-manifold, `𝒩` the closed image of a smooth embedding of a
surface, and `c` any chart of the maximal atlas. The part of `𝒩` in the chart
domain is, in the chart image, closed relative to it and locally a
codimension-two axis. Hence, for a field `Ψ` on `𝓜` differentiable off `𝒩`
whose chart representative `Ψ ∘ c⁻¹` is square integrable with
square-integrable coordinate derivatives on a subset `U` of the chart image:

* the weak directional-derivative identity holds against every smooth compact
  test supported in `U`, and every smooth compact localization is in `H¹`;
* if `Ψ` is twice continuously differentiable off `𝒩` and its representative
  solves the curvature-coupled Klein–Gordon equation of a coordinate metric on
  `U` off `𝒩`, the weak equation holds against every such test;
* a twice continuously differentiable representative almost everywhere equal
  to it on an open `U` agrees with it off `𝒩`, solves the equation on `U`,
  and vanishes exactly on `𝒩` when a continuous extension of the squared
  modulus does.

Differentiability off `𝒩` is the intrinsic manifold notion. Square
integrability is for coordinate volume in the chart, and tests are supported
in one chart image; a distribution on a manifold is determined by such tests.
The metric is a matrix field in the chart; its compatibility across charts
and the cited Cauchy theorem are separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ManifoldNodalChart

open MeasureTheory Set Manifold LorentzMatrixGroup RNCVolumeDensity RealLorentzFrame
open CurvedKGFirstVariation CurvedKGTestResidual RNCCoordinateConnection LocallyFlatNodalSet
open ProductTubeCoordinates TemperedDistribution
open scoped ContDiff Topology Manifold SchwartzMap Matrix.Norms.Operator

local notation "Space" => WithLp 2 (ℂ × ℂ)

variable {S M : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace M]

/-- The part of a subset of the manifold lying in a chart domain, in the
coordinates of that chart. -/
def chartSet (c : OpenPartialHomeomorph M Covector) (𝒩 : Set M) : Set Covector :=
  c '' (𝒩 ∩ c.source)

/-- A point of the chart image lies in the coordinate nodal set exactly when
the corresponding point of the manifold lies in the nodal set. -/
theorem mem_chartSet_iff {c : OpenPartialHomeomorph M Covector} {𝒩 : Set M} {y : Covector}
    (hy : y ∈ c.target) : y ∈ chartSet c 𝒩 ↔ c.symm y ∈ 𝒩 := by
  constructor
  · rintro ⟨x, ⟨hx, hxs⟩, rfl⟩
    rwa [c.left_inv hxs]
  · intro h
    exact ⟨c.symm y, ⟨h, c.map_target hy⟩, c.right_inv hy⟩

/-- Removing the coordinate nodal set from a subset of the chart image. -/
theorem mem_sdiff_chartSet_iff {c : OpenPartialHomeomorph M Covector} {𝒩 : Set M}
    {U : Set Covector} (hU : U ⊆ c.target) {y : Covector} :
    y ∈ U \ chartSet c 𝒩 ↔ y ∈ U ∧ c.symm y ∉ 𝒩 :=
  ⟨fun h => ⟨h.1, fun hn => h.2 ((mem_chartSet_iff (hU h.1)).mpr hn)⟩,
    fun h => ⟨h.1, fun hn => h.2 ((mem_chartSet_iff (hU h.1)).mp hn)⟩⟩

variable [ChartedSpace Covector M]

variable {c : OpenPartialHomeomorph M Covector} {Ψ u : M → ℂ} {y : Covector}

/-- A field differentiable at a point of the manifold has a differentiable
representative in every chart of the maximal atlas. -/
theorem differentiableAt_repr (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M)
    (hy : y ∈ c.target) (h : MDifferentiableAt 𝓘(ℝ, Covector) 𝓘(ℝ, ℂ) Ψ (c.symm y)) :
    DifferentiableAt ℝ (Ψ ∘ c.symm) y := by
  have hs : MDifferentiableAt 𝓘(ℝ, Covector) 𝓘(ℝ, Covector) c.symm y :=
    ((contMDiffOn_symm_of_mem_maximalAtlas hc).contMDiffAt
      (c.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  exact mdifferentiableAt_iff_differentiableAt.mp (h.comp y hs)

/-- A field twice continuously differentiable at a point of the manifold has
a twice continuously differentiable representative in every chart of the
maximal atlas. -/
theorem contDiffAt_repr (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M)
    (hy : y ∈ c.target) (h : ContMDiffAt 𝓘(ℝ, Covector) 𝓘(ℝ, ℂ) 2 Ψ (c.symm y)) :
    ContDiffAt ℝ 2 (Ψ ∘ c.symm) y := by
  have hs : ContMDiffAt 𝓘(ℝ, Covector) 𝓘(ℝ, Covector) 2 c.symm y :=
    ((contMDiffOn_symm_of_mem_maximalAtlas hc).contMDiffAt
      (c.open_target.mem_nhds hy)).of_le (by simp)
  exact contMDiffAt_iff_contDiffAt.mp (h.comp y hs)

variable [IsManifold 𝓘(ℝ, Covector) ∞ M]

/-- In every chart of the maximal atlas, the closed image of a smooth
embedding of a surface is closed relative to the chart image and locally a
codimension-two axis. -/
theorem chart_locallyFlat {f : S → M} (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f)
    (hN : IsClosed (range f)) {c : OpenPartialHomeomorph M Covector}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M) :
    LocallyFlat (chartSet c (range f)) c.target where
  isOpen := c.open_target
  isOpen_diff := by
    have e : c.target \ chartSet c (range f) = c '' (c.source ∩ (range f)ᶜ) := by
      ext y
      constructor
      · rintro ⟨hy, hn⟩
        exact ⟨c.symm y, ⟨c.map_target hy, fun hr => hn ((mem_chartSet_iff hy).mpr hr)⟩,
          c.right_inv hy⟩
      · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
        refine ⟨c.map_source hx, fun hmem => hn ?_⟩
        have h := (mem_chartSet_iff (c.map_source hx)).mp hmem
        rwa [c.left_inv hx] at h
    rw [e]
    exact c.isOpen_image_of_subset_source (c.open_source.inter hN.isOpen_compl) inter_subset_left
  adapted := by
    rintro _ ⟨⟨_, ⟨⟨s, rfl⟩, hsc⟩, rfl⟩, -⟩
    obtain ⟨e, hse, he, haxis⟩ := EmbeddedNodalCoordinates.exists_adapted_chart hf s
    refine ⟨c.symm.trans e, ⟨c.map_source hsc, ?_⟩, ?_, ?_, ?_⟩
    · change c.symm (c (f s)) ∈ e.source
      rwa [c.left_inv hsc]
    · exact ((contMDiffOn_of_mem_maximalAtlas he).comp'
        (contMDiffOn_symm_of_mem_maximalAtlas hc)).contDiffOn
    · exact ((contMDiffOn_of_mem_maximalAtlas hc).comp'
        (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn
    · intro y hy
      have hyt : y ∈ c.target := hy.1
      rw [mem_chartSet_iff hyt]
      exact haxis (c.symm y) hy.2

variable {f : S → M} {U K : Set Covector} {φ η : Covector → ℂ}

/-- In every chart of a four-manifold, the classical directional derivative of
the chart representative off a closed embedded nodal surface is its weak
directional derivative across the surface. -/
theorem chart_weak_directional_identity
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hU : U ⊆ c.target) (hψ : MemLp (Ψ ∘ c.symm) 2 (volume.restrict U))
    (hdiff : ∀ x, x ∉ range f → MDifferentiableAt 𝓘(ℝ, Covector) 𝓘(ℝ, ℂ) Ψ x)
    (v : Covector) (hD : MemLp (fun z => fderiv ℝ (Ψ ∘ c.symm) z v) 2 (volume.restrict U)) :
    Integrable (fun z => star (fderiv ℝ φ z v) * (Ψ ∘ c.symm) z) volume ∧
    Integrable (fun z => star (φ z) * fderiv ℝ (Ψ ∘ c.symm) z v) volume ∧
    (∫ z, star (fderiv ℝ φ z v) * (Ψ ∘ c.symm) z) =
      -(∫ z, star (φ z) * fderiv ℝ (Ψ ∘ c.symm) z v) :=
  (chart_locallyFlat hf hN hc).weak_directional_identity hφ hcφ hs hU hψ
    (fun _ hz => differentiableAt_repr hc (hU hz.1)
      (hdiff _ ((mem_sdiff_chartSet_iff hU).mp hz).2)) v hD

/-- In every chart of a four-manifold, every smooth compact localization of
the chart representative is in `H¹`: the field is in `H¹_loc` across the
nodal surface. -/
theorem chart_localized_memSobolev
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M)
    (hK : MeasurableSet K) (hKc : K ⊆ c.target)
    (hψ : MemLp (Ψ ∘ c.symm) 2 (volume.restrict K))
    (hdiff : ∀ x, x ∉ range f → MDifferentiableAt 𝓘(ℝ, Covector) 𝓘(ℝ, ℂ) Ψ x)
    (hD : ∀ i : Fin 4,
      MemLp (fun z => fderiv ℝ (Ψ ∘ c.symm) z (axis i)) 2 (volume.restrict K))
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ K) :
    ∃ hm : MemLp (fun z : Space => η (coordinates.symm z) *
        (Ψ ∘ c.symm) (coordinates.symm z)) 2 volume,
      MemSobolev 1 2 (hm.toLp _ : 𝓢'(Space, ℂ)) :=
  (chart_locallyFlat hf hN hc).localized_memSobolev hK hKc hψ
    (fun _ hz => differentiableAt_repr hc (hKc hz.1)
      (hdiff _ ((mem_sdiff_chartSet_iff hKc).mp hz).2)) hD hη hcη hsη

variable (p : MassiveParameters) {g : Covector → Mat4}

/-- In every chart of a four-manifold, a field that solves the
curvature-coupled Klein–Gordon equation of a coordinate metric off a closed
embedded nodal surface solves the weak equation across the surface. -/
theorem chart_weak_equation
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M) (hU : U ⊆ c.target)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hg : ∀ z ∈ U, ContDiffAt ℝ 2 g z) (hd : ∀ z ∈ U, (g z).det < 0)
    (hψ : MemLp (Ψ ∘ c.symm) 2 (volume.restrict U))
    (hD : ∀ j : Fin 4,
      MemLp (fun z => fderiv ℝ (Ψ ∘ c.symm) z (axis j)) 2 (volume.restrict U))
    (hψoff : ∀ x, x ∉ range f → ContMDiffAt 𝓘(ℝ, Covector) 𝓘(ℝ, ℂ) 2 Ψ x)
    (hKG : ∀ z ∈ U, c.symm z ∉ range f → kgOperator p g (Ψ ∘ c.symm) z = 0) :
    Integrable (fun z => volumeFactor (g z) • cross p g φ (Ψ ∘ c.symm) z) volume ∧
    (∫ z, volumeFactor (g z) • cross p g φ (Ψ ∘ c.symm) z) = 0 :=
  LocallyFlatWeakKG.weak_equation p (chart_locallyFlat hf hN hc) hU hφ hcφ hs hg hd hψ hD
    (fun _ hz => contDiffAt_repr hc (hU hz.1) (hψoff _ ((mem_sdiff_chartSet_iff hU).mp hz).2))
    (fun z hz => hKG z hz.1 ((mem_sdiff_chartSet_iff hU).mp hz).2)

/-- In every chart of a four-manifold, a twice continuously differentiable
field almost everywhere equal to a solution off the nodal surface agrees with
it off the surface, solves the equation on the whole open set, and vanishes
exactly on the surface when a continuous extension of the squared modulus
does. -/
theorem chart_continuation
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) ∞ M) (hUo : IsOpen U) (hU : U ⊆ c.target)
    (hg : ∀ z ∈ U, ContDiffAt ℝ 2 g z) (hd : ∀ z ∈ U, (g z).det < 0)
    (hψoff : ∀ x, x ∉ range f → ContMDiffAt 𝓘(ℝ, Covector) 𝓘(ℝ, ℂ) 2 Ψ x)
    (hKG : ∀ z ∈ U, c.symm z ∉ range f → kgOperator p g (Ψ ∘ c.symm) z = 0)
    (hu : ∀ z ∈ U, ContDiffAt ℝ 2 (u ∘ c.symm) z)
    (hae : (u ∘ c.symm) =ᵐ[volume.restrict U] (Ψ ∘ c.symm))
    {ρ : M → ℝ} (hρ : ContinuousOn (ρ ∘ c.symm) U)
    (hρψ : ∀ z ∈ U, c.symm z ∉ range f → ρ (c.symm z) = ‖Ψ (c.symm z)‖ ^ 2)
    (hzero : ∀ z ∈ U, ρ (c.symm z) = 0 ↔ c.symm z ∈ range f) :
    (∀ z ∈ U, c.symm z ∉ range f → u (c.symm z) = Ψ (c.symm z)) ∧
    (∀ z ∈ U, kgOperator p g (u ∘ c.symm) z = 0) ∧
    (∀ z ∈ U, ‖u (c.symm z)‖ ^ 2 = ρ (c.symm z)) ∧
    ∀ z ∈ U, u (c.symm z) = 0 ↔ c.symm z ∈ range f := by
  obtain ⟨heq, hop, hsq, hzr⟩ := LocallyFlatWeakKG.continuation p (chart_locallyFlat hf hN hc)
    hUo hU hg hd
    (fun _ hz => contDiffAt_repr hc (hU hz.1) (hψoff _ ((mem_sdiff_chartSet_iff hU).mp hz).2))
    (fun z hz => hKG z hz.1 ((mem_sdiff_chartSet_iff hU).mp hz).2) hu hae hρ
    (fun z hz => hρψ z hz.1 ((mem_sdiff_chartSet_iff hU).mp hz).2)
    (fun z hz => (hzero z hz).trans (mem_chartSet_iff (hU hz)).symm)
  exact ⟨fun z hz hn => heq ((mem_sdiff_chartSet_iff hU).mpr ⟨hz, hn⟩), hop, hsq,
    fun z hz => (hzr z hz).trans (mem_chartSet_iff (hU hz))⟩

end FoliationQM.ManifoldNodalChart
