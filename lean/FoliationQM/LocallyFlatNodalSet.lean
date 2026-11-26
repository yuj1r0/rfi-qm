module

public import FoliationQM.EmbeddedNodalSobolev

/-!
# Weak derivatives across a locally flat nodal set in an open coordinate domain

Source: v13 `thm:wallstrom` Part(c), the distributional-derivative argument
"showing `ψ ∈ H¹_loc(𝓜)` uniquely", component kinds C and D. The earlier
coordinate theorems take the nodal set to be the closed image of a smooth
embedding in all of coordinate four-space. In a chart of a four-manifold only
the part of the nodal surface inside the chart is visible: a subset `N` of the
open chart image `V` that is closed relative to `V` and that a smooth
coordinate change sends, near each of its points, to the standard
codimension-two axis. This module proves the same conclusions for such a pair
`(N, V)`: zero volume of `N ∩ V`, the weak directional-derivative identity
for tests supported in a subset of `V`, the same identity for a
square-integrable differential representative, and `H¹` membership of every
smooth compact localization.

The closed image of a smooth embedding in coordinate four-space is the case
`V = univ`. The statements are in coordinates with coordinate volume; the
chart of a manifold that produces `(N, V)` and the wave equation are separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LocallyFlatNodalSet

open MeasureTheory Set Manifold RealLorentzFrame AdaptedChartWeakDerivative
open EmbeddedNodalGlobalWeakDerivative RNCCoordinateConnection ProductTubeCoordinates
open TemperedDistribution
open scoped ContDiff Topology Manifold ComplexConjugate SchwartzMap

local notation "Space" => WithLp 2 (ℂ × ℂ)

/-- The set `N` is closed relative to the open set `V`, and near each point of
`N` in `V` a smooth coordinate change sends `N` to the standard
codimension-two axis. -/
structure LocallyFlat (N V : Set Covector) : Prop where
  isOpen : IsOpen V
  isOpen_diff : IsOpen (V \ N)
  adapted : ∀ x ∈ N ∩ V, ∃ e : OpenPartialHomeomorph Covector Covector, x ∈ e.source ∧
    ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
    ∀ y ∈ e.source, y ∈ N ↔ (e y) 2 = 0 ∧ (e y) 3 = 0

variable {N V U K : Set Covector} {φ ψ η : Covector → ℂ}

/-- The closed image of a smooth embedding of a surface in coordinate
four-space is locally flat in the whole space. -/
theorem of_embedding {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {f : S → Covector}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f)) :
    LocallyFlat (range f) univ where
  isOpen := isOpen_univ
  isOpen_diff := isOpen_univ.sdiff hN
  adapted := by
    rintro _ ⟨⟨s, rfl⟩, -⟩
    obtain ⟨e, hs, he, haxis⟩ := EmbeddedNodalCoordinates.exists_adapted_chart hf s
    exact ⟨e, hs, (contMDiffOn_of_mem_maximalAtlas he).contDiffOn,
      (contMDiffOn_symm_of_mem_maximalAtlas he).contDiffOn, haxis⟩

/-- A locally flat set restricts to every smaller open domain. -/
theorem LocallyFlat.mono (h : LocallyFlat N V) {W : Set Covector} (hW : IsOpen W)
    (hWV : W ⊆ V) : LocallyFlat N W where
  isOpen := hW
  isOpen_diff := by
    have e : W \ N = W ∩ (V \ N) := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hWV hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
    rw [e]
    exact hW.inter h.isOpen_diff
  adapted := fun x hx => h.adapted x ⟨hx.1, hWV hx.2⟩

/-- The part of a locally flat set inside its domain has zero volume. -/
theorem LocallyFlat.volume_inter_eq_zero (h : LocallyFlat N V) : volume (N ∩ V) = 0 := by
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨e, hxe, -, hi, haxis⟩ := h.adapted x hx
  refine ⟨N ∩ e.source, ?_, ?_⟩
  · exact Filter.mem_of_superset (inter_mem_nhdsWithin _ (e.open_source.mem_nhds hxe))
      fun y hy => ⟨hy.1.1, hy.2⟩
  · let t : Set Covector := e.target ∩ {v | v 2 = 0 ∧ v 3 = 0}
    have hdiff : DifferentiableOn ℝ e.symm t :=
      (hi.differentiableOn (by simp)).mono inter_subset_left
    have hnull : volume t = 0 :=
      measure_mono_null inter_subset_right SmoothCoordinateTubeCutoff.axis_null
    refine measure_mono_null ?_
      (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hnull)
    rintro y ⟨hyN, hye⟩
    exact ⟨e y, ⟨e.map_source hye, (haxis y hye).mp hyN⟩, e.left_inv hye⟩

/-- Removing the nodal set from a subset of the domain removes nothing but its
points in the domain. -/
theorem sdiff_eq (hKV : K ⊆ V) : K \ N = K \ (N ∩ V) := by
  ext x
  exact ⟨fun hx => ⟨hx.1, fun hn => hx.2 hn.1⟩, fun hx => ⟨hx.1, fun hn => hx.2 ⟨hn, hKV hx.1⟩⟩⟩

/-- Removing the nodal set does not change coordinate volume on a subset of
the domain. -/
theorem LocallyFlat.restrict_sdiff (h : LocallyFlat N V) (hKV : K ⊆ V) :
    volume.restrict (K \ N) = volume.restrict K := by
  rw [sdiff_eq hKV]
  exact Measure.restrict_congr_set (sdiff_null_ae_eq_self h.volume_inter_eq_zero)

/-- Almost every point of a subset of the domain lies off the nodal set. -/
theorem LocallyFlat.ae_notMem (h : LocallyFlat N V) (hK : MeasurableSet K) (hKV : K ⊆ V) :
    ∀ᵐ x ∂volume.restrict K, x ∉ N := by
  have hoff : ∀ᵐ x ∂(volume : Measure Covector), x ∉ N ∩ V :=
    measure_eq_zero_iff_ae_notMem.mp h.volume_inter_eq_zero
  filter_upwards [ae_restrict_mem hK, ae_restrict_of_ae hoff] with x hx hn
  exact fun hN => hn ⟨hN, hKV hx⟩

/-- A subset of the domain with the nodal set removed is measurable when the
subset is. -/
theorem LocallyFlat.measurableSet_sdiff (h : LocallyFlat N V) (hK : MeasurableSet K)
    (hKV : K ⊆ V) : MeasurableSet (K \ N) := by
  have e : K \ N = K ∩ (V \ N) := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hKV hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
  rw [e]
  exact hK.inter h.isOpen_diff.measurableSet

/-- The classical directional derivative off a locally flat nodal set is the
weak directional derivative across it, for every smooth compact test supported
in a subset of the domain. -/
theorem LocallyFlat.weak_directional_identity (h : LocallyFlat N V) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (hUV : U ⊆ V)
    (hψ : MemLp ψ 2 (volume.restrict U))
    (hdiff : ∀ x ∈ U \ N, DifferentiableAt ℝ ψ x) (v : Covector)
    (hD : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict U)) :
    Integrable (fun x => star (fderiv ℝ φ x v) * ψ x) volume ∧
    Integrable (fun x => star (φ x) * fderiv ℝ ψ x v) volume ∧
    (∫ x, star (fderiv ℝ φ x v) * ψ x) = -(∫ x, star (φ x) * fderiv ℝ ψ x v) := by
  have hψK : MemLp ψ 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hψ
  have hDK : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hD
  have Pψ := smooth_pairing hφ hc hψK v
  have PD := smooth_pairing hφ hc hDK v
  refine ⟨(supported_pair (tsupport_fderiv_apply_subset ℝ v) Pψ.2).1,
    (supported_pair (Subset.rfl : tsupport φ ⊆ tsupport φ) PD.1).1, ?_⟩
  refine weak_identity_of_local hφ hc hψK hDK v fun x hx => ?_
  by_cases hxN : x ∈ N
  · obtain ⟨e, hxe, he, hi, haxis⟩ := h.adapted x ⟨hxN, hUV (hs hx)⟩
    exact ⟨e.source, e.open_source, hxe, fun η hη hηc hηK hηW =>
      (AdaptedChartWeakDerivative.weak_directional_identity he hi hη hηc (hηK.trans hs) hηW hψ
        (fun y hy hn => hdiff y ⟨hy.1, fun hr => hn ((haxis y hy.2).mp hr)⟩) v hD).2.2⟩
  · refine ⟨V \ N, h.isOpen_diff, ⟨hUV (hs hx), hxN⟩, fun η hη hηc hηK hηW => ?_⟩
    exact integration_by_parts hη hηc (hηK.trans hs) hψ
      (fun y hy => hdiff y ⟨hs (hηK hy), (hηW hy).2⟩) v hD

/-- A square-integrable differential representative that is the classical
differential off the nodal set is a weak differential across it. -/
theorem LocallyFlat.weak_of_representative (h : LocallyFlat N V)
    {G : Covector → Covector →L[ℝ] ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) (hUV : U ⊆ V) (hψ : MemLp ψ 2 (volume.restrict U))
    (hG : MemLp G 2 (volume.restrict U))
    (hderiv : ∀ x ∈ U \ N, HasFDerivAt ψ (G x) x) (v : Covector) :
    Integrable (fun x => star (fderiv ℝ φ x v) * ψ x) volume ∧
    Integrable (fun x => star (φ x) * G x v) volume ∧
    (∫ x, star (fderiv ℝ φ x v) * ψ x) = -(∫ x, star (φ x) * G x v) := by
  have hK : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hψK : MemLp ψ 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hψ
  have hGK : MemLp G 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hG
  have hGv : MemLp (fun x => G x v) 2 (volume.restrict (tsupport φ)) :=
    (ContinuousLinearMap.apply ℝ ℂ v).comp_memLp' hGK
  have hEq : (fun x => fderiv ℝ ψ x v) =ᵐ[volume.restrict (tsupport φ)] fun x => G x v := by
    filter_upwards [ae_restrict_mem hK, h.ae_notMem hK (hs.trans hUV)] with x hx hn
    exact congrArg (fun L : Covector →L[ℝ] ℂ => L v) (hderiv x ⟨hs hx, hn⟩).fderiv
  have hDK : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict (tsupport φ)) :=
    MemLp.ae_eq hEq.symm hGv
  have H := h.weak_directional_identity hφ hc (Subset.rfl : tsupport φ ⊆ tsupport φ)
    (hs.trans hUV) hψK (fun x hx => (hderiv x ⟨hs hx.1, hx.2⟩).differentiableAt) v hDK
  have hint : (fun x => star (φ x) * fderiv ℝ ψ x v) =ᵐ[volume] fun x => star (φ x) * G x v := by
    filter_upwards [(ae_restrict_iff' hK).mp hEq] with x hx
    by_cases hxK : x ∈ tsupport φ
    · rw [hx hxK]
    · simp only [image_eq_zero_of_notMem_tsupport hxK, star_zero, zero_mul]
  exact ⟨H.1, H.2.1.congr hint, by rw [← integral_congr_ae hint]; exact H.2.2⟩

/-- Square-integrable field and derivative data, differentiable off a locally
flat nodal set, give `H¹` membership of every smooth compact localization
supported in a measurable subset of the domain. -/
theorem LocallyFlat.localized_memSobolev (h : LocallyFlat N V) (hK : MeasurableSet K)
    (hKV : K ⊆ V) (hψ : MemLp ψ 2 (volume.restrict K))
    (hdiff : ∀ x ∈ K \ N, DifferentiableAt ℝ ψ x)
    (hD : ∀ i : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis i)) 2 (volume.restrict K))
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ K) :
    ∃ hm : MemLp (fun y : Space => η (coordinates.symm y) * ψ (coordinates.symm y)) 2 volume,
      MemSobolev 1 2 (hm.toLp _ : 𝓢'(Space, ℂ)) :=
  LocalizedCoordinateSobolev.localized_memSobolev hK hψ hD
    (fun hφ hc hs v => h.weak_directional_identity hφ hc hs hKV hψ hdiff v
      (EmbeddedNodalPolarExtension.memLp_fderiv_apply hD v))
    hη hcη hsη

end FoliationQM.LocallyFlatNodalSet
