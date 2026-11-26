module

public import FoliationQM.EmbeddedNodalPolarExtension
public import FoliationQM.LocalizedCoordinateSobolev

/-!
# Localized Sobolev regularity across a closed embedded nodal surface

Source: v13 `thm:wallstrom` Part(c) with `eq:positive_h_energy`: "`ψ` admits
a unique almost-everywhere `H¹_loc` extension", component kinds C and D. Let
`𝒩` be the closed image of a smooth embedding of a surface in coordinate
four-space. A field that is square integrable on a measurable set `K`
together with its coordinate derivatives, and differentiable on `K` off `𝒩`,
has every smooth compact localization supported in `K` in the Fourier–Bessel
Sobolev space `H¹` of the Euclidean product space, after transport by the
volume-preserving coordinate equivalence. Finite positive auxiliary-metric
polar energy off `𝒩` supplies these data, so every localization of the polar
field `ψ = R q` supported in the region is in `H¹`.

No weak derivative identity, chart, cutoff estimate or Sobolev membership is
assumed. The values of the field on the null set `𝒩` are irrelevant. An
abstract four-manifold ambient and the Cauchy continuation are separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.EmbeddedNodalSobolev

open MeasureTheory Set Manifold LorentzMatrixGroup RNCCoordinateConnection
open AuxiliaryMetricEnergy CirclePolarEnergy ProductTubeCoordinates TemperedDistribution
open scoped ContDiff Topology Manifold SchwartzMap Matrix.Norms.Operator

local notation "Space" => WithLp 2 (ℂ × ℂ)

variable {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {f : S → Covector}

/-- Square-integrable field and derivative data, differentiable off a closed
embedded surface, give `H¹` membership of every smooth compact localization. -/
theorem localized_memSobolev
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    {K : Set Covector} {ψ η : Covector → ℂ} (hK : MeasurableSet K)
    (hψ : MemLp ψ 2 (volume.restrict K))
    (hdiff : ∀ x ∈ K \ range f, DifferentiableAt ℝ ψ x)
    (hD : ∀ i : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis i)) 2 (volume.restrict K))
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ K) :
    ∃ hm : MemLp (fun y : Space => η (coordinates.symm y) * ψ (coordinates.symm y)) 2 volume,
      MemSobolev 1 2 (hm.toLp _ : 𝓢'(Space, ℂ)) :=
  LocalizedCoordinateSobolev.localized_memSobolev hK hψ hD
    (fun hφ hc hs v =>
      EmbeddedNodalGlobalWeakDerivative.weak_directional_identity hf hN hφ hc hs hψ hdiff v
        (EmbeddedNodalPolarExtension.memLp_fderiv_apply hD v))
    hη hcη hsη

variable {K U : Set Covector} {H : Covector → Mat4} {R : Covector → ℝ} {q : Covector → ℂ}
  {dR α : Covector → Covector →L[ℝ] ℝ} {omega : ℝ}

/-- Finite positive polar energy off a closed embedded nodal surface gives
`H¹` membership of every smooth compact localization of the polar field. -/
theorem polar_localized_memSobolev
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    (hK : IsCompact K) (hH : ContinuousOn H K) (hpos : ∀ x ∈ K, (H x).PosDef)
    (hR : ∀ x ∈ K \ range f, HasFDerivAt R (dR x) x)
    (hq : ∀ x ∈ K \ range f,
      HasFDerivAt q ((α x).smulRight (-Complex.I * (omega : ℂ) * q x)) x)
    (hunit : ∀ x ∈ K \ range f, ‖q x‖ = 1)
    (he : Integrable (fun x => (R x) ^ 2 +
      realEnergy (H x) (fun i => dR x (axis i)) +
      omega ^ 2 * (R x) ^ 2 * realEnergy (H x) (fun i => α x (axis i)))
      ((volume.restrict (K \ range f)).withDensity
        (fun x => ENNReal.ofReal (density (H x)))))
    {η : Covector → ℂ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ K) :
    ∃ hm : MemLp (fun y : Space => η (coordinates.symm y) *
        field R q (coordinates.symm y)) 2 volume,
      MemSobolev 1 2 (hm.toLp _ : 𝓢'(Space, ℂ)) := by
  obtain ⟨hψ, hD, hweak⟩ :=
    EmbeddedNodalPolarExtension.polar_weak_extension hf hN hK hH hpos hR hq hunit he
  exact LocalizedCoordinateSobolev.localized_memSobolev hK.measurableSet hψ
    (fun i => hD (axis i)) hweak hη hcη hsη

/-- Positive polar energy on every compact subset of a region gives `H¹`
membership of every smooth compact localization supported in the region: the
polar field is in `H¹_loc` across the nodal surface. -/
theorem polar_localizations_memSobolev
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    (hH : ContinuousOn H U) (hpos : ∀ x ∈ U, (H x).PosDef)
    (hR : ∀ x ∈ U \ range f, HasFDerivAt R (dR x) x)
    (hq : ∀ x ∈ U \ range f,
      HasFDerivAt q ((α x).smulRight (-Complex.I * (omega : ℂ) * q x)) x)
    (hunit : ∀ x ∈ U \ range f, ‖q x‖ = 1)
    (he : ∀ K : Set Covector, IsCompact K → K ⊆ U →
      Integrable (fun x => (R x) ^ 2 +
        realEnergy (H x) (fun i => dR x (axis i)) +
        omega ^ 2 * (R x) ^ 2 * realEnergy (H x) (fun i => α x (axis i)))
        ((volume.restrict (K \ range f)).withDensity
          (fun x => ENNReal.ofReal (density (H x)))))
    {η : Covector → ℂ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ U) :
    ∃ hm : MemLp (fun y : Space => η (coordinates.symm y) *
        field R q (coordinates.symm y)) 2 volume,
      MemSobolev 1 2 (hm.toLp _ : 𝓢'(Space, ℂ)) :=
  polar_localized_memSobolev hf hN hcη.isCompact (hH.mono hsη) (fun x hx => hpos x (hsη hx))
    (fun x hx => hR x ⟨hsη hx.1, hx.2⟩) (fun x hx => hq x ⟨hsη hx.1, hx.2⟩)
    (fun x hx => hunit x ⟨hsη hx.1, hx.2⟩) (he (tsupport η) hcη.isCompact hsη) hη hcη
    subset_rfl

end FoliationQM.EmbeddedNodalSobolev
