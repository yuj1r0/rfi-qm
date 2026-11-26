module

public import FoliationQM.EmbeddedNodalWeakKG
public import FoliationQM.WeightedPolarEnergyL2

/-!
# Weak extension of polar data across a closed embedded nodal surface

Source: v13 `thm:wallstrom` Part(c) with `eq:positive_h_energy`: "`ψ` admits
a unique almost-everywhere `H¹_loc` extension satisfying `Pψ = 0`
distributionally", component kinds C and D. Let `𝒩` be the closed image of a
smooth embedding of a surface in coordinate four-space and `H` a continuous
positive-definite auxiliary metric on a compact set `K`. An amplitude `R` and
a unit circle phase `q` with the clock differential relation on `K` off `𝒩`,
whose positive `H`-energy `R² + |dR|²_H + ω²R²|α|²_H` is integrable for the
`H`-volume on `K` off `𝒩`, give a field `ψ = R q` that is square integrable
on `K` together with all its directional derivatives and satisfies the weak
directional-derivative identity against every smooth compact test supported
in `K`. If in addition `ψ` is twice continuously differentiable and solves
the curvature-coupled Klein–Gordon equation on `K` off `𝒩` for a twice
continuously differentiable Lorentzian metric, the weak equation holds for
every such test.

The values of `R` and `q` on the null set `𝒩` are irrelevant. Statements are
in ambient coordinates with coordinate volume; Hilbert Sobolev membership, an
abstract four-manifold ambient and the Cauchy continuation are separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.EmbeddedNodalPolarExtension

open MeasureTheory Set Manifold LorentzMatrixGroup RNCVolumeDensity RNCCoordinateConnection
open AuxiliaryMetricEnergy CirclePolarEnergy CurvedKGFirstVariation CurvedKGTestResidual
open RealLorentzFrame
open scoped ContDiff Topology Manifold Matrix.Norms.Operator

/-- Square integrability of the coordinate derivatives gives square
integrability of every directional derivative. -/
theorem memLp_fderiv_apply {μ : Measure Covector} {ψ : Covector → ℂ}
    (hD : ∀ i : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis i)) 2 μ) (v : Covector) :
    MemLp (fun x => fderiv ℝ ψ x v) 2 μ := by
  have h : (fun x => fderiv ℝ ψ x v) = fun x => ∑ i, v i • fderiv ℝ ψ x (axis i) := by
    funext x
    have h1 : v = ∑ i, v i • axis i := by
      ext j
      simp [RNCCoordinateConnection.axis, Pi.single_apply, Finset.sum_apply]
    conv_lhs => rw [h1]
    simp [map_sum, map_smul]
  rw [h]
  exact memLp_finsetSum _ fun i _ => (hD i).const_smul (v i)

variable {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {f : S → Covector}
  {K : Set Covector} {H : Covector → Mat4} {R : Covector → ℝ} {q : Covector → ℂ}
  {dR α : Covector → Covector →L[ℝ] ℝ} {omega : ℝ}

/-- Finite positive auxiliary-metric polar energy off a closed embedded nodal
surface gives square-integrable field and derivative data on the whole compact
set and the weak directional-derivative identity across the surface. -/
theorem polar_weak_extension
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
        (fun x => ENNReal.ofReal (density (H x))))) :
    MemLp (field R q) 2 (volume.restrict K) ∧
    (∀ v : Covector, MemLp (fun x => fderiv ℝ (field R q) x v) 2 (volume.restrict K)) ∧
    ∀ {φ : Covector → ℂ}, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      ∀ v : Covector,
      Integrable (fun x => star (fderiv ℝ φ x v) * field R q x) volume ∧
      Integrable (fun x => star (φ x) * fderiv ℝ (field R q) x v) volume ∧
      (∫ x, star (fderiv ℝ φ x v) * field R q x) =
        -(∫ x, star (φ x) * fderiv ℝ (field R q) x v) := by
  have hnull := EmbeddedNodalNullity.volume_range_eq_zero hf
  have hμ : volume.restrict (K \ range f) = volume.restrict K :=
    Measure.restrict_congr_set (sdiff_null_ae_eq_self hnull)
  have hS : MeasurableSet (K \ range f) := hK.measurableSet.diff hN.measurableSet
  obtain ⟨hψ, hD⟩ := WeightedPolarEnergyL2.polar_memLp hK hS sdiff_subset hH hpos hR hq hunit he
  rw [hμ] at hψ
  have hD' (v : Covector) : MemLp (fun x => fderiv ℝ (field R q) x v) 2 (volume.restrict K) :=
    memLp_fderiv_apply (fun i => hμ ▸ hD i) v
  have hdiff : ∀ x ∈ K \ range f, DifferentiableAt ℝ (field R q) x := fun x hx =>
    (hasFDerivAt_field (hR x hx) (hq x hx)).differentiableAt
  exact ⟨hψ, hD', fun hφ hc hs v =>
    EmbeddedNodalGlobalWeakDerivative.weak_directional_identity hf hN hφ hc hs hψ hdiff v
      (hD' v)⟩

/-- If the polar field moreover solves the curvature-coupled Klein–Gordon
equation off the nodal surface, the weak equation holds across it. -/
theorem polar_weak_equation (p : MassiveParameters) {g : Covector → Mat4}
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
    (hg : ∀ x ∈ K, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ K, (g x).det < 0)
    (hψ2 : ∀ x ∈ K \ range f, ContDiffAt ℝ 2 (field R q) x)
    (hKG : ∀ x ∈ K \ range f, kgOperator p g (field R q) x = 0)
    {φ : Covector → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ K) :
    Integrable (fun x => volumeFactor (g x) • cross p g φ (field R q) x) volume ∧
    (∫ x, volumeFactor (g x) • cross p g φ (field R q) x) = 0 := by
  obtain ⟨hψ, hD, -⟩ := polar_weak_extension hf hN hK hH hpos hR hq hunit he
  exact EmbeddedNodalWeakKG.weak_equation p hf hN hφ hc hs hg hd hψ (fun j => hD (axis j))
    hψ2 hKG

end FoliationQM.EmbeddedNodalPolarExtension
