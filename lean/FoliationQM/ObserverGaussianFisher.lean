module

public import FoliationQM.GaussianGlobalCauchyData
public import FoliationQM.ObserverFisherProduct
public import FoliationQM.ObserverNormalizedShape

/-!
# A full observer-slice Gaussian with a constant flux factor

V13 Remark 5.2 and supplement lines 299–309 distinguish normalized
density shapes from homogeneous Fisher integrals. On spatial Lebesgue
volume the three Cartesian score directions give a positive, explicitly
computable Fisher trace. A mixed-branch free Klein–Gordon field realizes
any positive constant observer factor on its zero-drift initial slice.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverGaussianFisher

open MeasureTheory LorentzCoordinates GaussianSliceMoments FisherNormalization
open ObserverNormalizedShape OsmoticSliceFields ObserverFluxDensity

/-- The three unit coordinate tangent vectors in the laboratory slice. -/
def axes (i : Fin 3) : Spatial := Pi.single i 1

/-- The Fisher trace in the three laboratory directions is the spatial score norm squared
times the actual density at each point. -/
theorem traceIntegrand_axes (r : Spatial → ℝ) (y : Spatial) :
    traceIntegrand r axes y = r y * speedSq (SpatialFisherEnergy.score r y) := by
  rw [traceIntegrand, Fin.sum_univ_three, speedSq_eq_sum]
  rfl

/-- The trace integrand of a positive-width Gaussian is integrable on the full slice. -/
theorem gaussian_trace_integrable {σ : ℝ} (hσ : 0 < σ) :
    Integrable (traceIntegrand (density σ) axes) := by
  simp_rw [funext (traceIntegrand_axes (density σ))]
  exact integrable_fisher hσ

/-- On three-dimensional Lebesgue volume the unnormalized Gaussian trace is 3Z/σ². -/
theorem gaussian_trace_eq {σ : ℝ} (hσ : 0 < σ) :
    fisherTrace (density σ) axes volume = normalization σ * (3/σ^2) := by
  rw [fisherTrace, funext (traceIntegrand_axes (density σ))]
  exact integral_fisher hσ

/-- Two separate normalizations give the same Gaussian shape and both have unit integral. -/
theorem gaussian_shapes {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    shape volume (fun y => a * density σ y) = shape volume (density σ) ∧
      (∫ y, shape volume (fun x => a * density σ x) y) = 1 ∧
      (∫ y, shape volume (density σ) y) = 1 := by
  have hm : 0 < mass volume (density σ) := by
    rw [mass, integral_density hσ]
    exact normalization_pos hσ
  have hs := shape_const_mul volume (density σ) ha hm
  have hu := integral_shape volume (density σ) (integrable_density hσ) hm
  exact ⟨hs, hs ▸ hu, hu⟩

/-- The constant-factor observer Gaussian has an integrable trace and the exact value a·3Z/σ². -/
theorem scaled_trace_eq {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    Integrable (traceIntegrand (fun y => a*density σ y) axes) ∧
      fisherTrace (fun y => a*density σ y) axes volume = a * (normalization σ * (3/σ^2)) := by
  obtain ⟨hi, ht⟩ := ObserverFisherProduct.fisherTrace_const_mul (ρ := density σ) axes volume ha
    (Filter.Eventually.of_forall fun y =>
      ⟨(smooth_density σ).differentiable (by decide) y, density_pos σ y⟩)
    (gaussian_trace_integrable hσ)
  exact ⟨hi, ht.trans (congrArg (a * ·) (gaussian_trace_eq hσ))⟩

/-- The positive Gaussian's two unnormalized homogeneous Fisher integrals coincide
if and only if the constant observer factor is one. -/
theorem scaled_trace_eq_iff {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    fisherTrace (fun y => a*density σ y) axes volume = fisherTrace (density σ) axes volume ↔
      a = 1 := by
  rw [(scaled_trace_eq hσ ha).2, gaussian_trace_eq hσ]
  have hp : 0 < normalization σ * (3/σ^2) := mul_pos (normalization_pos hσ) (by positivity)
  constructor
  · intro he
    exact mul_right_cancel₀ hp.ne' (he.trans (one_mul _).symm)
  · rintro rfl
    exact one_mul _

/-- A global free two-branch field realizes the Gaussian and its scaled observer flux
on a future-timelike initial slice with vanishing spatial drift. -/
theorem realized_slice (p : MassiveParameters) {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    let ψ := GaussianMixedCauchyWave.wave p σ 0 (a*p.m*p.c/p.hbar)
    let S := GaussianGlobalCauchyData.action p ψ
    GaussianGlobalCauchyData.density ψ ∘ slicePoint 0 = density σ ∧
      labDensity p ψ ∘ slicePoint 0 = (fun y => a*density σ y) ∧
      ∀ y, phaseDrift p.c S (slicePoint 0 y) = 0 ∧
        0 < minkowski (DressedMassDensityVariation.phaseDifferential S (slicePoint 0 y))
          (DressedMassDensityVariation.phaseDifferential S (slicePoint 0 y)) := by
  let freq := a*p.m*p.c/p.hbar
  have hf : 0 < freq := div_pos (mul_pos (mul_pos ha p.m_pos) p.c_pos) p.hbar_pos
  have hd := GaussianGlobalCauchyData.realized p hσ hf 0
  refine ⟨GaussianSliceCoercivity.density_eq hd, ?_, fun y =>
    ⟨(GaussianSliceCoercivity.slice_values hd y).1, (GaussianSliceCoercivity.future_timelike hd y).2⟩⟩
  funext y
  let ψ := GaussianMixedCauchyWave.wave p σ 0 freq
  change labDensity p ψ (slicePoint 0 y) = _
  rw [← GaussianGlobalCauchyData.reconstruct p ψ, labDensity_polar p
    ((hd.density_regular y).differentiableAt (by norm_num))
    ((hd.phase_regular y).differentiableAt (by norm_num)) (hd.density_pos y)]
  rw [(GaussianCauchySlice.normal_data p ((hd.density_regular y).differentiableAt (by norm_num))
    ((hd.phase_regular y).differentiableAt (by norm_num)) (hd.density_pos y) 0 freq
    (hd.initial_derivative y)).2]
  change GaussianGlobalCauchyData.density ψ (slicePoint 0 y) * (p.hbar*freq)/(p.m*p.c) = _
  have hy : GaussianGlobalCauchyData.density ψ (slicePoint 0 y) = density σ y :=
    congrFun (GaussianSliceCoercivity.density_eq hd) y
  rw [hy]
  dsimp only [freq]
  field_simp [p.hbar_pos.ne', p.m_pos.ne', p.c_pos.ne']

/-- The actual modulus and measured flux of the same free field have identical normalized
shapes and different full-slice Fisher integrals for every a > 0 distinct from one. -/
theorem realized_shape_and_unequal_trace (p : MassiveParameters) {σ a : ℝ}
    (hσ : 0 < σ) (ha : 0 < a) (hne : a ≠ 1) :
    let ψ := GaussianMixedCauchyWave.wave p σ 0 (a*p.m*p.c/p.hbar)
    let obs := labDensity p ψ ∘ slicePoint 0
    let inv := GaussianGlobalCauchyData.density ψ ∘ slicePoint 0
    shape volume obs = shape volume inv ∧ fisherTrace obs axes volume ≠ fisherTrace inv axes volume := by
  dsimp only
  obtain ⟨hi, ho, _⟩ := realized_slice p hσ ha
  rw [hi, ho]
  exact ⟨(gaussian_shapes hσ ha).1, fun he => hne ((scaled_trace_eq_iff hσ ha).mp he)⟩

end FoliationQM.ObserverGaussianFisher
