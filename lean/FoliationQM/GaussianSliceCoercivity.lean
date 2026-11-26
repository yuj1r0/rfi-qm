module

public import FoliationQM.GaussianCauchySlice
public import FoliationQM.GaussianSliceMoments
public import FoliationQM.SpacelikeOsmoticIntegral

/-!
# Exact initial-slice coercivity criterion for Gaussian Cauchy data

For v13 `eq:dilatation_coercivity_bound` and `eq:spacelike_coercivity`,
we evaluate both physical terms over the entire laboratory slice. The
complex initial field has real Gaussian amplitude, and its independently
prescribed normal derivative is (K−iω)ψ. The optimal speed bound is zero,
since the actual drift vanishes everywhere on this slice.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianSliceCoercivity

open MeasureTheory LorentzCoordinates OsmoticSliceFields ObserverFluxDensity
open GaussianSliceMoments GaussianCauchySlice SpacelikeOsmoticIntegral WeightedOsmoticCoercivity
open DressedMassDensityVariation ActionDensity PolarSecondDifferential

/-- A regular polar field on the initial slice with the free KG equation and two
prescribed Cauchy data. The width and the real normal amplitude rate are independent inputs. -/
structure SliceData (p : MassiveParameters) (ρ S : Covector → ℝ) (σ K freq : ℝ) : Prop where
  width_pos : 0 < σ
  frequency_pos : 0 < freq
  density_regular : ∀ y, ContDiffAt ℝ 2 ρ (slicePoint 0 y)
  phase_regular : ∀ y, ContDiffAt ℝ 2 S (slicePoint 0 y)
  density_pos : ∀ y, 0 < ρ (slicePoint 0 y)
  initial_value : ∀ y, actionField p ρ S (slicePoint 0 y) = (amplitude σ y : ℂ)
  initial_derivative : ∀ y,
    directionalDerivative (actionField p ρ S) (Madelung.coordinateVector 0) (slicePoint 0 y)
      = actionField p ρ S (slicePoint 0 y) * ((K : ℂ) - Complex.I * freq)
  kg : ∀ y, box (actionField p ρ S) Madelung.coordinateVector (slicePoint 0 y) +
    (((p.m^2*p.c^2/p.hbar^2 : ℝ) : ℂ) * actionField p ρ S (slicePoint 0 y)) = 0

/-- The source's strict weighted inequality on the full initial slice for a specified speed bound. -/
def DilatationBound (p : MassiveParameters) (ρ S : Covector → ℝ) (V : ℝ) : Prop :=
  weightedNorm volume (ρ ∘ slicePoint 0) (dilatation p.c S ∘ slicePoint 0) <
    (p.c - V) * weightedNorm volume (ρ ∘ slicePoint 0) (scoreMagnitude ρ 0)

/-- Weighted Minkowski square of the actual lower osmotic momentum over the full initial slice. -/
def signedIntegral (p : MassiveParameters) (ρ : Covector → ℝ) : ℝ :=
  ∫ y, ρ (slicePoint 0 y) * minkowski (infoMomentum p ρ (slicePoint 0 y))
    (infoMomentum p ρ (slicePoint 0 y))

variable {p : MassiveParameters} {ρ S : Covector → ℝ} {σ K freq : ℝ}

/-- Squaring the complex field on the slice gives exactly the Gaussian used in the Fisher integral. -/
theorem density_eq (h : SliceData p ρ S σ K freq) : ρ ∘ slicePoint 0 = density σ := by
  funext y
  change ρ (slicePoint 0 y) = _
  rw [density_of_real_slice p h.initial_value y (h.density_pos y).le]
  unfold amplitude density
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- The ambient spatial score on the slice agrees with the derivative of the Gaussian intensity. -/
theorem spatial_score (h : SliceData p ρ S σ K freq) (y : Spatial) :
    spatialScore ρ (slicePoint 0 y) = SpatialFisherEnergy.score (density σ) y := by
  rw [← SpatialFisherEnergy.score_slice 0 ((h.density_regular y).differentiableAt (by norm_num))
    (h.density_pos y), density_eq h]

/-- The original field has zero drift at every spatial point, normal score 2K and dilatation −2cK. -/
theorem slice_values (h : SliceData p ρ S σ K freq) (y : Spatial) :
    phaseDrift p.c S (slicePoint 0 y) = 0 ∧ normalScore ρ (slicePoint 0 y) = 2*K ∧
      dilatation p.c S (slicePoint 0 y) = -2*p.c*K :=
  gaussian_dilatation p σ K freq h.width_pos h.frequency_pos h.initial_value y
    (h.density_regular y) (h.phase_regular y) (h.density_pos y) (h.initial_derivative y) (h.kg y)

/-- The spatial speed supremum on the whole initial slice is exactly zero. -/
theorem speed_sup (h : SliceData p ρ S σ K freq) :
    (⨆ y : Spatial, euclideanSpeed (phaseDrift p.c S (slicePoint 0 y))) = 0 := by
  simp [(slice_values h _).1, euclideanSpeed, speedSq, spatialDot]

/-- The Gaussian Cauchy slice lies in the future-timelike phase domain even for large |K|. -/
theorem future_timelike (h : SliceData p ρ S σ K freq) (y : Spatial) :
    0 < normalMomentum S (slicePoint 0 y) ∧
      0 < minkowski (phaseDifferential S (slicePoint 0 y)) (phaseDifferential S (slicePoint 0 y)) := by
  let x := slicePoint 0 y
  have ha := (normal_data p ((h.density_regular y).differentiableAt (by norm_num))
    ((h.phase_regular y).differentiableAt (by norm_num)) (h.density_pos y) K freq (h.initial_derivative y)).2
  have hp : 0 < normalMomentum S x := ha ▸ mul_pos p.hbar_pos h.frequency_pos
  have hs (i : Fin 3) : phaseDifferential S x i.succ = 0 := by
    have hv := congrFun (slice_values h y).1 i
    change p.c * phaseDifferential S x i.succ / normalMomentum S x = 0 at hv
    exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hv).resolve_right hp.ne')).resolve_left p.c_pos.ne'
  constructor
  · exact hp
  · change 0 < minkowski (phaseDifferential S x) (phaseDifferential S x)
    unfold minkowski
    simp only [show phaseDifferential S x 1 = 0 from hs 0, show phaseDifferential S x 2 = 0 from hs 1,
      show phaseDifferential S x 3 = 0 from hs 2, zero_mul, sub_zero]
    exact mul_pos_of_neg_of_neg (neg_pos.mp hp) (neg_pos.mp hp)

private theorem signed_integrand (h : SliceData p ρ S σ K freq) (y : Spatial) :
    ρ (slicePoint 0 y) * minkowski (infoMomentum p ρ (slicePoint 0 y)) (infoMomentum p ρ (slicePoint 0 y)) =
    p.hbar^2/4 * (density σ y * (2*K)^2 - density σ y * speedSq (SpatialFisherEnergy.score (density σ) y)) := by
  have hr := congrFun (density_eq h) y
  rw [info_square, (slice_values h y).2.1, spatial_score h y, show ρ (slicePoint 0 y) = _ from hr]
  ring

/-- Each density-weighted square in the normal, spatial and dilatation comparison is integrable. -/
theorem integrable_squares (h : SliceData p ρ S σ K freq) :
    Integrable (fun y => ρ (slicePoint 0 y) * normalScore ρ (slicePoint 0 y)^2) ∧
    Integrable (fun y => ρ (slicePoint 0 y) * (scoreMagnitude ρ 0 y)^2) ∧
    Integrable (fun y => ρ (slicePoint 0 y) * dilatation p.c S (slicePoint 0 y)^2) := by
  have hr (y : Spatial) : ρ (slicePoint 0 y) = density σ y := congrFun (density_eq h) y
  simp only [hr, (slice_values h _).2.1, (slice_values h _).2.2, scoreMagnitude, euclideanSpeed_sq,
    spatial_score h]
  exact ⟨(integrable_density h.width_pos).mul_const _, integrable_fisher h.width_pos,
    (integrable_density h.width_pos).mul_const _⟩

/-- The source's signed physical integral exists as a Lebesgue integral over the entire slice. -/
theorem integrable_signed (h : SliceData p ρ S σ K freq) :
    Integrable (fun y => ρ (slicePoint 0 y) * minkowski (infoMomentum p ρ (slicePoint 0 y))
      (infoMomentum p ρ (slicePoint 0 y))) := by
  rw [funext (signed_integrand h)]
  exact (((integrable_density h.width_pos).mul_const _).sub (integrable_fisher h.width_pos)).const_mul _

/-- The actual signed momentum integral is ℏ²M(4K² − 3/σ²)/4, with M the Gaussian mass. -/
theorem signed_integral (h : SliceData p ρ S σ K freq) :
    signedIntegral p ρ = p.hbar^2/4 * normalization σ * (4*K^2 - 3/σ^2) := by
  unfold signedIntegral
  rw [funext (signed_integrand h), integral_const_mul,
    integral_sub ((integrable_density h.width_pos).mul_const _) (integrable_fisher h.width_pos),
    integral_mul_const, integral_density h.width_pos, integral_fisher h.width_pos]
  ring

/-- The weighted squared norms of dilatation and of the true spatial log-score are finite
and have the values M(2cK)² and 3M/σ². -/
theorem norm_squares (h : SliceData p ρ S σ K freq) :
    weightedNorm volume (ρ ∘ slicePoint 0) (dilatation p.c S ∘ slicePoint 0)^2 =
      normalization σ * (2*p.c*K)^2 ∧
    weightedNorm volume (ρ ∘ slicePoint 0) (scoreMagnitude ρ 0)^2 =
      normalization σ * (3/σ^2) := by
  have hr : ∀ᵐ y ∂volume, 0 ≤ (ρ ∘ slicePoint 0) y := ae_of_all _ (fun y => (h.density_pos y).le)
  rw [weightedNorm_sq hr, weightedNorm_sq hr, density_eq h]
  constructor
  · have he : dilatation p.c S ∘ slicePoint 0 = fun _ => -2*p.c*K := funext fun y => (slice_values h y).2.2
    rw [he, integral_mul_const, integral_density h.width_pos]
    ring
  · simp only [scoreMagnitude, euclideanSpeed_sq, spatial_score h]
    exact integral_fisher h.width_pos

/-- At the attained optimal speed bound zero, the source's strict inequality holds exactly
when the Cauchy rate satisfies 4K² < 3/σ². -/
theorem dilatation_bound_iff (h : SliceData p ρ S σ K freq) :
    DilatationBound p ρ S 0 ↔ 4*K^2 < 3/σ^2 := by
  obtain ⟨hd, hs⟩ := norm_squares h
  unfold DilatationBound
  have hD : 0 ≤ weightedNorm volume (ρ ∘ slicePoint 0) (dilatation p.c S ∘ slicePoint 0) := Real.sqrt_nonneg _
  have hG : 0 ≤ weightedNorm volume (ρ ∘ slicePoint 0) (scoreMagnitude ρ 0) := Real.sqrt_nonneg _
  rw [sub_zero, ← sq_lt_sq₀ hD (mul_nonneg p.c_pos.le hG), mul_pow, hd, hs]
  have hf := mul_pos (sq_pos_of_pos p.c_pos) (normalization_pos h.width_pos)
  rw [show normalization σ * (2 * p.c * K)^2 = (p.c^2 * normalization σ) * (4*K^2) by ring,
    ← mul_assoc (p.c^2) (normalization σ) (3/σ^2), mul_lt_mul_iff_right₀ hf]

/-- Zero real normal amplitude rate gives both the strict source bound and a negative osmotic integral. -/
theorem pure_imaginary_datum (h : SliceData p ρ S σ 0 freq) :
    DilatationBound p ρ S 0 ∧ signedIntegral p ρ < 0 := by
  have hs : 0 < 3/σ^2 := div_pos (by norm_num) (sq_pos_of_pos h.width_pos)
  constructor
  · apply (dilatation_bound_iff h).mpr
    simpa using hs
  · rw [signed_integral h]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_sub]
    exact mul_neg_of_pos_of_neg (mul_pos (div_pos (sq_pos_of_pos p.hbar_pos) (by norm_num))
      (normalization_pos h.width_pos)) (neg_lt_zero.mpr hs)

/-- At the threshold the physical integral vanishes and the strict source bound fails. -/
theorem threshold_equality (h : SliceData p ρ S σ K freq) (hK : 4*K^2 = 3/σ^2) :
    ¬ DilatationBound p ρ S 0 ∧ signedIntegral p ρ = 0 := by
  rw [dilatation_bound_iff h, signed_integral h, hK]
  simp

/-- Above the threshold the osmotic integral is positive and the strict source bound fails. -/
theorem above_threshold (h : SliceData p ρ S σ K freq) (hK : 3/σ^2 < 4*K^2) :
    ¬ DilatationBound p ρ S 0 ∧ 0 < signedIntegral p ρ := by
  rw [dilatation_bound_iff h, signed_integral h]
  exact ⟨hK.not_gt, mul_pos (mul_pos (div_pos (sq_pos_of_pos p.hbar_pos) (by norm_num))
    (normalization_pos h.width_pos)) (sub_pos.mpr hK)⟩

/-- Choosing K=1/σ makes the signed integral positive at every positive width with these data. -/
theorem inverse_width_datum (h : SliceData p ρ S σ (1/σ) freq) :
    ¬ DilatationBound p ρ S 0 ∧ 0 < signedIntegral p ρ := by
  apply above_threshold h
  rw [div_pow, one_pow, mul_div_assoc']
  exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos h.width_pos)).mpr (by norm_num)

end FoliationQM.GaussianSliceCoercivity
