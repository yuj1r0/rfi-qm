module

public import FoliationQM.SpatialFisherEnergy
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian mass and Fisher integral on an entire observer slice

For v13 `thm:adm_positivity` and `eq:dilatation_coercivity_bound`, the
intensity is a centered isotropic Gaussian with coordinate variance σ².
All three coordinates range over ℝ. The score is obtained by Fréchet
differentiation and its weighted square is integrated with Lebesgue volume.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianSliceMoments

open LorentzCoordinates SpatialFisherEnergy MeasureTheory ProbabilityTheory

/-- Unnormalised isotropic Gaussian intensity with coordinate standard deviation σ. -/
def density (σ : ℝ) (y : Spatial) : ℝ := Real.exp (-speedSq y / (2 * σ^2))

/-- Total spatial mass of the unnormalised Gaussian of positive width σ. -/
def normalization (σ : ℝ) : ℝ := (Real.sqrt (2 * Real.pi * σ^2))^3

/-- The Gaussian intensity is positive everywhere on the full spatial slice. -/
theorem density_pos (σ : ℝ) (y : Spatial) : 0 < density σ y := Real.exp_pos _

/-- For positive width the total-mass factor is strictly positive. -/
theorem normalization_pos {σ : ℝ} (hσ : 0 < σ) : 0 < normalization σ := by
  unfold normalization
  positivity

/-- The Gaussian intensity is smooth on the full spatial slice. -/
theorem smooth_density (σ : ℝ) : ContDiff ℝ ⊤ (density σ) := by
  unfold density speedSq spatialDot
  fun_prop

/-- Differentiating the logarithmic intensity gives the coordinate score −yᵢ/σ². -/
theorem score_eq (σ : ℝ) (y : Spatial) :
    score (density σ) y = fun i => -y i / σ^2 := by
  have he : (fun z => Real.log (density σ z)) =
      fun z => -((z 0)^2 + (z 1)^2 + (z 2)^2) * (2 * σ^2)⁻¹ := by
    funext z
    simp [density, speedSq, spatialDot, sq, div_eq_mul_inv]
  have hs (j : Fin 3) := (hasFDerivAt_apply (𝕜 := ℝ) j y).pow 2
  have hd := ((((hs 0).add (hs 1)).add (hs 2)).neg).mul_const (2 * σ^2)⁻¹
  simp only [Pi.add_apply, Pi.neg_apply] at hd
  ext i
  unfold score
  rw [he, hd.fderiv]
  fin_cases i <;> simp <;> ring

private def kernel (σ t : ℝ) : ℝ := Real.exp (-t^2 / (2 * σ^2))
private def widthFactor (σ : ℝ) : ℝ := Real.sqrt (2 * Real.pi * σ^2)

private theorem density_prod (σ : ℝ) (y : Spatial) :
    density σ y = ∏ i, kernel σ (y i) := by
  rw [Fin.prod_univ_three]
  unfold kernel density speedSq spatialDot
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private theorem moment_one_dim {σ : ℝ} (hσ : 0 < σ) :
    Integrable (kernel σ) ∧
    Integrable (fun t => kernel σ t * t^2) ∧
    (∫ t, kernel σ t) = widthFactor σ ∧
    (∫ t, kernel σ t * t^2) = widthFactor σ * σ^2 := by
  let v : NNReal := ⟨σ^2, sq_nonneg σ⟩
  have hv : v ≠ 0 := by
    intro hz
    have h : σ^2 = 0 := congrArg NNReal.toReal hz
    exact (sq_pos_of_pos hσ).ne' h
  have hw : 0 < widthFactor σ := by unfold widthFactor; positivity
  have ratio (t : ℝ) : kernel σ t = widthFactor σ * gaussianPDFReal 0 v t := by
    unfold gaussianPDFReal kernel
    change _ = widthFactor σ * ((widthFactor σ)⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]
    simp only [sub_zero]
    rfl
  have hker : Integrable (kernel σ) := by
    simpa only [funext ratio] using (integrable_gaussianPDFReal 0 v).const_mul (widthFactor σ)
  have hweighted : Integrable (fun t => kernel σ t * t^2) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := (2 * σ^2)⁻¹)
      (by positivity) (s := (2 : ℕ)) (by norm_num)
    convert h using 1
    funext t
    rw [Real.rpow_natCast]
    unfold kernel
    rw [div_eq_inv_mul]
    ring_nf
  have hm := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hm
  simp only [integral_id_gaussianReal, sub_zero] at hm
  rw [integral_gaussianReal_eq_integral_smul hv] at hm
  simp only [smul_eq_mul] at hm
  refine ⟨hker, hweighted, ?_, ?_⟩
  · simp_rw [ratio, integral_const_mul, integral_gaussianPDFReal_eq_one _ hv, mul_one]
  · simp_rw [ratio, mul_assoc, integral_const_mul, hm]
    rfl

/-- The Gaussian intensity is integrable against spatial Lebesgue volume. -/
theorem integrable_density {σ : ℝ} (hσ : 0 < σ) : Integrable (density σ) := by
  rw [funext (density_prod σ)]
  exact Integrable.fintype_prod (μ := fun _ => volume) (fun _ => (moment_one_dim hσ).1)

/-- The full three-dimensional Gaussian integral equals (√(2πσ²))³. -/
theorem integral_density {σ : ℝ} (hσ : 0 < σ) : (∫ y, density σ y) = normalization σ := by
  rw [funext (density_prod σ), integral_fintype_prod_volume_eq_pow, (moment_one_dim hσ).2.2.1]
  rfl

private def momentFactor (σ : ℝ) (i j : Fin 3) (t : ℝ) : ℝ :=
  if i = j then kernel σ t * t^2 else kernel σ t

private theorem coord_product (σ : ℝ) (i : Fin 3) (y : Spatial) :
    density σ y * (y i)^2 = ∏ j, momentFactor σ i j (y j) := by
  rw [density_prod, Fin.prod_univ_three, Fin.prod_univ_three]
  fin_cases i <;> simp [momentFactor] <;> ring

private theorem coordinate_moment {σ : ℝ} (hσ : 0 < σ) (i : Fin 3) :
    Integrable (fun y => density σ y * (y i)^2) ∧
    (∫ y, density σ y * (y i)^2) = normalization σ * σ^2 := by
  obtain ⟨h₀, h₂, m₀, m₂⟩ := moment_one_dim hσ
  rw [funext (coord_product σ i)]
  constructor
  · apply Integrable.fintype_prod (μ := fun _ => volume)
    intro j
    by_cases hij : i = j
    · change Integrable (fun t => if i = j then kernel σ t * t^2 else kernel σ t)
      simpa [hij] using h₂
    · change Integrable (fun t => if i = j then kernel σ t * t^2 else kernel σ t)
      simpa [hij] using h₀
  · rw [integral_fintype_prod_volume_eq_prod, Fin.prod_univ_three]
    fin_cases i <;> simp [momentFactor, m₀, m₂, normalization, widthFactor] <;> ring

private theorem fisher_split (σ : ℝ) (y : Spatial) :
    density σ y * speedSq (score (density σ) y) =
    (density σ y * (y 0)^2 + density σ y * (y 1)^2 + density σ y * (y 2)^2) / (σ^2)^2 := by
  rw [score_eq]
  unfold speedSq spatialDot
  ring

/-- The weighted squared norm of the actual logarithmic score is integrable over the whole slice. -/
theorem integrable_fisher {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun y => density σ y * speedSq (score (density σ) y)) := by
  rw [funext (fisher_split σ)]
  exact (((coordinate_moment hσ 0).1.add (coordinate_moment hσ 1).1).add
    (coordinate_moment hσ 2).1).div_const _

/-- The whole-slice spatial Fisher integral is the Gaussian mass times 3/σ². -/
theorem integral_fisher {σ : ℝ} (hσ : 0 < σ) :
    (∫ y, density σ y * speedSq (score (density σ) y)) = normalization σ * (3 / σ^2) := by
  have h01 : Integrable (fun y => density σ y * (y 0)^2 + density σ y * (y 1)^2) :=
    (coordinate_moment hσ 0).1.add (coordinate_moment hσ 1).1
  rw [funext (fisher_split σ), integral_div, integral_add h01 (coordinate_moment hσ 2).1,
    integral_add (coordinate_moment hσ 0).1 (coordinate_moment hσ 1).1,
    (coordinate_moment hσ 0).2, (coordinate_moment hσ 1).2, (coordinate_moment hσ 2).2]
  field_simp [hσ.ne']
  ring

end FoliationQM.GaussianSliceMoments
