module

public import FoliationQM.KLIntegralTaylor
public import FoliationQM.ClockTaylorAverage
public import FoliationQM.ClockKLLimit
public import Mathlib.Analysis.Asymptotics.Ring

/-!
# Finite clock shifts of the actual KL integral

Sources: v13 `thm:clock_sideband` proof and `eq:kl_fisher_expansion`,
supplement fourth-order refinement. Weighted spatial derivative envelopes
control the actual KL Taylor error. Genuine phase averaging cancels the
cubic term and gives an explicit fourth-order bound. Its constant is the
integral of the chosen density's fourth-derivative envelope, not a universal
constant. The supplied probe model and source boundary conditions remain inputs.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ClockKLFiniteShift

open MeasureTheory Filter Metric Set TranslatedKL KLDifferentiation FisherNormalization
open ClockProbeCovariance ClockProbeLimit ClockKLLimit KLFourthDomination
open scoped Topology BigOperators

/-- The explicit scale-radius bound places every phase probe in the common
translation ball, including negative and zero scales. -/
theorem scaled_probe_mem_ball (ell ε r : ℝ) (hε : |ε| * |ell| < r) (θ : Space) :
    ε • displacement ell θ ∈ ball (0 : Space) r := by
  rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (norm_displacement_le ell θ) (abs_nonneg ε)).trans_lt hε

/-- A positive common radius contains every scaled probe for all sufficiently
small real scales, with an explicit scale-radius inequality. -/
theorem eventually_scale_radius_lt (ell : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ ε : ℝ in 𝓝 0, |ε| * |ell| < r := by
  have hc : ContinuousAt (fun ε : ℝ => |ε| * |ell|) 0 := by fun_prop
  have ht : Tendsto (fun ε : ℝ => |ε| * |ell|) (𝓝 0) (𝓝 0) := by
    simpa only [abs_zero, zero_mul] using hc.tendsto
  exact ht.eventually_lt_const hr

/-- The actual finite-shift KL average differs from its Fisher quadratic
term by at most the integrated fourth-derivative envelope times scale-four. -/
theorem norm_averaged_kl_sub_fisher_le {f : Space → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure Space} {r : ℝ} (D : HigherDomination f μ r)
    (hfirst : ∀ i, (∫ x, fderiv ℝ f x (coordinate i) ∂μ) = 0)
    (hFisher : ∀ i, Integrable (matrixIntegrand f coordinate i i) μ)
    (hSecond : ∀ i, Integrable
      (fun x => fderiv ℝ (fderiv ℝ f) x (coordinate i) (coordinate i)) μ)
    (hsecond : ∀ i, (∫ x, fderiv ℝ (fderiv ℝ f) x (coordinate i) (coordinate i) ∂μ) = 0)
    (ell ε : ℝ) (hε : |ε| * |ell| < r) :
    ‖average3 (fun θ => value f μ (ε • displacement ell θ)) -
      ε ^ 2 * ell ^ 2 / 4 * fisherTrace f coordinate μ‖ ≤
      ((∫ x, D.fourthBound x ∂μ) / 24) * (ε ^ 4 * ell ^ 4) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hc : Continuous (fun θ => value f μ (ε • displacement ell θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact (hasFDerivAt_value hf2 hpos D.toDomination
      (scaled_probe_mem_ball ell ε r hε θ)).continuousAt.comp
      (f := fun θ => ε • displacement ell θ) (g := value f μ) (x := θ)
      (show ContinuousAt (fun θ => ε • displacement ell θ) θ from
        by simpa using! ((continuous_displacement ell).const_smul ε).continuousAt)
  have ht := ClockTaylorAverage.norm_average3_sub_trace_le_of_remainder ell ε
    (value f μ) (secondIntegral f μ 0) (thirdIntegral f μ 0)
    (C := (∫ x, D.fourthBound x ∂μ) / 24)
    (div_nonneg (integral_fourthBound_nonneg D) (by norm_num)) hc
    (fun θ => by
      simpa only [ClockTaylorAverage.polynomial, quadratic, ClockProbeCubic.cubic] using
        KLIntegralTaylor.norm_value_sub_quadratic_cubic_le hf hpos D
          (scaled_probe_mem_ball ell ε r hε θ)
          (boundary_all_directions hf2 hpos D.toDomination hfirst))
  have he (i : Fin 3) : secondIntegral f μ 0 (Pi.single i 1) (Pi.single i 1) =
      fisherMatrix f coordinate μ i i := by
    rw [← fderiv_fderiv_value hf2 hpos D.toDomination (mem_ball_self D.radius_pos)]
    exact KLHessian.hessian_eq_fisherMatrix hf2 hpos D.toDomination coordinate i i
      (hFisher i) (hSecond i) (hsecond i)
  simp_rw [he] at ht
  rwa [← fisherTrace_eq_sum_diagonal f coordinate μ hFisher] at ht

/-- The source finite-shift correction is genuinely fourth order along
small real scales, with the fixed probe radius retained in the comparison. -/
theorem isBigO_averaged_kl_sub_fisher {f : Space → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure Space} {r : ℝ} (D : HigherDomination f μ r)
    (hfirst : ∀ i, (∫ x, fderiv ℝ f x (coordinate i) ∂μ) = 0)
    (hFisher : ∀ i, Integrable (matrixIntegrand f coordinate i i) μ)
    (hSecond : ∀ i, Integrable
      (fun x => fderiv ℝ (fderiv ℝ f) x (coordinate i) (coordinate i)) μ)
    (hsecond : ∀ i, (∫ x, fderiv ℝ (fderiv ℝ f) x (coordinate i) (coordinate i) ∂μ) = 0)
    (ell : ℝ) :
    (fun ε : ℝ => average3 (fun θ => value f μ (ε • displacement ell θ)) -
      ε ^ 2 * ell ^ 2 / 4 * fisherTrace f coordinate μ)
      =O[𝓝 0] (fun ε : ℝ => ε ^ 4 * ell ^ 4) := by
  apply Asymptotics.IsBigO.of_bound ((∫ x, D.fourthBound x ∂μ) / 24)
  filter_upwards [eventually_scale_radius_lt ell D.radius_pos] with ε hε
  simpa only [Real.norm_of_nonneg (show 0 ≤ ε ^ 4 * ell ^ 4 by positivity)] using
    norm_averaged_kl_sub_fisher_le hf hpos D hfirst hFisher hSecond hsecond ell ε hε

/-- Auxiliary spatial normalization preserves the actual order-four regularity. -/
theorem contDiff_normalizedDensity_four {ρ : Space → ℝ} (hρ : ContDiff ℝ 4 ρ) (Z : ℝ) :
    ContDiff ℝ 4 (normalizedDensity ρ Z) := by
  change ContDiff ℝ 4 (fun x => ρ x / Z)
  simpa only [div_eq_mul_inv] using hρ.mul (contDiff_const (c := Z⁻¹))

/-- The finite normalized KL estimate has the exact physical hbar-squared
quadratic coefficient and an explicit density-dependent fourth-order error. -/
theorem norm_normalized_clock_kl_sub_fisher_le (p : MassiveParameters)
    {ρ : Space → ℝ} {Z : ℝ} (hρ : ContDiff ℝ 4 ρ) (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z)
    {μ : Measure Space} {r : ℝ} (D : HigherDomination (normalizedDensity ρ Z) μ r)
    (hfirst : ∀ i, (∫ x, fderiv ℝ (normalizedDensity ρ Z) x (coordinate i) ∂μ) = 0)
    (hFisher : ∀ i, Integrable (matrixIntegrand (normalizedDensity ρ Z) coordinate i i) μ)
    (hSecond : ∀ i, Integrable (fun x => fderiv ℝ (fderiv ℝ (normalizedDensity ρ Z))
      x (coordinate i) (coordinate i)) μ)
    (hsecond : ∀ i, (∫ x, fderiv ℝ (fderiv ℝ (normalizedDensity ρ Z))
      x (coordinate i) (coordinate i) ∂μ) = 0)
    (ε : ℝ) (hε : |ε| * |p.ellC| < r) :
    ‖(Z * p.m ^ 2 * p.c ^ 2) *
        average3 (fun θ => value (normalizedDensity ρ Z) μ (ε • displacement p.ellC θ)) -
      ε ^ 2 * p.hbar ^ 2 / 4 * fisherTrace ρ coordinate μ‖ ≤
      (Z * p.m ^ 2 * p.c ^ 2) *
        (((∫ x, D.fourthBound x ∂μ) / 24) * (ε ^ 4 * p.ellC ^ 4)) := by
  have hf := contDiff_normalizedDensity_four hρ Z
  have hp := fun x => normalizedDensity_pos ρ hZ (hpos x)
  have hb := norm_averaged_kl_sub_fisher_le hf hp D hfirst hFisher hSecond hsecond p.ellC ε hε
  have hd := hρ.differentiable (by norm_num)
  have hi i := integrable_physical_matrix hd hpos hZ μ i i (hFisher i)
  have htrace := integrable_trace_of_diagonal ρ coordinate μ hi
  have hc : (Z * p.m ^ 2 * p.c ^ 2) *
      (ε ^ 2 * p.ellC ^ 2 / 4 * fisherTrace (normalizedDensity ρ Z) coordinate μ) =
      ε ^ 2 * p.hbar ^ 2 / 4 * fisherTrace ρ coordinate μ := by
    calc
      _ = ε ^ 2 * p.hbar ^ 2 / 4 *
          (Z * fisherTrace (normalizedDensity ρ Z) coordinate μ) := by
        unfold MassiveParameters.ellC
        field_simp [p.m_pos.ne', p.c_pos.ne']
      _ = _ := by rw [mass_mul_fisherTrace_normalizedDensity hd hpos hZ coordinate μ htrace]
  have hpref : 0 ≤ Z * p.m ^ 2 * p.c ^ 2 := by positivity
  rw [← hc, ← mul_sub, norm_mul, Real.norm_of_nonneg hpref]
  exact mul_le_mul_of_nonneg_left hb hpref

/-- For actual finite positive spatial Lebesgue mass, every translated
auxiliary density is a unit-mass law and the physical finite-shift error
obeys the proved quartic estimate. -/
theorem spatial_probability_finite_shift (p : MassiveParameters)
    {ρ : Space → ℝ} {Z : ℝ} (hρ : ContDiff ℝ 4 ρ) (hpos : ∀ x, 0 < ρ x) (hZ : 0 < Z)
    {r : ℝ} (D : HigherDomination (normalizedDensity ρ Z) volume r)
    (hmassInt : Integrable ρ) (hmass : (∫ x, ρ x) = Z)
    (hfirst : ∀ i, (∫ x, fderiv ℝ (normalizedDensity ρ Z) x (coordinate i)) = 0)
    (hFisher : ∀ i, Integrable (matrixIntegrand (normalizedDensity ρ Z) coordinate i i))
    (hSecond : ∀ i, Integrable (fun x => fderiv ℝ (fderiv ℝ (normalizedDensity ρ Z))
      x (coordinate i) (coordinate i)))
    (hsecond : ∀ i, (∫ x, fderiv ℝ (fderiv ℝ (normalizedDensity ρ Z))
      x (coordinate i) (coordinate i)) = 0)
    (ε : ℝ) (hε : |ε| * |p.ellC| < r) :
    (∀ a : Space, Integrable (fun x => normalizedDensity ρ Z (x + a)) ∧
      (∫ x, normalizedDensity ρ Z (x + a)) = 1) ∧
    ‖(Z * p.m ^ 2 * p.c ^ 2) *
        average3 (fun θ => value (normalizedDensity ρ Z) volume (ε • displacement p.ellC θ)) -
      ε ^ 2 * p.hbar ^ 2 / 4 * fisherTrace ρ coordinate volume‖ ≤
      (Z * p.m ^ 2 * p.c ^ 2) *
        (((∫ x, D.fourthBound x) / 24) * (ε ^ 4 * p.ellC ^ 4)) :=
  ⟨fun a => ⟨integrable_translated_density hmassInt Z a,
      integral_translated_density hmassInt hZ hmass a⟩,
    norm_normalized_clock_kl_sub_fisher_le p hρ hpos hZ D
      hfirst hFisher hSecond hsecond ε hε⟩

end FoliationQM.ClockKLFiniteShift
