module

public import FoliationQM.WaveScoreAlgebra
public import FoliationQM.WeightedProbabilityTransport
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Actual wave-density probability and finite score moments

Sources: v13 thm:uncertainty, eq:p_var_decomp and eq:cramer_rao,
component kinds C and D. Normalization of an actual L² wave gives a genuine
probability measure. Actual L² derivative and position hypotheses give finite
weighted moments. The logarithmic score is identified almost everywhere for
this measure, which assigns zero mass to nodes. No whole-line score pairing,
momentum variance or Gaussian classification is assumed or asserted here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WaveDensityMeasure

open MeasureTheory WaveScoreAlgebra
open scoped ENNReal

/-- The actual measure with wave norm squared as its Lebesgue density. -/
def densityMeasure (u : ℝ → ℂ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (density (u x)))

private theorem measurable_density {u : ℝ → ℂ} (hu : Continuous u) :
    Measurable (fun x => density (u x)) := (hu.norm.pow 2).measurable

private theorem measurable_weight {u : ℝ → ℂ} (hu : Continuous u) :
    Measurable (fun x => ENNReal.ofReal (density (u x))) :=
  (measurable_density hu).ennreal_ofReal

private theorem integrable_density_of_memLp {u : ℝ → ℂ} (hu : MemLp u 2 volume) :
    Integrable (fun x => density (u x)) volume :=
  (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu

/-- Genuine L² integrability and actual unit normalization give a probability measure. -/
theorem isProbabilityMeasure {u : ℝ → ℂ} (hu : MemLp u 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) : IsProbabilityMeasure (densityMeasure u) := by
  constructor
  change (volume.withDensity (fun x => ENNReal.ofReal (density (u x)))) Set.univ = 1
  rw [WeightedProbabilityTransport.withDensity_mass_eq_ofReal_integral volume
    (integrable_density_of_memLp hu) (ae_of_all _ fun x => density_nonneg (u x)), hnorm]
  exact ENNReal.ofReal_one

/-- Weighted integrability is equivalent to genuine integrability of the density-weighted function. -/
theorem integrable_iff_weighted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {u : ℝ → ℂ} (hu : Continuous u) {f : ℝ → E} :
    Integrable f (densityMeasure u) ↔ Integrable (fun x => density (u x) • f x) volume := by
  have hto (x : ℝ) : (ENNReal.ofReal (density (u x))).toReal = density (u x) :=
    ENNReal.toReal_ofReal (density_nonneg (u x))
  simpa only [densityMeasure, hto] using
    (integrable_withDensity_iff_integrable_smul' (μ := volume) (g := f)
      (measurable_weight hu) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top))

/-- The actual integral transport includes a proof that its density-weighted side is finite. -/
theorem integrable_and_integral_transport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {u : ℝ → ℂ} (hu : Continuous u)
    {f : ℝ → E} (hf : Integrable f (densityMeasure u)) :
    Integrable (fun x => density (u x) • f x) volume ∧
      (∫ x, f x ∂densityMeasure u) = ∫ x, density (u x) • f x := by
  refine ⟨(integrable_iff_weighted hu).mp hf, ?_⟩
  have hto (x : ℝ) : (ENNReal.ofReal (density (u x))).toReal = density (u x) :=
    ENNReal.toReal_ofReal (density_nonneg (u x))
  simpa only [densityMeasure, hto] using
    (integral_withDensity_eq_integral_toReal_smul (μ := volume) (measurable_weight hu)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) f)

/-- Density-measure almost-everywhere statements need hold only on the positive-density locus. -/
theorem ae_iff_positive {u : ℝ → ℂ} (hu : Continuous u) (p : ℝ → Prop) :
    (∀ᵐ x ∂densityMeasure u, p x) ↔ ∀ᵐ x, 0 < density (u x) → p x := by
  simpa only [densityMeasure, ENNReal.ofReal_ne_zero_iff] using
    (ae_withDensity_iff (μ := volume) (p := p) (measurable_weight hu))

/-- Nodes have zero density measure; global positivity of the wave is not assumed. -/
theorem ae_density_pos {u : ℝ → ℂ} (hu : Continuous u) :
    ∀ᵐ x ∂densityMeasure u, 0 < density (u x) :=
  (ae_iff_positive hu _).mpr (ae_of_all _ fun _ hx => hx)

/-- The separately supplied complex position moment gives genuine weighted position L². -/
theorem memLp_position {u : ℝ → ℂ} (hu : Continuous u)
    (hx : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume) :
    MemLp (fun x : ℝ => x) 2 (densityMeasure u) := by
  have hs : Integrable (fun x => density (u x) * x ^ 2) volume := by
    simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      density, mul_comm] using
      (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx
  apply (memLp_two_iff_integrable_sq continuous_id.aestronglyMeasurable).mpr
  exact (integrable_iff_weighted hu).mpr hs

/-- The actual position second moment is finite and equals its Lebesgue-density expression. -/
theorem position_second_moment {u : ℝ → ℂ} (hu : Continuous u)
    (hx : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume) :
    Integrable (fun x => density (u x) * x ^ 2) volume ∧
      (∫ x, x ^ 2 ∂densityMeasure u) = ∫ x, density (u x) * x ^ 2 :=
  integrable_and_integral_transport hu (memLp_position hu hx).integrable_sq

private theorem aestronglyMeasurable_score {u v : ℝ → ℂ} (hu : Continuous u)
    (hv : MemLp v 2 volume) :
    AEStronglyMeasurable (fun x => score (u x) (v x)) volume := by
  have hq : AEMeasurable (fun x => v x / u x) volume :=
    hv.aestronglyMeasurable.aemeasurable.div hu.measurable.aemeasurable
  have hr := Complex.continuous_re.measurable.comp_aemeasurable hq
  simpa only [score_eq_two_re_div, Function.comp_apply] using!
    (hr.const_mul 2).aestronglyMeasurable

private theorem aestronglyMeasurable_phaseRate {u v : ℝ → ℂ} (hu : Continuous u)
    (hv : MemLp v 2 volume) :
    AEStronglyMeasurable (fun x => phaseRate (u x) (v x)) volume := by
  have hq : AEMeasurable (fun x => v x / u x) volume :=
    hv.aestronglyMeasurable.aemeasurable.div hu.measurable.aemeasurable
  have hi := Complex.continuous_im.measurable.comp_aemeasurable hq
  simpa only [phaseRate_eq_im_div, Function.comp_apply] using! hi.aestronglyMeasurable

/-- The pointwise score bound yields a genuinely integrable density-weighted square, including nodes. -/
theorem integrable_weighted_score_sq {u v : ℝ → ℂ} (hu : Continuous u)
    (hv : MemLp v 2 volume) :
    Integrable (fun x => density (u x) * score (u x) (v x) ^ 2) volume := by
  apply ((integrable_density_of_memLp hv).const_mul 4).mono_nonneg
    ((measurable_density hu).aestronglyMeasurable.mul
      ((aestronglyMeasurable_score hu hv).pow 2))
  · exact ae_of_all _ fun x => mul_nonneg (density_nonneg (u x)) (sq_nonneg _)
  · exact ae_of_all _ fun x => density_mul_score_sq_le (u x) (v x)

/-- The actual canonical score is square-integrable for the genuine density measure. -/
theorem memLp_score {u v : ℝ → ℂ} (hu : Continuous u) (hv : MemLp v 2 volume) :
    MemLp (fun x => score (u x) (v x)) 2 (densityMeasure u) := by
  have hm : AEStronglyMeasurable (fun x => score (u x) (v x)) (densityMeasure u) :=
    AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous volume _)
      (aestronglyMeasurable_score hu hv)
  apply (memLp_two_iff_integrable_sq hm).mpr
  exact (integrable_iff_weighted hu).mpr (integrable_weighted_score_sq hu hv)

/-- The phase-rate bound likewise gives a genuinely finite density-weighted square. -/
theorem integrable_weighted_phaseRate_sq {u v : ℝ → ℂ} (hu : Continuous u)
    (hv : MemLp v 2 volume) :
    Integrable (fun x => density (u x) * phaseRate (u x) (v x) ^ 2) volume := by
  apply (integrable_density_of_memLp hv).mono_nonneg
    ((measurable_density hu).aestronglyMeasurable.mul
      ((aestronglyMeasurable_phaseRate hu hv).pow 2))
  · exact ae_of_all _ fun x => mul_nonneg (density_nonneg (u x)) (sq_nonneg _)
  · exact ae_of_all _ fun x => density_mul_phaseRate_sq_le (u x) (v x)

/-- The canonical phase rate has genuine weighted L² integrability. -/
theorem memLp_phaseRate {u v : ℝ → ℂ} (hu : Continuous u) (hv : MemLp v 2 volume) :
    MemLp (fun x => phaseRate (u x) (v x)) 2 (densityMeasure u) := by
  have hm : AEStronglyMeasurable (fun x => phaseRate (u x) (v x)) (densityMeasure u) :=
    AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous volume _)
      (aestronglyMeasurable_phaseRate hu hv)
  apply (memLp_two_iff_integrable_sq hm).mpr
  exact (integrable_iff_weighted hu).mpr (integrable_weighted_phaseRate_sq hu hv)

/-- Actual bulk momentum is square-integrable by constant scaling of the phase rate. -/
theorem memLp_bulk {u v : ℝ → ℂ} (hu : Continuous u) (hv : MemLp v 2 volume)
    (hbar : ℝ) : MemLp (fun x => bulk hbar (u x) (v x)) 2 (densityMeasure u) :=
  (memLp_phaseRate hu hv).const_mul hbar

/-- The actual logarithmic derivative equals the canonical score almost everywhere
for the density measure, where zero-density nodes are negligible. -/
theorem ae_log_derivative_eq_score {u v : ℝ → ℂ} (hu : Continuous u)
    (hd : ∀ᵐ x, HasDerivAt u (v x) x) :
    (fun x => deriv (fun y => Real.log (density (u y))) x) =ᵐ[densityMeasure u]
      (fun x => score (u x) (v x)) := by
  apply (ae_iff_positive hu _).mpr
  filter_upwards [hd] with x hx hpos
  exact (hasDerivAt_log_density hx ((density_pos_iff (u x)).mp hpos)).deriv

/-- The true logarithmic derivative inherits actual weighted L² integrability. -/
theorem memLp_log_derivative {u v : ℝ → ℂ} (hu : Continuous u)
    (hd : ∀ᵐ x, HasDerivAt u (v x) x) (hv : MemLp v 2 volume) :
    MemLp (fun x => deriv (fun y => Real.log (density (u y))) x) 2 (densityMeasure u) :=
  MemLp.ae_eq (ae_log_derivative_eq_score hu hd).symm (memLp_score hu hv)

/-- The actual Fisher integral is finite and equals the canonical Lebesgue-weighted score integral. -/
theorem fisher_integral_eq {u v : ℝ → ℂ} (hu : Continuous u)
    (hd : ∀ᵐ x, HasDerivAt u (v x) x) (hv : MemLp v 2 volume) :
    Integrable (fun x => density (u x) * score (u x) (v x) ^ 2) volume ∧
    Integrable (fun x => (deriv (fun y => Real.log (density (u y))) x) ^ 2)
      (densityMeasure u) ∧
    (∫ x, (deriv (fun y => Real.log (density (u y))) x) ^ 2 ∂densityMeasure u) =
      ∫ x, density (u x) * score (u x) (v x) ^ 2 := by
  refine ⟨integrable_weighted_score_sq hu hv, (memLp_log_derivative hu hd hv).integrable_sq, ?_⟩
  calc
    (∫ x, (deriv (fun y => Real.log (density (u y))) x) ^ 2 ∂densityMeasure u) =
        ∫ x, score (u x) (v x) ^ 2 ∂densityMeasure u := by
      apply integral_congr_ae
      filter_upwards [ae_log_derivative_eq_score hu hd] with x hx
      rw [hx]
    _ = ∫ x, density (u x) * score (u x) (v x) ^ 2 :=
      (integrable_and_integral_transport hu (memLp_score hu hv).integrable_sq).2

end FoliationQM.WaveDensityMeasure
