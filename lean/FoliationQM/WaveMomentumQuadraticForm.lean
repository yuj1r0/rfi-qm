module

public import FoliationQM.QuantumCurrentAlgebra
public import FoliationQM.WaveScoreIntegrationByParts
public import FoliationQM.OsmoticScoreVariance

/-!
# Actual quantum expectation and momentum quadratic-form variance

Sources: v13 thm:uncertainty, eq:p_var_decomp and eq:p_fisher_bound,
component kinds C and D. The observables are literal complex-current and
centered momentum norm-square integrals. Genuine L² inputs give finiteness;
the proved whole-line density identity gives reality of the expectation.
The decomposition and Fisher bound are then derived for the actual locally
absolutely continuous representative. No position moment is needed here.

Canonical bulk momentum is identified with a supplied local phase derivative
in a subsequent source bridge. Classical derivatives concern the actual AC
representative; equality almost everywhere transfers the integral observables.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.WaveMomentumQuadraticForm
open MeasureTheory Filter WaveScoreAlgebra WaveDensityMeasure QuantumCurrentAlgebra
open scoped ComplexConjugate

variable {u v u' v' : ℝ → ℂ}

/-- The literal complex expectation of the weak-derivative momentum current. -/
def quantumExpectation (hbar : ℝ) (u v : ℝ → ℂ) : ℂ :=
  ∫ x, current hbar (u x) (v x)

/-- The literal norm-square quadratic form at an arbitrary real center. -/
def quadraticMoment (hbar p : ℝ) (u v : ℝ → ℂ) : ℝ :=
  ∫ x, ‖centeredPValue hbar p (u x) (v x)‖ ^ 2

/-- The real part of the actual complex momentum expectation. -/
def meanMomentum (hbar : ℝ) (u v : ℝ → ℂ) : ℝ :=
  (quantumExpectation hbar u v).re

/-- The actual momentum quadratic-form variance at its actual mean. -/
def momentumVariance (hbar : ℝ) (u v : ℝ → ℂ) : ℝ :=
  quadraticMoment hbar (meanMomentum hbar u v) u v

/-- Actual wave and derivative equality almost everywhere preserve the expectation. -/
theorem quantumExpectation_congr_ae (hbar : ℝ)
    (hu : u =ᵐ[volume] u') (hv : v =ᵐ[volume] v') :
    quantumExpectation hbar u v = quantumExpectation hbar u' v' := by
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  rw [hx, hy]

/-- Actual equality of both fields preserves the fixed-center quadratic form. -/
theorem quadraticMoment_congr_ae (hbar p : ℝ)
    (hu : u =ᵐ[volume] u') (hv : v =ᵐ[volume] v') :
    quadraticMoment hbar p u v = quadraticMoment hbar p u' v' := by
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  rw [hx, hy]

/-- The actual expectation identity also transports the center of the variance. -/
theorem momentumVariance_congr_ae (hbar : ℝ)
    (hu : u =ᵐ[volume] u') (hv : v =ᵐ[volume] v') :
    momentumVariance hbar u v = momentumVariance hbar u' v' := by
  have hm : meanMomentum hbar u v = meanMomentum hbar u' v' :=
    congrArg Complex.re (quantumExpectation_congr_ae hbar hu hv)
  unfold momentumVariance
  rw [hm]
  exact quadraticMoment_congr_ae hbar _ hu hv

/-- The actual derivative momentum belongs to L² by constant complex scaling. -/
theorem memLp_pValue (hbar : ℝ) (hv : MemLp v 2 volume) :
    MemLp (fun x => pValue hbar (v x)) 2 volume := by
  simpa only [pValue] using hv.const_mul ((-Complex.I) * (hbar : ℂ))

/-- The literal complex quantum current is genuinely integrable by the L² product. -/
theorem integrable_current (hbar : ℝ) (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) : Integrable (fun x => current hbar (u x) (v x)) volume := by
  exact (hu.star.integrable_mul (memLp_pValue hbar hv)).congr
    (Eventually.of_forall fun _ => rfl)

/-- Every real-centered momentum norm square has a genuine finite integral. -/
theorem integrable_centered_norm_sq (hbar p : ℝ) (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) :
    Integrable (fun x => ‖centeredPValue hbar p (u x) (v x)‖ ^ 2) volume := by
  have hm : MemLp (fun x => centeredPValue hbar p (u x) (v x)) 2 volume := by
    refine MemLp.ae_eq ?_ ((memLp_pValue hbar hv).sub (hu.const_mul (p : ℂ)))
    exact Eventually.of_forall fun _ => rfl
  exact hm.norm.integrable_sq

/-- The actual density-weighted bulk mean is finite even before normalization. -/
theorem integrable_bulk (hc : Continuous u) (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) (hbar : ℝ) :
    Integrable (fun x => bulk hbar (u x) (v x)) (densityMeasure u) := by
  apply (integrable_iff_weighted hc).mpr
  apply (integrable_current hbar hu hv).re.congr
  exact Eventually.of_forall fun x => by
    simpa only [RCLike.re_eq_complex_re, smul_eq_mul] using current_re hbar (u x) (v x)

/-- Whole-line density integration by parts makes the actual expectation real
and identifies it with the genuine density-weighted bulk mean. -/
theorem quantumExpectation_eq_bulk_mean (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) (hbar : ℝ) :
    quantumExpectation hbar u v =
      (CenteredL2Variance.mean (densityMeasure u) (fun x => bulk hbar (u x) (v x)) : ℂ) := by
  have hj := integrable_current hbar hu hv
  have hb := integrable_and_integral_transport hc (integrable_bulk hc hu hv hbar)
  apply Complex.ext
  · change (∫ x, current hbar (u x) (v x)).re =
      CenteredL2Variance.mean (densityMeasure u) (fun x => bulk hbar (u x) (v x))
    calc
      _ = ∫ x, (current hbar (u x) (v x)).re := by
        simpa only [RCLike.re_eq_complex_re] using (integral_re hj).symm
      _ = ∫ x, density (u x) * bulk hbar (u x) (v x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => current_re hbar (u x) (v x)
      _ = _ := by simpa only [smul_eq_mul, CenteredL2Variance.mean] using hb.2.symm
  · change (∫ x, current hbar (u x) (v x)).im = 0
    calc
      _ = ∫ x, (current hbar (u x) (v x)).im := by
        simpa only [RCLike.im_eq_complex_im] using (integral_im hj).symm
      _ = ∫ x, -(hbar / 2) * densityDerivative (u x) (v x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => current_im hbar (u x) (v x)
      _ = 0 := by
        rw [integral_const_mul, WaveScoreIntegrationByParts.integral_densityDerivative hAC hd hu hv,
          mul_zero]

/-- The actual finite quadratic form splits at any real center into the
bulk centered square and the actual logarithmic-density Fisher integral. -/
theorem quadraticMoment_eq (hc : Continuous u)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar p : ℝ) :
    quadraticMoment hbar p u v =
      (∫ x, (bulk hbar (u x) (v x) - p) ^ 2 ∂densityMeasure u) +
      (hbar ^ 2 / 4) *
        (∫ x, (deriv (fun y => Real.log (density (u y))) x) ^ 2 ∂densityMeasure u) := by
  let : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hnorm
  have hb : MemLp (fun x => bulk hbar (u x) (v x) - p) 2 (densityMeasure u) := by
    refine MemLp.ae_eq ?_ ((memLp_bulk hc hv hbar).sub (memLp_const p))
    exact Eventually.of_forall fun _ => rfl
  have ht := integrable_and_integral_transport hc hb.integrable_sq
  have hi : Integrable (fun x => density (u x) * (bulk hbar (u x) (v x) - p) ^ 2)
      volume := by simpa only [smul_eq_mul] using ht.1
  have hs := integrable_weighted_score_sq hc hv
  have hf := fisher_integral_eq hc hd hv
  calc
    _ = ∫ x, density (u x) * (bulk hbar (u x) (v x) - p) ^ 2 +
        (hbar ^ 2 / 4) * (density (u x) * score (u x) (v x) ^ 2) := by
      apply integral_congr_ae
      filter_upwards [ae_centeredPValue_norm_sq hbar p hd] with x hx
      rw [hx]
      ring
    _ = (∫ x, density (u x) * (bulk hbar (u x) (v x) - p) ^ 2) +
        (hbar ^ 2 / 4) * (∫ x, density (u x) * score (u x) (v x) ^ 2) := by
      rw [integral_add hi (hs.const_mul _), integral_const_mul]
    _ = _ := by
      rw [← hf.2.2]
      congr 1
      simpa only [smul_eq_mul] using ht.2.symm

/-- Centering at the proved actual quantum mean gives the genuine canonical
bulk variance plus the logarithmic-density Fisher contribution. -/
theorem variance_decomposition (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) :
    momentumVariance hbar u v =
      CenteredL2Variance.variance (densityMeasure u) (fun x => bulk hbar (u x) (v x)) +
      (hbar ^ 2 / 4) *
        (∫ x, (deriv (fun y => Real.log (density (u y))) x) ^ 2 ∂densityMeasure u) := by
  have hm : meanMomentum hbar u v =
      CenteredL2Variance.mean (densityMeasure u) (fun x => bulk hbar (u x) (v x)) := by
    unfold meanMomentum
    rw [quantumExpectation_eq_bulk_mean hc hAC hd hu hv hbar]
    rfl
  unfold momentumVariance
  rw [hm]
  simpa only [CenteredL2Variance.variance, CenteredL2Variance.centered] using
    quadraticMoment_eq hc hd hu hv hnorm hbar
      (CenteredL2Variance.mean (densityMeasure u) (fun x => bulk hbar (u x) (v x)))

/-- Nonnegative genuine bulk variance gives the actual momentum-Fisher bound. -/
theorem fisher_bound (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) :
    (hbar ^ 2 / 4) *
        (∫ x, (deriv (fun y => Real.log (density (u y))) x) ^ 2 ∂densityMeasure u) ≤
      momentumVariance hbar u v := by
  rw [variance_decomposition hc hAC hd hu hv hnorm hbar]
  exact le_add_of_nonneg_left (CenteredL2Variance.variance_nonneg _ _)

/-- Derived zero logarithmic-score mean identifies the Fisher contribution
with the actual osmotic variance, giving the sum of two genuine variances. -/
theorem variance_decomposition_osmotic (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) :
    momentumVariance hbar u v =
      CenteredL2Variance.variance (densityMeasure u) (fun x => bulk hbar (u x) (v x)) +
      CenteredL2Variance.variance (densityMeasure u)
        (OsmoticScoreVariance.observable hbar
          (fun x => deriv (fun y => Real.log (density (u y))) x)) := by
  let : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hnorm
  have hs := memLp_log_derivative hc hd hv
  have hm : CenteredL2Variance.mean (densityMeasure u)
      (fun x => deriv (fun y => Real.log (density (u y))) x) = 0 :=
    WaveScoreIntegrationByParts.integral_log_derivative hc hAC hd hu hv
  rw [variance_decomposition hc hAC hd hu hv hnorm hbar,
    OsmoticScoreVariance.variance_observable (densityMeasure u) hs hbar hm]

end FoliationQM.WaveMomentumQuadraticForm
