module

public import FoliationQM.FirstOrderSobolevConverse
public import FoliationQM.GaussianDistributionalDerivative
public import FoliationQM.GaussianWaveRigidity
public import FoliationQM.GaussianDensitySaturation

/-!
# Actual Gaussian Sobolev states attaining sharp uncertainty

Sources: v13 thm:uncertainty and eq:heisenberg, component kinds C and D.
The concrete Lp wave and derivative have a genuine tempered-distribution
derivative relation, which gives actual pinned Bessel H¹ membership. Their
normalization, position moment and Gaussian density measure are transported
through actual almost-everywhere equalities. A genuine affine supplied phase
then proves literal sharp uncertainty for the same original Lp state and
derivative. No new representative is selected, and no classical derivative
of an arbitrary Lp representative or squared-operator domain is asserted.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianSobolevWitness
open MeasureTheory ProbabilityTheory Filter GaussianDistributionalDerivative
open GaussianPlanePhaseWave WaveScoreAlgebra WaveDensityMeasure SobolevCramerRao
open CenteredL2Variance WaveMomentumQuadraticForm
open scoped NNReal SchwartzMap LineDeriv

/-- The concrete Gaussian Lp wave is an actual normalized H¹ source state
with its specified weak derivative, finite position moment and Gaussian measure. -/
theorem source_data (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    TemperedDistribution.MemSobolev 1 2 (waveLp m hv k theta : 𝓢'(ℝ, ℂ)) ∧
    (∫ x : ℝ, ‖waveLp m hv k theta x‖ ^ 2) = 1 ∧
    MemLp (fun x : ℝ => (x : ℂ) * waveLp m hv k theta x) 2 volume ∧
    ∂_{(1 : ℝ)} (waveLp m hv k theta : 𝓢'(ℝ, ℂ)) =
      (derivativeLp m hv k theta : 𝓢'(ℝ, ℂ)) ∧
    ((fun x => density (waveLp m hv k theta x)) =ᵐ[volume] gaussianPDFReal m v) ∧
    densityMeasure (waveLp m hv k theta) = gaussianReal m v ∧
    IsProbabilityMeasure (densityMeasure (waveLp m hv k theta)) := by
  have hD := lineDeriv_waveLp m hv k theta
  have hF := waveLp_ae_eq m hv k theta
  have hn : (∫ x : ℝ, ‖waveLp m hv k theta x‖ ^ 2) = 1 := by
    calc
      (∫ x : ℝ, ‖waveLp m hv k theta x‖ ^ 2) =
          ∫ x, ‖wave m v k theta x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hF] with x hx
        rw [hx]
      _ = 1 := integral_norm_sq m hv k theta
  have hx : MemLp (fun x : ℝ => (x : ℂ) * waveLp m hv k theta x) 2 volume := by
    apply MemLp.ae_eq _ (memLp_position_mul_wave m hv k theta)
    filter_upwards [hF] with x he
    rw [he]
  have hρ : (fun x => density (waveLp m hv k theta x)) =ᵐ[volume]
      gaussianPDFReal m v := by
    filter_upwards [hF] with x he
    rw [he]
    exact norm_sq m hv k theta x
  have hμ : densityMeasure (waveLp m hv k theta) = gaussianReal m v := by
    rw [densityMeasure, gaussianReal_of_var_ne_zero m hv, gaussianPDF_def]
    apply withDensity_congr_ae
    filter_upwards [hρ] with x he
    exact congrArg ENNReal.ofReal he
  exact ⟨FirstOrderSobolevConverse.memSobolev_one_of_lp_derivative
    (waveLp m hv k theta) (derivativeLp m hv k theta) hD,
    hn, hx, hD, hρ, hμ, isProbabilityMeasure (Lp.memLp (waveLp m hv k theta)) hn⟩

/-- The same concrete Gaussian source state and genuine weak derivative attain
the literal sharp bound, using their actual affine polar phase and quantum QF. -/
theorem sqrt_equality (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ)
    (hbar : ℝ) (hhbar : 0 < hbar) :
    Real.sqrt (variance (densityMeasure (waveLp m hv k theta)) (fun x : ℝ => x)) *
      Real.sqrt (momentumVariance hbar (waveLp m hv k theta)
        (derivativeLp m hv k theta)) = hbar / 2 := by
  let W := wave m v k theta
  let S : ℝ → ℝ := fun x => hbar * (k * x + theta)
  have hAC (a b : ℝ) : AbsolutelyContinuousOnInterval W a b :=
    (GaussianWaveRigidity.contDiff_wave m hv k theta).contDiffOn.absolutelyContinuousOnInterval
  have hd : ∀ᵐ x ∂volume, HasDerivAt W (deriv W x) x :=
    Eventually.of_forall fun x => (differentiable_wave m hv k theta x).hasDerivAt
  have hS (x : ℝ) : HasDerivAt S (hbar * k) x := by
    simpa only [S, mul_one] using!
      (((hasDerivAt_id x).const_mul k).add_const theta).const_mul hbar
  have hρ (x : ℝ) : density (W x) = gaussianPDFReal m v x := norm_sq m hv k theta x
  have hpolar (x : ℝ) (_ : 0 < density (W x)) : W x =
      (Real.sqrt (density (W x)) : ℂ) *
        Complex.exp (Complex.I * ((S x / hbar : ℝ) : ℂ)) := by
    have hcancel : S x / hbar = k * x + theta := by
      apply (div_eq_iff hhbar.ne').mpr
      dsimp only [S]
      ring
    rw [hcancel, hρ]
    rfl
  have heq := GaussianDensitySaturation.sqrt_equality_of_supplied_phase
    (continuous_wave m hv k theta) hAC hd (memLp_wave m hv k theta)
    (memLp_deriv_wave m hv k theta) (memLp_position_mul_wave m hv k theta)
    (integral_norm_sq m hv k theta) hbar hhbar m hv (Eventually.of_forall hρ) S
    (Eventually.of_forall fun x _ => (hS x).differentiableAt) hpolar
    (hbar * k) (Eventually.of_forall fun x => (hS x).deriv)
  have hμ := densityMeasure_congr_ae (waveLp_ae_eq m hv k theta)
  have hQ := momentumVariance_congr_ae hbar (waveLp_ae_eq m hv k theta)
    (derivativeLp_ae_eq m hv k theta)
  simpa only [hμ, hQ] using heq

end FoliationQM.GaussianSobolevWitness
