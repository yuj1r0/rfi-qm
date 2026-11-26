module

public import FoliationQM.GaussianPlanePhaseWave
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Actual L2 Gaussian waves and their distributional derivatives

Sources: v13 thm:uncertainty and eq:heisenberg, component kinds C and D.
The proved square integrability of the literal Gaussian wave and its classical
derivative constructs two actual Lp elements. Full-line complex integration
by parts, with three genuinely integrable products, identifies their embedded
tempered distributions under the actual direction-one derivative. Every
complex Schwartz test is covered; the distribution pairing is plain complex
multiplication. Only the smooth reference wave is differentiated. The chosen
Lp representatives are related to it by actual almost-everywhere equalities.
Sobolev membership and sharp uncertainty remain separate consequences.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianDistributionalDerivative
open MeasureTheory GaussianPlanePhaseWave
open scoped ENNReal NNReal SchwartzMap LineDeriv

/-- The actual L2 element constructed from the proved Gaussian wave integrability. -/
def waveLp (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_wave m hv k theta).toLp (wave m v k theta)

/-- The actual L2 element constructed from the reference wave's genuine derivative. -/
def derivativeLp (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_deriv_wave m hv k theta).toLp (deriv (wave m v k theta))

/-- The chosen Lp wave representative equals the literal smooth wave almost everywhere. -/
theorem waveLp_ae_eq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    (waveLp m hv k theta : ℝ → ℂ) =ᵐ[volume] wave m v k theta :=
  (memLp_wave m hv k theta).coeFn_toLp

/-- The chosen Lp derivative representative equals the actual classical derivative almost everywhere. -/
theorem derivativeLp_ae_eq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    (derivativeLp m hv k theta : ℝ → ℂ) =ᵐ[volume] deriv (wave m v k theta) :=
  (memLp_deriv_wave m hv k theta).coeFn_toLp

private theorem integral_test (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (k theta : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * deriv (wave m v k theta) x) =
      -(∫ x, deriv φ x * wave m v k theta x) := by
  have hφ : MemLp φ 2 volume := φ.memLp 2 volume
  have hφ' : MemLp (deriv φ) 2 volume := by
    have he : (SchwartzMap.derivCLM ℂ ℂ φ : ℝ → ℂ) = deriv φ :=
      funext (SchwartzMap.derivCLM_apply ℂ φ)
    rw [← he]
    exact (SchwartzMap.derivCLM ℂ ℂ φ).memLp 2 volume
  have hW := memLp_wave m hv k theta
  have hW' := memLp_deriv_wave m hv k theta
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => φ.hasDerivAt x)
    (fun x _ => (differentiable_wave m hv k theta x).hasDerivAt)
    (hφ.integrable_mul hW') (hφ'.integrable_mul hW) (hφ.integrable_mul hW)

/-- The actual direction-one derivative of the embedded Lp wave equals the
embedded Lp derivative, as tested against every complex Schwartz function. -/
theorem lineDeriv_waveLp (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    ∂_{(1 : ℝ)} (waveLp m hv k theta : 𝓢'(ℝ, ℂ)) =
      (derivativeLp m hv k theta : 𝓢'(ℝ, ℂ)) := by
  ext1 φ
  rw [TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
  calc
    (∫ x, (-∂_{(1 : ℝ)} φ) x • waveLp m hv k theta x) =
        -(∫ x, deriv φ x * wave m v k theta x) := by
      calc
        _ = ∫ x, -(deriv φ x * wave m v k theta x) := by
          apply integral_congr_ae
          filter_upwards [waveLp_ae_eq m hv k theta] with x hx
          change -((∂_{(1 : ℝ)} φ) x) * waveLp m hv k theta x = _
          rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
            fderiv_apply_one_eq_deriv, hx, neg_mul]
        _ = _ := integral_neg _
    _ = ∫ x, φ x * deriv (wave m v k theta) x :=
      (integral_test m hv k theta φ).symm
    _ = ∫ x, φ x • derivativeLp m hv k theta x := by
      apply integral_congr_ae
      filter_upwards [derivativeLp_ae_eq m hv k theta] with x hx
      simp only [smul_eq_mul, hx]

end FoliationQM.GaussianDistributionalDerivative
