module

public import FoliationQM.MasterMetricAndCone
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The actual derivative of the positive-density polar field

Sources: v13 `eq:master_local_metric` and supplement
`eq:audit11_master_euclidean`. The real phase is a local lift. All derivatives
below are Mathlib Fréchet derivatives over `ℝ`, on an arbitrary real normed
vector space. Positivity is required at the point of differentiation; no
claim at a nodal zero or of a global phase lift is made. The metric identities
are evaluated on each tangent vector, so describe the pullback of the complex
Euclidean target metric, not an isometry with a spacetime metric.
-/
@[expose] public section

namespace FoliationQM.PolarDifferential

open MasterMetricAndCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The source's amplitude-phase field, using an actual complex exponential. -/
noncomputable def polarField (ρ Φ : E → ℝ) (x : E) : ℂ :=
  (Real.sqrt (ρ x) : ℂ) * phase (Φ x)

/-- A continuous real-linear differential for the polar field. -/
noncomputable def polarDifferential (ρ Φ : ℝ) (dρ dΦ : E →L[ℝ] ℝ) : E →L[ℝ] ℂ :=
  (Real.sqrt ρ : ℂ) • (phase Φ • (Complex.I • (Complex.ofRealCLM.comp dΦ))) +
    phase Φ • (Complex.ofRealCLM.comp ((1 / (2 * Real.sqrt ρ)) • dρ))

/-- Evaluation of the continuous linear differential is the algebraic tangent
proved in the preceding milestone. -/
theorem polarDifferential_apply (ρ Φ : ℝ) (dρ dΦ : E →L[ℝ] ℝ) (v : E) :
    polarDifferential ρ Φ dρ dΦ v = polarTangent ρ Φ (dρ v) (dΦ v) := by
  simp only [polarDifferential, polarTangent, amplitudeTangent,
    add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- The product and chain rules establish the actual Fréchet derivative on
positive density, from the derivatives of the two real source fields. -/
theorem hasFDerivAt_polarField {ρ Φ : E → ℝ} {dρ dΦ : E →L[ℝ] ℝ} {x : E}
    (hρ : HasFDerivAt ρ dρ x) (hΦ : HasFDerivAt Φ dΦ x) (hpos : 0 < ρ x) :
    HasFDerivAt (polarField ρ Φ) (polarDifferential (ρ x) (Φ x) dρ dΦ) x := by
  have hR := Complex.ofRealCLM.hasFDerivAt.comp x (hρ.sqrt (ne_of_gt hpos))
  have hΦc := Complex.ofRealCLM.hasFDerivAt.comp x hΦ
  have he := (hΦc.mul_const Complex.I).cexp
  exact hR.mul he

/-- Existence of the actual field differential needs only pointwise source
regularity and positive density. -/
theorem differentiableAt_polarField {ρ Φ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hΦ : DifferentiableAt ℝ Φ x) (hpos : 0 < ρ x) :
    DifferentiableAt ℝ (polarField ρ Φ) x :=
  (hasFDerivAt_polarField hρ.hasFDerivAt hΦ.hasFDerivAt hpos).differentiableAt

/-- The actual Fréchet derivative evaluated on an arbitrary tangent vector. -/
theorem fderiv_polarField_apply {ρ Φ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hΦ : DifferentiableAt ℝ Φ x) (hpos : 0 < ρ x)
    (v : E) :
    fderiv ℝ (polarField ρ Φ) x v =
      polarTangent (ρ x) (Φ x) (fderiv ℝ ρ x v) (fderiv ℝ Φ x v) := by
  rw [(hasFDerivAt_polarField hρ.hasFDerivAt hΦ.hasFDerivAt hpos).fderiv]
  exact polarDifferential_apply _ _ _ _ v

/-- First equality of the source metric identity, for actual derivatives. -/
theorem fderiv_polarField_normSq {ρ Φ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hΦ : DifferentiableAt ℝ Φ x) (hpos : 0 < ρ x)
    (v : E) :
    Complex.normSq (fderiv ℝ (polarField ρ Φ) x v) =
      (fderiv ℝ ρ x v) ^ 2 / (4 * ρ x) + ρ x * (fderiv ℝ Φ x v) ^ 2 := by
  rw [fderiv_polarField_apply hρ hΦ hpos]
  exact polarTangent_normSq _ _ _ _ hpos

/-- The same pullback identity written using Mathlib's actual norm. -/
theorem fderiv_polarField_norm_sq {ρ Φ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hΦ : DifferentiableAt ℝ Φ x) (hpos : 0 < ρ x)
    (v : E) :
    ‖fderiv ℝ (polarField ρ Φ) x v‖ ^ 2 =
      (fderiv ℝ ρ x v) ^ 2 / (4 * ρ x) + ρ x * (fderiv ℝ Φ x v) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  exact fderiv_polarField_normSq hρ hΦ hpos v

/-- Actual logarithmic-density differential on the regular domain. -/
theorem fderiv_log_density_apply {ρ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hpos : 0 < ρ x) (v : E) :
    fderiv ℝ (fun y => Real.log (ρ y)) x v = fderiv ℝ ρ x v / ρ x := by
  rw [(hρ.hasFDerivAt.log (ne_of_gt hpos)).fderiv]
  simp only [smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The clock phase specialization with its actual source differential. -/
theorem fderiv_clock_phase_apply (p : MassiveParameters) {τ : E → ℝ} {x : E}
    (hτ : DifferentiableAt ℝ τ x) (v : E) :
    fderiv ℝ (fun y => -p.omega0 * τ y) x v = -p.omega0 * fderiv ℝ τ x v := by
  rw [(hτ.hasFDerivAt.const_mul (-p.omega0)).fderiv]
  rfl

/-- The full regular-domain clock/log-density identity, with genuine Fréchet
derivatives for the wave field, clock, and logarithmic density. -/
theorem fderiv_clockField_norm_sq (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x) (hpos : 0 < ρ x)
    (v : E) :
    ‖fderiv ℝ (polarField ρ (fun y => -p.omega0 * τ y)) x v‖ ^ 2 =
      (ρ x / p.ellC ^ 2) *
        (p.c ^ 2 * (fderiv ℝ τ x v) ^ 2 +
          (p.ellC ^ 2 / 4) * (fderiv ℝ (fun y => Real.log (ρ y)) x v) ^ 2) := by
  rw [← Complex.normSq_eq_norm_sq,
    fderiv_polarField_apply hρ (hτ.const_mul (-p.omega0)) hpos,
    fderiv_clock_phase_apply p hτ,
    fderiv_log_density_apply hρ hpos]
  exact polarTangent_clock_normSq p _ _ _ _ hpos

end FoliationQM.PolarDifferential
