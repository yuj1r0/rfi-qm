module
public import FoliationQM.TwistedScalarControl
public import FoliationQM.RelativeAction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrated chiral corrections and the scalar action limit

For v13 `thm:dirac_lift`, integrate the actual massive density of the
chirally rotated spinor on its spacetime domain. A common bound on
the four angle derivatives provides an explicit integrable majorant.
The density increment can also be integrated before separate actions.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff
namespace FoliationQM.TwistedScalarAction
open MeasureTheory Filter DiracFieldDensity TwistedScalarDensity TwistedScalarControl ScalarSpinDefect

/-- The true massive action of the chirally rotated scalar field. -/
def action (p : MassiveParameters) (β : Covector → ℝ) (z : Covector → ℂ) (U : Set Covector) : ℝ :=
  ∫ x in U, density p β z x

/-- The real scalar Klein–Gordon integrand for the coordinate directions of flat spacetime. -/
def scalarDensity (p : MassiveParameters) (z : Covector → ℂ) (x : Covector) : ℝ :=
  (ActionVariation.fieldPairing p z z coordinateDirections x).re

/-- The integrated scalar density on the same spacetime set. -/
def scalarAction (p : MassiveParameters) (z : Covector → ℂ) (U : Set Covector) : ℝ :=
  ∫ x in U, scalarDensity p z x

/-- A compact change of the scalar field with fixed chiral background. -/
def relativeAction (p : MassiveParameters) (β : Covector → ℝ) (z w : Covector → ℂ) (U : Set Covector) : ℝ :=
  ∫ x in U, density p β w x - density p β z x

/-- The part subtracted from the scalar integrand. -/
def correction (p : MassiveParameters) (β : Covector → ℝ) (z : Covector → ℂ) (x : Covector) : ℝ :=
  potential p β x * Complex.normSq (z x)

variable (p : MassiveParameters) {β : Covector → ℝ} {z w : Covector → ℂ} {U : Set Covector}

/-- Splitting of the ordinary action with both terms genuinely integrable. -/
theorem action_eq (hU : MeasurableSet U) (hβ : ∀ x ∈ U, DifferentiableAt ℝ β x)
    (hz : ∀ x ∈ U, DifferentiableAt ℝ z x) (hscalar : IntegrableOn (scalarDensity p z) U)
    (hc : IntegrableOn (correction p β z) U) :
    action p β z U = scalarAction p z U - ∫ x in U, correction p β z x := by
  rw [scalarAction, ← integral_sub hscalar hc]
  exact setIntegral_congr_fun hU fun x hx => density_eq_pairing p (hβ x hx) (hz x hx)

/-- Whenever the correction is integrable, the spinor action is finite exactly when the scalar action is finite. -/
theorem integrable_iff (hU : MeasurableSet U) (hβ : ∀ x ∈ U, DifferentiableAt ℝ β x)
    (hz : ∀ x ∈ U, DifferentiableAt ℝ z x) (hc : IntegrableOn (correction p β z) U) :
    IntegrableOn (density p β z) U ↔ IntegrableOn (scalarDensity p z) U := by
  constructor
  · intro h
    apply (h.add hc).congr_fun _ hU
    intro x hx
    change density p β z x + correction p β z x = _
    rw [density_eq_pairing p (hβ x hx) (hz x hx)]
    exact sub_add_cancel _ _
  · intro h
    exact (h.sub hc).congr_fun (fun x hx => (density_eq_pairing p (hβ x hx) (hz x hx)).symm) hU

/-- A finite pair of massive densities gives the ordinary action difference. -/
theorem relative_eq_sub (hz : IntegrableOn (density p β z) U) (hw : IntegrableOn (density p β w) U) :
    relativeAction p β z w U = action p β w U - action p β z U := integral_sub hw hz

/-- The potential is continuous at every C¹ point of the angle. -/
theorem continuousAt_potential {x : Covector} (hβ : ContDiffAt ℝ 1 β x) :
    ContinuousAt (potential p β) x := by
  have hg : ContinuousAt (gradient β) x := continuousAt_pi.mpr fun μ =>
    (hβ.continuousAt_fderiv one_ne_zero).clm_apply (continuousAt_const (y := coordinateDirections μ))
  have hc : Continuous (fun v : Covector => p.hbar^2 / 4 * minkowski v v) := by unfold minkowski; fun_prop
  exact hc.continuousAt.comp hg

/-- Local C¹ angles and continuous scalar fields give a measurable correction on the integration domain. -/
theorem measurable_correction (hU : MeasurableSet U) (hβ : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : ContinuousOn z U) :
    AEStronglyMeasurable (correction p β z) (volume.restrict U) := by
  apply ContinuousOn.aestronglyMeasurable _ hU
  exact fun x hx => ((continuousAt_potential p (hβ x hx)).continuousWithinAt).mul
    (Complex.continuous_normSq.continuousAt.comp_continuousWithinAt (hz x hx))

/-- The common derivative bound yields the explicit envelope ℏ² M² times the squared modulus. -/
theorem correction_bound {x : Covector} {M : ℝ} (hM : ∀ μ, |gradient β x μ| ≤ M) :
    ‖correction p β z x‖ ≤ p.hbar^2 * M^2 * Complex.normSq (z x) := by
  rw [Real.norm_eq_abs, correction, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
  exact mul_le_mul_of_nonneg_right (abs_potential_le p β x hM) (Complex.normSq_nonneg _)

variable {B : ℕ → Covector → ℝ} {M : Covector → ℝ}

/-- The integrated correction tends to zero under genuine pointwise derivative convergence
and an integrable derivative envelope on the restricted volume. -/
theorem tendsto_integral_correction (hU : MeasurableSet U) (hβ : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 1 (B n) x)
    (hz : ContinuousOn z U) (hlim : ∀ᵐ x ∂volume.restrict U, Tendsto (fun n => gradient (B n) x) atTop (𝓝 0))
    (hM : ∀ n, ∀ᵐ x ∂volume.restrict U, ∀ μ, |gradient (B n) x μ| ≤ M x)
    (hint : IntegrableOn (fun x => p.hbar^2 * (M x)^2 * Complex.normSq (z x)) U) :
    Tendsto (fun n => ∫ x in U, correction p (B n) z x) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict U) (f := fun _ => (0 : ℝ)) _
    (fun n => measurable_correction p hU (hβ n) hz) hint
    (fun n => (hM n).mono (fun x hx => correction_bound p hx))
    (hlim.mono (fun x hx => by simpa [correction] using (tendsto_potential_zero p hx).mul_const (Complex.normSq (z x))))
  simpa using h

/-- Value convergence of the actual chiral actions to the scalar action under the stated
derivative and integrability controls; every action included here is finite. -/
theorem tendsto_action (hU : MeasurableSet U) (hβ : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 1 (B n) x)
    (hz : ∀ x ∈ U, DifferentiableAt ℝ z x) (hs : IntegrableOn (scalarDensity p z) U)
    (hlim : ∀ᵐ x ∂volume.restrict U, Tendsto (fun n => gradient (B n) x) atTop (𝓝 0))
    (hM : ∀ n, ∀ᵐ x ∂volume.restrict U, ∀ μ, |gradient (B n) x μ| ≤ M x)
    (hint : IntegrableOn (fun x => p.hbar^2 * (M x)^2 * Complex.normSq (z x)) U) :
    (∀ n, IntegrableOn (density p (B n) z) U) ∧ Tendsto (fun n => action p (B n) z U) atTop (𝓝 (scalarAction p z U)) := by
  have hc : ContinuousOn z U := fun x hx => (hz x hx).continuousAt.continuousWithinAt
  have hi (n : ℕ) : IntegrableOn (correction p (B n) z) U :=
    hint.mono' (measurable_correction p hU (hβ n) hc) ((hM n).mono (fun _ hx => correction_bound p hx))
  have hd (n : ℕ) (x : Covector) (hx : x ∈ U) := (hβ n x hx).differentiableAt_one
  refine ⟨fun n => (integrable_iff p hU (hd n) hz (hi n)).mpr hs, ?_⟩
  simp_rw [action_eq p hU (hd _) hz hs (hi _)]
  simpa using (tendsto_const_nhds (x := scalarAction p z U)).sub (tendsto_integral_correction p hU hβ hc hlim hM hint)

end FoliationQM.TwistedScalarAction
