module

public import FoliationQM.SmoothLogarithmicCutoffEnergy
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Norm

/-!
# The smooth logarithmic cutoff on the Euclidean normal plane

Source: v13 `eq:log_cutoff_wallstrom` and `eq:log_cutoff_l2_bound`, component
kinds C and D. The actual complex Euclidean norm realizes the radial cutoff.
Its constant germ at the origin supplies smoothness there; the real derivative
and its operator norm are genuine derivatives of this same function. General
tubular geometry and the normal-plane energy integral remain separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SmoothNormalPlaneCutoff

open Filter Set
open scoped Topology ContDiff

/-- The smooth scalar logarithmic cutoff evaluated at the actual Euclidean radius of the complex plane. -/
def profile (ε : ℝ) (z : ℂ) : ℝ :=
  SmoothLogarithmicCutoffProfile.profile ε ‖z‖

/-- The plane cutoff is zero on the radius-ε² disk, one outside the radius-ε disk, and between zero and one everywhere. -/
theorem profile_spec {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (∀ z : ℂ, ‖z‖ ≤ ε ^ 2 → profile ε z = 0) ∧
    (∀ z : ℂ, ε ≤ ‖z‖ → profile ε z = 1) ∧
    ∀ z : ℂ, 0 ≤ profile ε z ∧ profile ε z ≤ 1 := by
  obtain ⟨hz, ho, hr⟩ := SmoothLogarithmicCutoffProfile.profile_spec h0 h1
  exact ⟨fun z h => hz ‖z‖ h, fun z h => ho ‖z‖ h, fun z => hr ‖z‖⟩

private theorem eventually_zero {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ∀ᶠ z in 𝓝 (0 : ℂ), profile ε z = 0 := by
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ < ε ^ 2 :=
    (continuous_norm.tendsto (0 : ℂ)).eventually
      (eventually_lt_nhds (by simpa using sq_pos_of_pos h0))
  filter_upwards [hn] with z hz
  exact (profile_spec h0 h1).1 z hz.le

private theorem scalar_deriv_zero {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    deriv (SmoothLogarithmicCutoffProfile.profile ε) 0 = 0 := by
  by_contra hz
  have hm := SmoothLogarithmicCutoffProfile.support_deriv_subset h0 h1 hz
  exact (not_le_of_gt (sq_pos_of_pos h0)) hm.1

/-- The actual plane cutoff is infinitely real differentiable, including the origin where it has a constant-zero germ. -/
theorem contDiff_profile {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ContDiff ℝ ∞ (profile ε) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (eventually_zero h0 h1)
  · exact (SmoothLogarithmicCutoffProfile.contDiff_profile h0 h1).contDiffAt.comp z
      (contDiffAt_norm ℝ hz)

/-- The actual real Fréchet derivative is the scalar radial derivative times the norm derivative; the identity also holds at the origin. -/
theorem fderiv_profile {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (z : ℂ) :
    fderiv ℝ (profile ε) z =
      deriv (SmoothLogarithmicCutoffProfile.profile ε) ‖z‖ •
        fderiv ℝ (norm : ℂ → ℝ) z := by
  by_cases hz : z = 0
  · subst z
    rw [norm_zero, scalar_deriv_zero h0 h1, zero_smul]
    exact (hasFDerivAt_zero_of_eventually_const (0 : ℝ) (eventually_zero h0 h1)).fderiv
  · have hn : DifferentiableAt ℝ (norm : ℂ → ℝ) z :=
      (contDiffAt_norm ℝ hz : ContDiffAt ℝ 1 (norm : ℂ → ℝ) z).differentiableAt_one
    have hs := ((SmoothLogarithmicCutoffProfile.contDiff_profile h0 h1).differentiable
      (by simp) ‖z‖).hasDerivAt
    exact (hs.comp_hasFDerivAt z hn.hasFDerivAt).fderiv

/-- The operator norm of the actual plane derivative equals the absolute scalar radial derivative, including at radius zero. -/
theorem norm_fderiv_profile {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (z : ℂ) :
    ‖fderiv ℝ (profile ε) z‖ =
      |deriv (SmoothLogarithmicCutoffProfile.profile ε) ‖z‖| := by
  rw [fderiv_profile h0 h1]
  by_cases hz : z = 0
  · subst z
    rw [norm_zero, scalar_deriv_zero h0 h1, zero_smul, norm_zero, abs_zero]
  · have hn : DifferentiableAt ℝ (norm : ℂ → ℝ) z :=
      (contDiffAt_norm ℝ hz : ContDiffAt ℝ 1 (norm : ℂ → ℝ) z).differentiableAt_one
    rw [norm_smul, Real.norm_eq_abs, norm_fderiv_norm hn, mul_one]

/-- The support of the actual real derivative lies in the closed Euclidean annulus between ε² and ε. -/
theorem support_fderiv_subset {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Function.support (fderiv ℝ (profile ε)) ⊆ {z : ℂ | ε ^ 2 ≤ ‖z‖ ∧ ‖z‖ ≤ ε} := by
  intro z hz
  have hs : deriv (SmoothLogarithmicCutoffProfile.profile ε) ‖z‖ ≠ 0 := by
    intro h
    apply hz
    rw [fderiv_profile h0 h1, h, zero_smul]
  exact SmoothLogarithmicCutoffProfile.support_deriv_subset h0 h1 hs

/-- At every fixed nonzero point the plane cutoff is eventually exactly one as ε tends to zero through positive values. -/
theorem eventually_profile_eq_one {z : ℂ} (hz : z ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), profile ε z = 1 :=
  SmoothLogarithmicCutoffProfile.eventually_profile_eq_one (norm_pos_iff.mpr hz)

/-- One nonnegative constant bounds the actual derivative at every nonzero point for all 0 < ε < 1 by C divided by radius times |log ε|. -/
theorem exists_uniform_fderiv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ z : ℂ, z ≠ 0 →
      ‖fderiv ℝ (profile ε) z‖ ≤ C / (‖z‖ * |Real.log ε|) := by
  obtain ⟨C, hC, hb⟩ := SmoothLogarithmicCutoffEnergy.exists_uniform_derivative_bound
  refine ⟨C, hC, ?_⟩
  intro ε h0 h1 z hz
  rw [norm_fderiv_profile h0 h1]
  exact hb ε h0 h1 ‖z‖ (norm_pos_iff.mpr hz)

end FoliationQM.SmoothNormalPlaneCutoff
