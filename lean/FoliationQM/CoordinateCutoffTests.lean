module

public import FoliationQM.SmoothCoordinateTubeCutoff
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Algebra.Support

/-!
# Genuine compact tests away from the coordinate nodal axis

Source: v13 `eq:log_cutoff_wallstrom`, component kinds C and D.
The same smooth coordinate cutoff multiplies the original
complex test. Its closed support stays inside the original support and outside
the open inner tube. This gives compact tests away from the literal flat
axis without any regularity requirement on the comparison set's boundary.
The actual product derivative is retained in every constant direction.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateCutoffTests

open Set ProductTubeCoordinates SmoothCoordinateTubeCutoff
open scoped ContDiff

/-- The original complex test multiplied by the same smooth real coordinate cutoff. -/
def test (ε : ℝ) (φ : Covector → ℂ) (x : Covector) : ℂ :=
  profile ε x • φ x

/-- The cut-off test is smooth and compact; its closed support retains the original support and the inner-radius bound, and lies inside the comparison set away from the axis. -/
theorem test_data {ε : ℝ} {φ : Covector → ℂ} {U : Set Covector}
    (h0 : 0 < ε) (h1 : ε < 1) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (test ε φ) ∧ HasCompactSupport (test ε φ) ∧
    tsupport (test ε φ) ⊆ tsupport φ ∩ {x | ε ^ 2 ≤ ‖(coordinates x).snd‖} ∧
    tsupport (test ε φ) ⊆ U \ {x : Covector | x 2 = 0 ∧ x 3 = 0} := by
  have hsm : ContDiff ℝ ∞ (test ε φ) := by
    change ContDiff ℝ ∞ (fun x => profile ε x • φ x)
    exact (contDiff_profile h0 h1).smul hφ
  have hcp : HasCompactSupport (test ε φ) := by
    change HasCompactSupport (profile ε • φ)
    exact hc.smul_left
  have hr : Continuous (fun x : Covector => ‖(coordinates x).snd‖) :=
    ((WithLp.sndL 2 ℝ ℂ ℂ).continuous.comp coordinates.continuous).norm
  have hp : Function.support (profile ε) ⊆ {x | ε ^ 2 ≤ ‖(coordinates x).snd‖} := by
    intro x hx
    change profile ε x ≠ 0 at hx
    change ε ^ 2 ≤ ‖(coordinates x).snd‖
    by_contra hn
    exact hx ((profile_spec h0 h1).1 x (le_of_lt (lt_of_not_ge hn)))
  have ht : tsupport (profile ε) ⊆ {x | ε ^ 2 ≤ ‖(coordinates x).snd‖} :=
    closure_minimal hp (isClosed_le continuous_const hr)
  have hsupport : tsupport (test ε φ) ⊆
      tsupport φ ∩ {x | ε ^ 2 ≤ ‖(coordinates x).snd‖} := by
    intro x hx
    change x ∈ tsupport (fun y => profile ε y • φ y) at hx
    exact ⟨tsupport_smul_subset_right (profile ε) φ hx,
      ht (tsupport_smul_subset_left (profile ε) φ hx)⟩
  refine ⟨hsm, hcp, hsupport, ?_⟩
  intro x hx
  refine ⟨hs (hsupport hx).1, ?_⟩
  intro ha
  have hz : (coordinates x).snd = 0 :=
    show x ∈ coordinates ⁻¹' {y : WithLp 2 (ℂ × ℂ) | y.snd = 0} from
      axis_preimage.symm ▸ ha
  have hb := (hsupport hx).2
  change ε ^ 2 ≤ ‖(coordinates x).snd‖ at hb
  rw [hz, norm_zero] at hb
  exact (not_le_of_gt (sq_pos_of_pos h0)) hb

/-- The actual directional derivative of the cut-off complex test is the sum of the cutoff-derivative and original-test-derivative terms. -/
theorem directional_test {ε : ℝ} {φ : Covector → ℂ} {x : Covector}
    (h0 : 0 < ε) (h1 : ε < 1) (hφ : DifferentiableAt ℝ φ x) (v : Covector) :
    fderiv ℝ (test ε φ) x v =
      fderiv ℝ (profile ε) x v • φ x + profile ε x • fderiv ℝ φ x v := by
  have hχ := (contDiff_profile h0 h1).differentiable (by simp) x
  change fderiv ℝ (fun y => profile ε y • φ y) x v = _
  rw [fderiv_fun_smul hχ hφ]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, add_comm]

end FoliationQM.CoordinateCutoffTests
