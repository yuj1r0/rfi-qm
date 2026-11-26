module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Genuine compact primitives for zero-mean smooth tests

Sources: v13 `eq:cramer_rao` and `thm:uncertainty`, component kind C.
These real-line test-function results support the actual weak-derivative
bridge. A zero-mean compact smooth test has a compact smooth primitive
when its integral is anchored strictly left of the support. The left
and right exterior identities prove compact support, including both
endpoints. A normalized smooth compact test is constructed from an
actual normalized bump. No Sobolev representative or density integration
by parts is presumed by these statements.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CompactTestPrimitive

open MeasureTheory Set
open scoped ContDiff

/-- Every compact support on the real line lies strictly inside a bounded interval. -/
theorem exists_support_interval {φ : ℝ → ℝ} (hc : HasCompactSupport φ) :
    ∃ a b : ℝ, a < b ∧ tsupport φ ⊆ Ioo a b := by
  obtain ⟨R, hR, hsub⟩ := hc.isCompact.isBounded.subset_ball_lt (0 : ℝ) (0 : ℝ)
  refine ⟨-R, R, by linarith, ?_⟩
  simpa only [Real.ball_zero_eq_Ioo] using hsub

/-- The actual interval-integral primitive with a specified base point. -/
def primitive (a : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in a..x, φ t

/-- The primitive of a continuous test has its actual derivative at every point. -/
theorem hasDerivAt_primitive {φ : ℝ → ℝ} (hφ : Continuous φ) (a x : ℝ) :
    HasDerivAt (primitive a φ) (φ x) x :=
  (hφ.integral_hasStrictDerivAt a x).hasDerivAt

/-- The actual primitive of a smooth test is smooth. -/
theorem contDiff_primitive {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (a : ℝ) :
    ContDiff ℝ ∞ (primitive a φ) := by
  refine contDiff_infty_iff_deriv.mpr ⟨?_, ?_⟩
  · intro x
    exact (hasDerivAt_primitive hφ.continuous a x).differentiableAt
  · have hderiv : deriv (primitive a φ) = φ :=
      funext fun x => (hasDerivAt_primitive hφ.continuous a x).deriv
    rw [hderiv]
    exact hφ

/-- An integral anchored left of the support vanishes throughout its left exterior. -/
theorem primitive_eq_zero_of_le {φ : ℝ → ℝ} {a x : ℝ}
    (hs : Function.support φ ⊆ Ioi a) (hx : x ≤ a) : primitive a φ x = 0 := by
  have hz : EqOn φ (fun _ => (0 : ℝ)) (uIcc a x) := by
    intro t ht
    rw [uIcc_of_ge hx] at ht
    by_contra hn
    exact (not_lt_of_ge ht.2) (hs hn)
  exact (intervalIntegral.integral_congr hz).trans intervalIntegral.integral_zero

/-- Once the upper endpoint contains the support, the primitive equals the full integral. -/
theorem primitive_eq_integral_of_ge {φ : ℝ → ℝ} {a b x : ℝ}
    (hs : Function.support φ ⊆ Ioc a b) (hx : b ≤ x) :
    primitive a φ x = ∫ t, φ t := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  exact ⟨(hs ht).1, (hs ht).2.trans hx⟩

/-- Zero total integral removes the primitive's right constant, so its support
stays inside the closed enclosing interval. -/
theorem tsupport_primitive_subset {φ : ℝ → ℝ} {a b : ℝ}
    (hs : tsupport φ ⊆ Ioo a b) (hzero : (∫ x, φ x) = 0) :
    tsupport (primitive a φ) ⊆ Icc a b := by
  have hleft : Function.support φ ⊆ Ioi a := fun x hx => (hs (subset_tsupport φ hx)).1
  have hright : Function.support φ ⊆ Ioc a b :=
    fun x hx => ⟨(hs (subset_tsupport φ hx)).1, (hs (subset_tsupport φ hx)).2.le⟩
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  simp only [mem_Icc, not_and_or, not_le] at hnot
  rcases hnot with hxa | hbx
  · exact hx (primitive_eq_zero_of_le hleft hxa.le)
  · exact hx ((primitive_eq_integral_of_ge hright hbx.le).trans hzero)

/-- The left-anchored primitive of a zero-mean test is compactly supported. -/
theorem hasCompactSupport_primitive {φ : ℝ → ℝ} {a b : ℝ}
    (hs : tsupport φ ⊆ Ioo a b) (hzero : (∫ x, φ x) = 0) :
    HasCompactSupport (primitive a φ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_primitive_subset hs hzero)

/-- Every actual zero-mean smooth compact test is the derivative of a smooth compact test. -/
theorem exists_smooth_compact_primitive {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hzero : (∫ x, φ x) = 0) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ ∞ Ψ ∧ HasCompactSupport Ψ ∧
      ∀ x, HasDerivAt Ψ (φ x) x := by
  obtain ⟨a, b, _, hs⟩ := exists_support_interval hc
  exact ⟨primitive a φ, contDiff_primitive hφ a, hasCompactSupport_primitive hs hzero,
    hasDerivAt_primitive hφ.continuous a⟩

/-- An actual smooth compact test with integral one is supplied by a normalized bump. -/
theorem exists_normalized_smooth_compact :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∫ x, η x) = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, ?_, b.hasCompactSupport_normed, b.integral_normed⟩
  exact b.contDiff_normed

end FoliationQM.CompactTestPrimitive
