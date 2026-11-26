module

public import FoliationQM.CompactTestPrimitive
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The actual complex primitive of a locally integrable derivative

Sources: v13 eq:cramer_rao and thm:uncertainty, analytic component kind C.
One complex interval integral is continuous, locally absolutely continuous,
and differentiates to its integrand almost everywhere. Its signed compact-test
identity is derived from real-component absolute-continuity integration by
parts. Every full test integral is genuinely finite. No representative theorem,
boundary decay, score pairing or Sobolev equivalence is an input here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ComplexIntervalPrimitive

open MeasureTheory Set
open scoped ContDiff

private theorem intervalIntegrable_of_local {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : ℝ → E} (hv : LocallyIntegrable v volume) (a b : ℝ) :
    IntervalIntegrable v volume a b :=
  intervalIntegrable_iff.mpr <|
    (hv.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc

/-- The single actual complex primitive, anchored at zero. -/
def primitive (v : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..x, v t

/-- Local integrability gives continuity of the actual complex primitive. -/
theorem continuous_primitive {v : ℝ → ℂ} (hv : LocallyIntegrable v volume) :
    Continuous (primitive v) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_of_local hv) 0

/-- The genuine derivative of the primitive equals its integrand almost everywhere. -/
theorem ae_hasDerivAt_primitive {v : ℝ → ℂ} (hv : LocallyIntegrable v volume) :
    ∀ᵐ x, HasDerivAt (primitive v) (v x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hv] with x hx
  exact hx 0

/-- The derivative equality retains the almost-everywhere qualification. -/
theorem ae_deriv_primitive {v : ℝ → ℂ} (hv : LocallyIntegrable v volume) :
    deriv (primitive v) =ᵐ[volume] v := by
  filter_upwards [ae_hasDerivAt_primitive hv] with x hx
  exact hx.deriv

/-- Real projection commutes with this genuinely finite interval integral. -/
theorem re_primitive {v : ℝ → ℂ} (hv : LocallyIntegrable v volume) (x : ℝ) :
    (primitive v x).re = ∫ t in (0 : ℝ)..x, (v t).re :=
  (Complex.reCLM.intervalIntegral_comp_comm (intervalIntegrable_of_local hv 0 x)).symm

/-- Imaginary projection commutes with the same interval integral. -/
theorem im_primitive {v : ℝ → ℂ} (hv : LocallyIntegrable v volume) (x : ℝ) :
    (primitive v x).im = ∫ t in (0 : ℝ)..x, (v t).im :=
  (Complex.imCLM.intervalIntegral_comp_comm (intervalIntegrable_of_local hv 0 x)).symm

private theorem local_re {v : ℝ → ℂ} (hv : LocallyIntegrable v volume) :
    LocallyIntegrable (fun x => (v x).re) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact (hv.integrableOn_isCompact hK).re

private theorem local_im {v : ℝ → ℂ} (hv : LocallyIntegrable v volume) :
    LocallyIntegrable (fun x => (v x).im) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact (hv.integrableOn_isCompact hK).im

private theorem real_primitive_ac {w : ℝ → ℝ} (hw : LocallyIntegrable w volume)
    (a b : ℝ) : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, w t) a b := by
  have ha := (intervalIntegrable_of_local hw a b).absolutelyContinuousOnInterval_intervalIntegral
    (c := a) left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => ∫ t in (0 : ℝ)..a, w t) a b :=
    (contDiff_const : ContDiff ℝ 1 _).contDiffOn.absolutelyContinuousOnInterval
  apply (hc.add ha).congr
  intro x _
  exact intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_of_local hw 0 a) (intervalIntegrable_of_local hw a x)

/-- The actual complex primitive is absolutely continuous on every finite interval.
The real proof shifts its anchor into that interval before applying the primitive theorem. -/
theorem absolutelyContinuousOnInterval_primitive {v : ℝ → ℂ}
    (hv : LocallyIntegrable v volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (primitive v) a b := by
  have hr : AbsolutelyContinuousOnInterval (fun x => (primitive v x).re) a b := by
    apply (real_primitive_ac (local_re hv) a b).congr
    intro x _
    exact (re_primitive hv x).symm
  have hi : AbsolutelyContinuousOnInterval (fun x => (primitive v x).im) a b := by
    apply (real_primitive_ac (local_im hv) a b).congr
    intro x _
    exact (im_primitive hv x).symm
  have hrc := Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hr
  have hic := Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hi
  apply (hrc.add (hic.const_smul Complex.I)).congr
  intro x _
  change ((primitive v x).re : ℂ) + Complex.I * ((primitive v x).im : ℂ) = primitive v x
  rw [mul_comm]
  exact Complex.re_add_im _

/-- Multiplying the integrand by a compact continuous real test is genuinely integrable. -/
theorem integrable_test {v : ℝ → ℂ} (hv : LocallyIntegrable v volume)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun x => φ x • v x) volume :=
  hv.integrable_smul_left_of_hasCompactSupport hφ hs

/-- The primitive paired with the derivative of a compact smooth test is genuinely integrable. -/
theorem integrable_deriv_test_primitive {v : ℝ → ℂ} (hv : LocallyIntegrable v volume)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    Integrable (fun x => deriv φ x • primitive v x) volume :=
  (continuous_primitive hv).locallyIntegrable.integrable_smul_left_of_hasCompactSupport
    (hφ.continuous_deriv (by simp)) hs.deriv

private theorem real_test_identity {w : ℝ → ℝ} (hw : LocallyIntegrable w volume)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    Integrable (fun x => φ x * w x) volume ∧
    Integrable (fun x => deriv φ x * (∫ t in (0 : ℝ)..x, w t)) volume ∧
    (∫ x, φ x * w x) = -(∫ x, deriv φ x * (∫ t in (0 : ℝ)..x, w t)) := by
  let P : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, w t
  have hP : Continuous P :=
    intervalIntegral.continuous_primitive (intervalIntegrable_of_local hw) 0
  refine ⟨hw.integrable_smul_left_of_hasCompactSupport hφ.continuous hs,
    hP.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (hφ.continuous_deriv (by simp)) hs.deriv, ?_⟩
  obtain ⟨a, b, _, hab⟩ := CompactTestPrimitive.exists_support_interval hs
  have hφa : φ a = 0 := image_eq_zero_of_notMem_tsupport (by
    intro ha
    exact (lt_irrefl a) (hab ha).1)
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hb
    exact (lt_irrefl b) (hab hb).2)
  have hφac : AbsolutelyContinuousOnInterval φ a b :=
    (hφ.of_le (by simp) : ContDiff ℝ 1 φ).contDiffOn.absolutelyContinuousOnInterval
  have hibp := (real_primitive_ac hw a b).integral_mul_deriv_eq_deriv_mul hφac
  have hderiv : deriv P =ᵐ[volume] w := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hw] with x hx
    exact (hx 0).deriv
  have hreplace : (∫ x in a..b, deriv P x * φ x) = ∫ x in a..b, w x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with x hx _
    rw [hx]
  have hsupport : Function.support φ ⊆ Ioc a b := fun x hx =>
    ⟨(hab (subset_tsupport φ hx)).1, (hab (subset_tsupport φ hx)).2.le⟩
  have hdSupport : Function.support (deriv φ) ⊆ Ioc a b := fun x hx =>
    ⟨(hab (support_deriv_subset hx)).1, (hab (support_deriv_subset hx)).2.le⟩
  have hleft : (∫ x in a..b, P x * deriv φ x) = ∫ x, P x * deriv φ x :=
    intervalIntegral.integral_eq_integral_of_support_subset
      ((Function.support_mul_subset_right P (deriv φ)).trans hdSupport)
  have hright : (∫ x in a..b, w x * φ x) = ∫ x, w x * φ x :=
    intervalIntegral.integral_eq_integral_of_support_subset
      ((Function.support_mul_subset_right w φ).trans hsupport)
  change (∫ x in a..b, P x * deriv φ x) =
    P b * φ b - P a * φ a - ∫ x in a..b, deriv P x * φ x at hibp
  rw [hφa, hφb, mul_zero, mul_zero, sub_self, zero_sub, hreplace, hleft, hright] at hibp
  have hfinal : (∫ x, w x * φ x) = -(∫ x, P x * deriv φ x) := by linarith
  simpa only [mul_comm] using hfinal

/-- The actual primitive satisfies the signed weak-test identity, derived by real-component IBP. -/
theorem integral_test {v : ℝ → ℂ} (hv : LocallyIntegrable v volume)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    (∫ x, φ x • v x) = -(∫ x, deriv φ x • primitive v x) := by
  have hvtest := integrable_test hv hφ.continuous hs
  have hGtest := integrable_deriv_test_primitive hv hφ hs
  have hr := (real_test_identity (local_re hv) φ hφ hs).2.2
  have hi := (real_test_identity (local_im hv) φ hφ hs).2.2
  apply Complex.ext
  · calc
      (∫ x, φ x • v x).re = ∫ x, φ x * (v x).re := by
        simpa only [map_smul, Complex.reCLM_apply, smul_eq_mul] using
          (Complex.reCLM.integral_comp_comm hvtest).symm
      _ = -(∫ x, deriv φ x * (primitive v x).re) := by
        simpa only [re_primitive hv] using hr
      _ = (-(∫ x, deriv φ x • primitive v x)).re := by
        rw [Complex.neg_re]
        exact congrArg Neg.neg (by
          simpa only [map_smul, Complex.reCLM_apply, smul_eq_mul] using
            Complex.reCLM.integral_comp_comm hGtest)
  · calc
      (∫ x, φ x • v x).im = ∫ x, φ x * (v x).im := by
        simpa only [map_smul, Complex.imCLM_apply, smul_eq_mul] using
          (Complex.imCLM.integral_comp_comm hvtest).symm
      _ = -(∫ x, deriv φ x * (primitive v x).im) := by
        simpa only [im_primitive hv] using hi
      _ = (-(∫ x, deriv φ x • primitive v x)).im := by
        rw [Complex.neg_im]
        exact congrArg Neg.neg (by
          simpa only [map_smul, Complex.imCLM_apply, smul_eq_mul] using
            Complex.imCLM.integral_comp_comm hGtest)

end FoliationQM.ComplexIntervalPrimitive
