module

public import FoliationQM.Madelung
public import FoliationQM.FlatIntegrationByParts
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Stationarity of the flat quadratic action

Source: v13 `thm:kahler`. Smooth compactly supported variations provide the
boundary condition on flat spacetime. All integrals are Lebesgue integrals,
and all derivatives are actual real derivatives. Polar inverse charts and
curved-spacetime stationary equivalence are separate claims.
-/
@[expose] public section

namespace FoliationQM.StationaryAction

open MeasureTheory
open ActionVariation FlatIntegrationByParts PolarSecondDifferential
open scoped ComplexConjugate ContDiff

/-- The real pairing against every complex smooth compactly supported test
function detects a continuous complex field, using the fundamental lemma. -/
theorem continuous_eq_zero_of_test_pairings (F : Covector → ℂ) (hF : Continuous F)
    (h : ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ x, (conj (η x) * F x).re = 0) : F = 0 := by
  apply MeasureTheory.Measure.eq_of_ae_eq (μ := volume) _ hF continuous_zero
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hF.locallyIntegrable
  intro g hg hgc
  have hgd : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hgc' : HasCompactSupport (fun x => (g x : ℂ)) :=
    hgc.comp_left (g := fun t : ℝ => (t : ℂ)) rfl
  have hgi : ContDiff ℝ ∞ (fun x => Complex.I * (g x : ℂ)) := contDiff_const.mul hgd
  have hgic : HasCompactSupport (fun x => Complex.I * (g x : ℂ)) := hgc'.mul_left
  have hr := h _ hgd hgc'
  have hi := h _ hgi hgic
  have hp : Integrable (fun x => (g x : ℂ) * F x) :=
    (hgd.continuous.mul hF).integrable_of_hasCompactSupport hgc'.mul_right
  have hpr : Integrable (fun x => g x • F x) := by
    simpa only [Complex.real_smul] using hp
  apply Complex.ext
  · have hre := integral_re hpr
    simp only [RCLike.re_eq_complex_re] at hre
    rw [← hre]
    simpa [Complex.real_smul] using hr
  · have him := integral_im hpr
    simp only [RCLike.im_eq_complex_im] at him
    rw [← him]
    simpa [Complex.real_smul, Complex.mul_re, Complex.mul_im] using hi

/-- Real form of the proved integration-by-parts formula. -/
theorem integral_re_fieldPairing_eq (p : MassiveParameters) {η ψ : Covector → ℂ}
    (hη : ContDiff ℝ 1 η) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport η) (e : Fin 4 → Covector) :
    (∫ x, (fieldPairing p η ψ e x).re) =
      -(∫ x, (conj (η x) * kgOperator p ψ e x).re) := by
  have h := congrArg Complex.re (integral_fieldPairing_eq p hη hψ hc e)
  have hp := integral_re (integrable_fieldPairing p hη hψ hc e)
  have hq := integral_re (integrable_test_kgOperator p hη hψ hc e)
  simp only [RCLike.re_eq_complex_re] at hp hq
  rw [Complex.neg_re, ← hp, ← hq] at h
  exact h

/-- The first derivative of the actual finite action, after integration by
parts. The variation is smooth and compactly supported. -/
theorem hasDerivAt_action_eq_kg_pairing (p : MassiveParameters)
    {ψ η : Covector → ℂ} (e : Fin 4 → Covector)
    (hψ : ContDiff ℝ 2 ψ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hfinite : Integrable (fun x => (fieldPairing p ψ ψ e x).re)) :
    HasDerivAt (fun t : ℝ => action p (fun x => ψ x + t * η x) e volume)
      (-2 * ∫ x, (conj (η x) * kgOperator p ψ e x).re) 0 := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hη2 : ContDiff ℝ 2 η := hη.of_le (by norm_num)
  have hcross := (integrable_fieldPairing p hη1 hψ hc e).re
  have htest := (integrable_fieldPairing p hη1 hη2 hc e).re
  have hd := hasDerivAt_action_variation p ψ η e volume
    (Filter.Eventually.of_forall (hψ.differentiable (by norm_num)))
    (Filter.Eventually.of_forall (hη.differentiable (by simp))) hfinite hcross htest
  rw [integral_re_fieldPairing_eq p hη1 hψ hc e] at hd
  convert hd using 1
  ring

/-- Stationarity includes finiteness of the actual real action density and
zero derivative along every smooth compactly supported complex variation. -/
def Stationary (p : MassiveParameters) (ψ : Covector → ℂ)
    (e : Fin 4 → Covector) : Prop :=
  Integrable (fun x => (fieldPairing p ψ ψ e x).re) ∧
    ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η →
      HasDerivAt (fun t : ℝ => action p (fun x => ψ x + t * η x) e volume) 0 0

/-- The quadratic action is stationary exactly when its actual dimensional
KG operator vanishes. This is a whole-flat-spacetime finite-action theorem. -/
theorem stationary_iff_kgOperator (p : MassiveParameters) {ψ : Covector → ℂ}
    (e : Fin 4 → Covector) (hψ : ContDiff ℝ 2 ψ)
    (hfinite : Integrable (fun x => (fieldPairing p ψ ψ e x).re)) :
    Stationary p ψ e ↔ ∀ x, kgOperator p ψ e x = 0 := by
  constructor
  · intro hs
    have heq := continuous_eq_zero_of_test_pairings (kgOperator p ψ e)
      (continuous_kgOperator p hψ e) (by
        intro η hη hc
        have hd := hasDerivAt_action_eq_kg_pairing p e hψ hη hc hfinite
        have hz := (hs.2 η hη hc).unique hd
        linarith)
    intro x
    exact congrFun heq x
  · intro hkg
    refine ⟨hfinite, ?_⟩
    intro η hη hc
    have hd := hasDerivAt_action_eq_kg_pairing p e hψ hη hc hfinite
    simpa only [hkg, mul_zero, Complex.zero_re, integral_zero, mul_zero] using hd

/-- The dimensional operator has the source's normalized KG zero set, using
the nonzero positive action scale. -/
theorem kgOperator_eq_zero_iff (p : MassiveParameters) (ψ : Covector → ℂ)
    (e : Fin 4 → Covector) (x : Covector) :
    kgOperator p ψ e x = 0 ↔
      box ψ e x + (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * ψ x) = 0 := by
  have hh : (p.hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt p.hbar_pos)
  have heq : kgOperator p ψ e x = (p.hbar : ℂ) ^ 2 *
      (box ψ e x + (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * ψ x)) := by
    simp only [kgOperator, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp
  rw [heq, mul_eq_zero, or_iff_right (pow_ne_zero 2 hh)]

/-- Source-coordinate specialization: stationary real quadratic action iff
the normalized KG equation, for C² fields with integrable real action density. -/
theorem stationary_iff_kleinGordon (p : MassiveParameters) {ψ : Covector → ℂ}
    (hψ : ContDiff ℝ 2 ψ)
    (hfinite : Integrable (fun x =>
      (fieldPairing p ψ ψ Madelung.coordinateVector x).re)) :
    Stationary p ψ Madelung.coordinateVector ↔ ∀ x,
      box ψ Madelung.coordinateVector x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * ψ x) = 0 := by
  rw [stationary_iff_kgOperator p Madelung.coordinateVector hψ hfinite]
  exact forall_congr' fun x => kgOperator_eq_zero_iff p ψ Madelung.coordinateVector x

end FoliationQM.StationaryAction
