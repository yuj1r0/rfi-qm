module

public import FoliationQM.TwoBodySourceVariations
public import FoliationQM.TwoBodyComplexVariation
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The two-body Euler–Lagrange equations on joint spacetime

Stationarity in each independent field means vanishing of the actual derivative of the
relative action for every smooth compactly supported variation. The fundamental lemma
and continuity recover the pointwise equations of v13 `thm:entanglement_nosignaling`.
For the complex wave, real and purely imaginary tests detect both components.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyEulerLagrange

open MeasureTheory TwoBodyCoordinates TwoBodyActionDensity TwoBodyActions
open TwoBodySchrodingerResidual TwoBodyPolarContinuity
open scoped ContDiff BigOperators

/-- Stationarity for arbitrary compact smooth real density variations at fixed phase. -/
def DensityStationary (h m₁ m₂ : ℝ) (V ρ S : Point → ℝ) : Prop :=
  ∀ a : Point → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a →
    HasDerivAt (fun s => relative (densityL h m₁ m₂ V ρ S)
      (densityL h m₁ m₂ V (fun z => ρ z + s*a z) S)) 0 0

/-- Stationarity for arbitrary compact smooth real phase variations at fixed density. -/
def PhaseStationary (h m₁ m₂ : ℝ) (V ρ S : Point → ℝ) : Prop :=
  ∀ b : Point → ℝ, ContDiff ℝ ∞ b → HasCompactSupport b →
    HasDerivAt (fun s => relative (densityL h m₁ m₂ V ρ S)
      (densityL h m₁ m₂ V ρ (fun z => S z + s*b z))) 0 0

/-- Stationarity of the quadratic action for arbitrary compact smooth complex wave variations. -/
def ComplexStationary (h m₁ m₂ : ℝ) (V : Point → ℝ) (ψ : Point → ℂ) : Prop :=
  ∀ η : Point → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η →
    HasDerivAt (fun s => relative (complexL h m₁ m₂ V ψ)
      (complexL h m₁ m₂ V (TwoBodyComplexVariation.variation s ψ η))) 0 0

private theorem continuous_D {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (h : ContDiff ℝ 1 f) (v : Point) : Continuous (D v f) :=
  (h.continuous_fderiv (by decide)).clm_apply continuous_const

private theorem continuous_DD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (h : ContDiff ℝ 2 f) (v : Point) : Continuous (D v (D v f)) :=
  continuous_D ((h.fderiv_right (m := 1) (by decide)).clm_apply contDiff_const) v

/-- With a C² amplitude away from zero the physical Bohm potential is continuous. -/
theorem continuous_quantum (h m₁ m₂ : ℝ) {R : Point → ℝ} (hR : ContDiff ℝ 2 R)
    (hn : ∀ p, R p ≠ 0) : Continuous (quantum h m₁ m₂ R) := by
  unfold quantum
  exact (continuous_finsetSum _ fun j _ => continuous_const.mul
    (continuous_DD hR (axis j))).neg.div hR.continuous hn

/-- The Hamilton–Jacobi–Bohm residual is continuous on the positive physical density chart. -/
theorem continuous_hamiltonJacobi (h m₁ m₂ : ℝ) {V ρ S : Point → ℝ} (hV : Continuous V)
    (hρ : ContDiff ℝ 2 ρ) (hp : ∀ p, 0 < ρ p) (hS : ContDiff ℝ 1 S) :
    Continuous (hamiltonJacobi h m₁ m₂ V (fun p => √(ρ p)) S) :=
  (TwoBodyDensityVariation.continuous_classical m₁ m₂ hV hS).add
    (continuous_quantum h m₁ m₂ (hρ.sqrt fun p => (hp p).ne') (fun p => (Real.sqrt_pos.2 (hp p)).ne'))

/-- The C¹ density and C² phase make every term of the polar continuity residual continuous. -/
theorem continuous_continuity (m₁ m₂ : ℝ) {ρ S : Point → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hS : ContDiff ℝ 2 S) : Continuous (continuity m₁ m₂ ρ S) :=
  (continuous_D hρ timeAxis).add (continuous_finsetSum _ fun j _ =>
    continuous_D (contDiff_flux m₁ m₂ hρ hS j) (axis j))

/-- A C² wave and continuous real potential give a continuous Schrödinger residual. -/
theorem continuous_schrodinger (h m₁ m₂ : ℝ) {V : Point → ℝ} {ψ : Point → ℂ}
    (hV : Continuous V) (hψ : ContDiff ℝ 2 ψ) : Continuous (schrodinger h m₁ m₂ V ψ) := by
  unfold schrodinger
  exact ((continuous_const.mul (continuous_D (hψ.of_le (by decide)) timeAxis)).add
    (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_DD hψ (axis j)))).sub
      ((Complex.continuous_ofReal.comp hV).mul hψ.continuous)

/-- On the full joint spacetime, vanishing smooth compact real test pairings detect
a continuous real scalar at every point. -/
theorem real_test_zero {F : Point → ℝ} (hF : Continuous F)
    (ht : ∀ g : Point → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → (∫ p, g p * F p) = 0) :
    ∀ p, F p = 0 := by
  let := volume_isAddHaarMeasure
  have hae : F =ᵐ[volume] 0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hF.locallyIntegrable ht
  exact fun p => congrFun (Measure.eq_of_ae_eq hae hF continuous_zero) p

/-- Real and purely imaginary test waves separately recover both components of a
continuous complex residual from the real first variation. -/
theorem complex_test_zero {F : Point → ℂ} (hF : Continuous F)
    (ht : ∀ η : Point → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η →
      (∫ p, (star (η p) * F p).re) = 0) : ∀ p, F p = 0 := by
  have test (g : Point → ℝ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
      (∫ p, g p * (F p).re) = 0 ∧ (∫ p, g p * (F p).im) = 0 := by
    have hgc : ContDiff ℝ ∞ (fun p => (g p : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hcs : HasCompactSupport (fun p => (g p : ℂ)) := hc.comp_left (g := Complex.ofReal) rfl
    have hr := ht _ hgc hcs
    have hi := ht (fun p => Complex.I * (g p : ℂ)) (contDiff_const.mul hgc) hcs.mul_left
    constructor
    · simpa [Complex.star_def, Complex.mul_re] using hr
    · simpa [Complex.star_def, Complex.mul_re, Complex.mul_im] using hi
  have hr := real_test_zero (Complex.continuous_re.comp hF) (fun g hg hc => (test g hg hc).1)
  have hi := real_test_zero (Complex.continuous_im.comp hF) (fun g hg hc => (test g hg hc).2)
  exact fun p => Complex.ext (hr p) (hi p)

/-- Vanishing of every density variation is equivalent to the physical Hamilton–Jacobi–Bohm
equation at every point of joint spacetime. -/
theorem density_iff (h m₁ m₂ : ℝ) {V ρ S : Point → ℝ} (hV : Continuous V)
    (hρ : ContDiff ℝ 2 ρ) (hp : ∀ p, 0 < ρ p) (hS : ContDiff ℝ 1 S) :
    DensityStationary h m₁ m₂ V ρ S ↔ ∀ p, hamiltonJacobi h m₁ m₂ V (fun z => √(ρ z)) S p = 0 := by
  constructor
  · intro hstat
    apply real_test_zero (continuous_hamiltonJacobi h m₁ m₂ hV hρ hp hS)
    intro a ha hc
    have hd := TwoBodyDensityVariation.hasDerivAt_relative h m₁ m₂ hV hρ hp hS (ha.of_le (by norm_num)) hc
    exact neg_eq_zero.mp (hd.unique (hstat a ha hc))
  · intro he a ha hc
    have hd := TwoBodyDensityVariation.hasDerivAt_relative h m₁ m₂ hV hρ hp hS (ha.of_le (by norm_num)) hc
    simpa only [he, mul_zero, integral_zero, neg_zero] using hd

/-- Vanishing of every phase variation is equivalent to the polar continuity equation. -/
theorem phase_iff (h m₁ m₂ : ℝ) (V : Point → ℝ) {ρ S : Point → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hS : ContDiff ℝ 2 S) :
    PhaseStationary h m₁ m₂ V ρ S ↔ ∀ p, continuity m₁ m₂ ρ S p = 0 := by
  constructor
  · intro hstat
    apply real_test_zero (continuous_continuity m₁ m₂ hρ hS)
    intro b hb hc
    exact (TwoBodyPhaseVariation.hasDerivAt_relative h m₁ m₂ V hρ hS
      (hb.of_le (by norm_num)) hc).unique (hstat b hb hc)
  · intro he b hb hc
    have hd := TwoBodyPhaseVariation.hasDerivAt_relative h m₁ m₂ V hρ hS (hb.of_le (by norm_num)) hc
    simpa only [he, mul_zero, integral_zero] using hd

/-- Stationarity for all complex wave variations is equivalent to the full two-body
Schrödinger equation, with no nonvanishing hypothesis on the wave. -/
theorem complex_iff (h m₁ m₂ : ℝ) {V : Point → ℝ} {ψ : Point → ℂ}
    (hV : Continuous V) (hψ : ContDiff ℝ 2 ψ) :
    ComplexStationary h m₁ m₂ V ψ ↔ ∀ p, schrodinger h m₁ m₂ V ψ p = 0 := by
  constructor
  · intro hstat
    apply complex_test_zero (continuous_schrodinger h m₁ m₂ hV hψ)
    intro η hη hc
    have he := (TwoBodyComplexVariation.first_variation h m₁ m₂ hV hψ
      (hη.of_le (by norm_num)) hc).unique (hstat η hη hc)
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  · intro he η hη hc
    have hd := TwoBodyComplexVariation.first_variation h m₁ m₂ hV hψ (hη.of_le (by norm_num)) hc
    simpa only [he, mul_zero, Complex.zero_re, integral_zero] using hd

end FoliationQM.TwoBodyEulerLagrange
