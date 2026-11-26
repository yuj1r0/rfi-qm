module

public import FoliationQM.PolarTangentEquiv
public import FoliationQM.StationaryAction

/-!
# Smooth compact polar tangent variations

Source: v13 `thm:kahler`. On a supplied smooth positive-density real-phase
chart, polar tangent variations and complex test fields correspond with
their actual smoothness and compact support. Stationarity here is tested
along the affine complex curves with these tangent vectors. Nonlinear
affine density/phase curves require a separate integrated chain rule.
-/
@[expose] public section

namespace FoliationQM.PolarTestVariations

open PolarTangentEquiv ActionDensity ActionVariation StationaryAction
open scoped ComplexConjugate ContDiff
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The positive-density polar map preserves any available smoothness. -/
theorem contDiff_actionField (p : MassiveParameters) {ρ S : E → ℝ}
    {n : WithTop ℕ∞} (hρ : ContDiff ℝ n ρ) (hS : ContDiff ℝ n S)
    (hpos : ∀ x, 0 < ρ x) : ContDiff ℝ n (actionField p ρ S) := by
  have hR := Complex.ofRealCLM.contDiff.comp (hρ.sqrt (fun x => ne_of_gt (hpos x)))
  have hSc := Complex.ofRealCLM.contDiff.comp (hS.div_const p.hbar)
  exact hR.mul ((hSc.mul (contDiff_const (c := Complex.I))).cexp)

/-- A compact pair of density/action increments induces a complex field. -/
noncomputable def testTangent (p : MassiveParameters) (ρ S a b : E → ℝ) : E → ℂ :=
  fun x => tangent p (ρ x) (actionField p ρ S x) (a x) (b x)

/-- Smoothness of the forward tangent map on the positive chart. -/
theorem contDiff_testTangent (p : MassiveParameters) {ρ S a b : E → ℝ}
    {n : WithTop ℕ∞} (hρ : ContDiff ℝ n ρ) (hS : ContDiff ℝ n S)
    (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n b) (hpos : ∀ x, 0 < ρ x) :
    ContDiff ℝ n (testTangent p ρ S a b) := by
  have hden : ∀ x, (2 : ℝ) * ρ x ≠ 0 :=
    fun x => mul_ne_zero (by norm_num) (ne_of_gt (hpos x))
  exact (contDiff_actionField p hρ hS hpos).mul
    ((Complex.ofRealCLM.contDiff.comp (ha.div (contDiff_const.mul hρ) hden)).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hb.div_const p.hbar))))

omit [NormedSpace ℝ E] in
/-- The forward tangent introduces no support outside the two real tests. -/
theorem hasCompactSupport_testTangent (p : MassiveParameters) (ρ S : E → ℝ)
    {a b : E → ℝ} (ha : HasCompactSupport a) (hb : HasCompactSupport b) :
    HasCompactSupport (testTangent p ρ S a b) := by
  have ha' : HasCompactSupport (fun x => a x / (2 * ρ x)) := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using ha.mul_right (f' := fun x => (2 * ρ x)⁻¹)
  have hb' : HasCompactSupport (fun x => b x / p.hbar) := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using hb.mul_right (f' := fun _ => p.hbar⁻¹)
  exact ((ha'.comp_left (g := fun r : ℝ => (r : ℂ)) rfl).add
    (hb'.comp_left (g := fun r : ℝ => (r : ℂ)) rfl).mul_left).mul_left

/-- The inverse density increment is smooth for smooth background and test. -/
theorem contDiff_densityVariation {ψ η : E → ℂ} {n : WithTop ℕ∞}
    (hψ : ContDiff ℝ n ψ) (hη : ContDiff ℝ n η) :
    ContDiff ℝ n (fun x => densityVariation (ψ x) (η x)) := by
  exact contDiff_const.mul (Complex.reCLM.contDiff.comp
    ((Complex.conjCLE.contDiff.comp hψ).mul hη))

/-- The inverse phase increment is smooth on a positive-density chart. -/
theorem contDiff_phaseVariation (p : MassiveParameters) {ρ : E → ℝ} {ψ η : E → ℂ}
    {n : WithTop ℕ∞} (hρ : ContDiff ℝ n ρ) (hψ : ContDiff ℝ n ψ)
    (hη : ContDiff ℝ n η) (hpos : ∀ x, 0 < ρ x) :
    ContDiff ℝ n (fun x => phaseVariation p (ρ x) (ψ x) (η x)) := by
  exact (contDiff_const.mul (Complex.imCLM.contDiff.comp
    ((Complex.conjCLE.contDiff.comp hψ).mul hη))).div hρ (fun x => ne_of_gt (hpos x))

omit [NormedSpace ℝ E] in
/-- The inverse density increment inherits the complex test's support. -/
theorem hasCompactSupport_densityVariation (ψ : E → ℂ) {η : E → ℂ}
    (hc : HasCompactSupport η) :
    HasCompactSupport (fun x => densityVariation (ψ x) (η x)) := by
  exact (hc.mul_left (f := fun x => conj (ψ x))).comp_left
    (g := fun z : ℂ => 2 * z.re) (by simp)

omit [NormedSpace ℝ E] in
/-- Division by the positive background introduces no new test support. -/
theorem hasCompactSupport_phaseVariation (p : MassiveParameters) (ρ : E → ℝ)
    (ψ : E → ℂ) {η : E → ℂ} (hc : HasCompactSupport η) :
    HasCompactSupport (fun x => phaseVariation p (ρ x) (ψ x) (η x)) := by
  have hc' := (hc.mul_left (f := fun x => conj (ψ x))).comp_left
    (g := fun z : ℂ => p.hbar * z.im) (by simp)
  simpa only [phaseVariation, div_eq_mul_inv, Pi.mul_def, Function.comp_def] using
    hc'.mul_right (f' := fun x => (ρ x)⁻¹)

/-- Every smooth compact complex test has smooth compact density and phase
increments. Positivity is pointwise; no uniform density bound is assumed. -/
theorem exists_testTangent (p : MassiveParameters) {ρ S : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S) (hpos : ∀ x, 0 < ρ x)
    {η : E → ℂ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    ∃ a b : E → ℝ, ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      HasCompactSupport a ∧ HasCompactSupport b ∧ testTangent p ρ S a b = η := by
  let ψ := actionField p ρ S
  have hψ := contDiff_actionField p hρ hS hpos
  refine ⟨fun x => densityVariation (ψ x) (η x),
    fun x => phaseVariation p (ρ x) (ψ x) (η x),
    contDiff_densityVariation hψ hη, contDiff_phaseVariation p hρ hψ hη hpos,
    hasCompactSupport_densityVariation ψ hc,
    hasCompactSupport_phaseVariation p ρ ψ hc, ?_⟩
  funext x
  exact tangent_inverse p (hpos x) (actionField_conj_mul p ρ S x (hpos x).le) (η x)

/-- Testing the actual quadratic action along every induced polar tangent
is equivalent to testing every complex direction. These are affine curves
in the complex field; this does not assert an integrated nonlinear chain rule. -/
theorem stationary_iff_polar_tangent_tests (p : MassiveParameters) {ρ S : Covector → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S) (hpos : ∀ x, 0 < ρ x)
    (e : Fin 4 → Covector)
    (hfinite : Integrable (fun x =>
      (fieldPairing p (actionField p ρ S) (actionField p ρ S) e x).re)) :
    Stationary p (actionField p ρ S) e ↔
      ∀ a b : Covector → ℝ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
        HasCompactSupport a → HasCompactSupport b →
        HasDerivAt (fun t : ℝ => action p
          (fun x => actionField p ρ S x + t * testTangent p ρ S a b x) e volume) 0 0 := by
  constructor
  · intro hs a b ha hb hca hcb
    exact hs.2 _ (contDiff_testTangent p hρ hS ha hb hpos)
      (hasCompactSupport_testTangent p ρ S hca hcb)
  · intro ht
    refine ⟨hfinite, ?_⟩
    intro η hη hc
    obtain ⟨a, b, ha, hb, hca, hcb, heq⟩ := exists_testTangent p hρ hS hpos hη hc
    simpa only [heq] using ht a b ha hb hca hcb

/-- The compact polar tangent test criterion has exactly the KG zero set
on a supplied smooth positive-density chart with finite action. -/
theorem polar_tangent_tests_iff_kgOperator (p : MassiveParameters) {ρ S : Covector → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S) (hpos : ∀ x, 0 < ρ x)
    (e : Fin 4 → Covector)
    (hfinite : Integrable (fun x =>
      (fieldPairing p (actionField p ρ S) (actionField p ρ S) e x).re)) :
    (∀ a b : Covector → ℝ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
        HasCompactSupport a → HasCompactSupport b →
        HasDerivAt (fun t : ℝ => action p
          (fun x => actionField p ρ S x + t * testTangent p ρ S a b x) e volume) 0 0) ↔
      ∀ x, FlatIntegrationByParts.kgOperator p (actionField p ρ S) e x = 0 := by
  rw [← stationary_iff_polar_tangent_tests p hρ hS hpos e hfinite]
  exact stationary_iff_kgOperator p e
    ((contDiff_actionField p hρ hS hpos).of_le (by norm_num)) hfinite

end FoliationQM.PolarTestVariations
