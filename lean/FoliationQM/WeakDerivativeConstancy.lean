module

public import FoliationQM.CompactTestPrimitive
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Actual zero weak derivative implies almost-everywhere constancy

Sources: v13 eq:cramer_rao and thm:uncertainty. Kind C, analytic component.
A real Banach-valued locally integrable function whose actual derivative-test
pairings vanish is constant almost everywhere. The proof constructs a genuine
compact primitive of each zero-mean test and uses the fundamental lemma.
No pointwise regularity or absolutely continuous representative is an input.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.WeakDerivativeConstancy

open MeasureTheory Filter
open scoped ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {h : ℝ → F}

/-- A normalized compact test determines every genuine test pairing of a function
with zero weak derivative. -/
theorem test_pairing_eq_constant [CompleteSpace F] (hloc : LocallyIntegrable h volume)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, deriv φ x • h x) = 0)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηi : (∫ x, η x) = 1)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθs : HasCompactSupport θ) :
    (∫ x, θ x • h x) = (∫ x, θ x) • (∫ x, η x • h x) := by
  let c : ℝ := ∫ x, θ x
  let q : ℝ → ℝ := fun x => θ x - c * η x
  have hq : ContDiff ℝ ∞ q := hθ.sub (contDiff_const.mul hη)
  have hqs : HasCompactSupport q := hθs.sub (hηs.mul_left (f := fun _ => c))
  have hθint : Integrable θ volume := hθ.continuous.integrable_of_hasCompactSupport hθs
  have hηint : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hηs
  have hqi : (∫ x, q x) = 0 := by
    dsimp only [q]
    rw [integral_sub hθint (hηint.const_mul c), integral_const_mul, hηi, mul_one]
    exact sub_self c
  obtain ⟨Ψ, hΨ, hΨs, hΨd⟩ :=
    CompactTestPrimitive.exists_smooth_compact_primitive hq hqs hqi
  have hderiv : deriv Ψ = q := funext fun x => (hΨd x).deriv
  have hz := hweak Ψ hΨ hΨs
  rw [hderiv] at hz
  have hθh := hloc.integrable_smul_left_of_hasCompactSupport hθ.continuous hθs
  have hηh := hloc.integrable_smul_left_of_hasCompactSupport hη.continuous hηs
  have hsplit : (∫ x, q x • h x) =
      (∫ x, θ x • h x) - c • (∫ x, η x • h x) := by
    simp_rw [q, sub_smul, mul_smul]
    rw [integral_sub hθh (hηh.fun_smul c), integral_smul]
  rw [hsplit] at hz
  exact sub_eq_zero.mp hz

/-- Genuine zero derivative-test pairings imply constancy almost everywhere,
without imposing pointwise continuity on the original representative. -/
theorem exists_ae_const_of_test_derivative_eq_zero [CompleteSpace F]
    (hloc : LocallyIntegrable h volume)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, deriv φ x • h x) = 0) :
    ∃ C : F, h =ᵐ[volume] fun _ => C := by
  obtain ⟨η, hη, hηs, hηi⟩ := CompactTestPrimitive.exists_normalized_smooth_compact
  refine ⟨∫ x, η x • h x, ae_eq_of_integral_contDiff_smul_eq hloc
    (locallyIntegrable_const _) ?_⟩
  intro θ hθ hθs
  rw [integral_smul_const]
  exact test_pairing_eq_constant hloc hweak hη hηs hηi hθ hθs

end FoliationQM.WeakDerivativeConstancy
