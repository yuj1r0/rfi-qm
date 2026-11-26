module

public import FoliationQM.TwoBodyFisherVariation
public import FoliationQM.TwoBodyActions
public import FoliationQM.TwoBodyMadelung

/-!
# Independent density variation of the two-particle action

The classical term is affine in the density. The compact perturbation
preserves positivity near zero and the integrated Fisher variation gives
the Bohm potential. Together they recover the negative Hamilton–Jacobi
pairing as the derivative of the actual relative action.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyDensityVariation

open MeasureTheory TwoBodyCoordinates TwoBodyActionDensity TwoBodyActions
open TwoBodySchrodingerResidual TwoBodyFisherVariation
open scoped Topology BigOperators

/-- Classical Hamilton–Jacobi residual before adding the Bohm potential. -/
def classical (m₁ m₂ : ℝ) (V S : Point → ℝ) (p : Point) : ℝ :=
  Dt S p + (∑ j, (D (axis j) S p)^2 / (2 * mass m₁ m₂ j)) + V p

/-- Continuous potential and continuously differentiable phase give a continuous classical residual. -/
theorem continuous_classical (m₁ m₂ : ℝ) {V S : Point → ℝ} (hV : Continuous V)
    (hS : ContDiff ℝ 1 S) : Continuous (classical m₁ m₂ V S) := by
  have hd (v : Point) : Continuous (D v S) :=
    (hS.continuous_fderiv (by norm_num)).clm_apply continuous_const
  unfold classical
  exact ((hd timeAxis).add (continuous_finsetSum _ fun j _ =>
    ((hd (axis j)).pow 2).div_const _)).add hV

/-- A compact density test times the classical residual is absolutely integrable. -/
theorem integrable_test_classical (m₁ m₂ : ℝ) {V S a : Point → ℝ} (hV : Continuous V)
    (hS : ContDiff ℝ 1 S) (ha : Continuous a) (hc : HasCompactSupport a) :
    Integrable (fun p => a p * classical m₁ m₂ V S p) :=
  (ha.mul (continuous_classical m₁ m₂ hV hS)).integrable_of_hasCompactSupport hc.mul_right

/-- The density variation changes the Lagrangian by an affine classical term and
the negative change in the Fisher integrand, for every parameter value. -/
theorem difference (h m₁ m₂ : ℝ) (V ρ S a : Point → ℝ) (s : ℝ) (p : Point) :
    densityL h m₁ m₂ V (fun z => ρ z+s*a z) S p - densityL h m₁ m₂ V ρ S p =
      -s * (a p * classical m₁ m₂ V S p) -
      (fisherL h m₁ m₂ (fun z => ρ z+s*a z) p - fisherL h m₁ m₂ ρ p) := by
  unfold densityL classical
  ring

/-- Near zero the full relative Lagrangian density is an integrable perturbation. -/
theorem integrable_difference (h m₁ m₂ : ℝ) {V ρ S a : Point → ℝ} (hV : Continuous V)
    (hρ : ContDiff ℝ 1 ρ) (hp : ∀ p, 0 < ρ p) (hS : ContDiff ℝ 1 S)
    (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    ∀ᶠ s in 𝓝 (0 : ℝ), Integrable (fun p =>
      densityL h m₁ m₂ V (fun z => ρ z+s*a z) S p - densityL h m₁ m₂ V ρ S p) := by
  filter_upwards [integrable_fisher_change h m₁ m₂ hρ hp ha hc] with s hs
  simp only [difference]
  exact ((integrable_test_classical m₁ m₂ hV hS ha.continuous hc).const_mul (-s)).sub hs

/-- Compact density variations preserve absolute integrability of the classical contribution. -/
theorem integrable_classical_perturbed (m₁ m₂ : ℝ) {V ρ S a : Point → ℝ} (hV : Continuous V)
    (hS : ContDiff ℝ 1 S) (ha : Continuous a) (hc : HasCompactSupport a)
    (hi : Integrable (classicalDensity m₁ m₂ V ρ S)) (s : ℝ) :
    Integrable (classicalDensity m₁ m₂ V (fun z => ρ z+s*a z) S) := by
  apply (hi.add ((integrable_test_classical m₁ m₂ hV hS ha hc).const_mul s)).congr
  filter_upwards with p
  change ρ p * classical m₁ m₂ V S p + s * (a p * classical m₁ m₂ V S p) =
    (ρ p + s * a p) * classical m₁ m₂ V S p
  ring

/-- Independent affine variation of density gives the negative Hamilton–Jacobi–Bohm pairing. -/
theorem hasDerivAt_relative (h m₁ m₂ : ℝ) {V ρ S a : Point → ℝ} (hV : Continuous V)
    (hρ : ContDiff ℝ 2 ρ) (hp : ∀ p, 0 < ρ p) (hS : ContDiff ℝ 1 S)
    (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    HasDerivAt (fun s => relative (densityL h m₁ m₂ V ρ S)
      (densityL h m₁ m₂ V (fun z => ρ z + s*a z) S))
      (-(∫ p, a p * hamiltonJacobi h m₁ m₂ V (fun z => √(ρ z)) S p)) 0 := by
  let B := ∫ p, a p * classical m₁ m₂ V S p
  let F := fun s : ℝ => ∫ p, fisherL h m₁ m₂ (fun z => ρ z+s*a z) p - fisherL h m₁ m₂ ρ p
  have hiB := integrable_test_classical m₁ m₂ hV hS ha.continuous hc
  have hiQ := TwoBodyBohmGreen.integrable_test_quantum h m₁ m₂ (hρ.sqrt fun p => (hp p).ne')
    (fun p => Real.sqrt_pos.mpr (hp p)) ha hc
  have he : (fun s => relative (densityL h m₁ m₂ V ρ S)
      (densityL h m₁ m₂ V (fun z => ρ z + s*a z) S)) =ᶠ[𝓝 0] fun s => -s * B - F s := by
    filter_upwards [integrable_fisher_change h m₁ m₂ (hρ.of_le (by norm_num)) hp ha hc] with s hs
    unfold relative
    simp only [difference, integral_sub (hiB.const_mul (-s)) hs, integral_const_mul, B, F]
  have hd := (((hasDerivAt_id (0 : ℝ)).neg.mul_const B).sub (fisher_relative h m₁ m₂ hρ hp ha hc))
  have hg : (-(1 : ℝ)) * B - (∫ p, a p * quantum h m₁ m₂ (fun z => √(ρ z)) p) =
      -(∫ p, a p * hamiltonJacobi h m₁ m₂ V (fun z => √(ρ z)) S p) := by
    change _ = -(∫ p, a p * (classical m₁ m₂ V S p + quantum h m₁ m₂ (fun z => √(ρ z)) p))
    simp only [mul_add, integral_add hiB hiQ, B]
    ring
  rw [← hg]
  exact hd.congr_of_eventuallyEq he

end FoliationQM.TwoBodyDensityVariation
