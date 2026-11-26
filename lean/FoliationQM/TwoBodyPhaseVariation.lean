module

public import FoliationQM.TwoBodyActions
public import FoliationQM.TwoBodyPolarContinuity

/-!
# Compact phase variations of the two-particle action

The relative action along an affine phase line is exactly quadratic in
the parameter. Integration by parts identifies its first derivative at
zero with the full time and two-particle continuity residual.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyPhaseVariation

open MeasureTheory TwoBodyCoordinates TwoBodyActionDensity TwoBodyPolarContinuity TwoBodyActions
open scoped BigOperators

/-- Coefficient of the variation parameter, before integration by parts. -/
def linear (m₁ m₂ : ℝ) (ρ S b : Point → ℝ) (p : Point) : ℝ :=
  -(Dt b p * ρ p + ∑ j, D (axis j) b p * flux m₁ m₂ ρ S j p)

/-- Coefficient of the square of the variation parameter in the Lagrangian. -/
def quadratic (m₁ m₂ : ℝ) (ρ b : Point → ℝ) (p : Point) : ℝ :=
  -ρ p * ∑ j, (D (axis j) b p)^2 / (2 * mass m₁ m₂ j)

private theorem dir_affine {S b : Point → ℝ} {p : Point} (hS : DifferentiableAt ℝ S p)
    (hb : DifferentiableAt ℝ b p) (v : Point) (s : ℝ) :
    D v (fun z => S z + s*b z) p = D v S p + s*D v b p := by
  simp only [D, fderiv_fun_add hS (hb.const_mul _), fderiv_const_mul hb,
    add_apply, smul_apply, smul_eq_mul]

/-- The pointwise phase increment has exactly a linear and a quadratic term. -/
theorem density_expansion (h m₁ m₂ : ℝ) (V ρ : Point → ℝ) {S b : Point → ℝ} {p : Point}
    (hS : DifferentiableAt ℝ S p) (hb : DifferentiableAt ℝ b p) (s : ℝ) :
    densityL h m₁ m₂ V ρ (fun z => S z + s*b z) p - densityL h m₁ m₂ V ρ S p =
      s * linear m₁ m₂ ρ S b p + s^2 * quadratic m₁ m₂ ρ b p := by
  have H (u v m : ℝ) : (u+s*v)^2/(2*m) = u^2/(2*m) + s*(v*u/m) + s^2*(v^2/(2*m)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hf : (∑ j, D (axis j) b p * flux m₁ m₂ ρ S j p) =
      ρ p * ∑ j, D (axis j) b p * D (axis j) S p / mass m₁ m₂ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold flux
    ring
  simp only [densityL, linear, quadratic, Dt, dir_affine hS hb, H, Finset.sum_add_distrib,
    ← Finset.mul_sum, hf]
  ring

/-- Both polynomial coefficients vanish outside the topological support of the test. -/
theorem compact_coefficients (m₁ m₂ : ℝ) (ρ S : Point → ℝ) {b : Point → ℝ}
    (hc : HasCompactSupport b) :
    HasCompactSupport (linear m₁ m₂ ρ S b) ∧ HasCompactSupport (quadratic m₁ m₂ ρ b) := by
  constructor <;> apply HasCompactSupport.intro hc <;> intro p hp <;>
    simp [linear, quadratic, Dt, D, fderiv_of_notMem_tsupport ℝ hp]

private theorem continuous_D {f : Point → ℝ} (hf : ContDiff ℝ 1 f) (v : Point) :
    Continuous (D v f) := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- Both coefficients are integrable for a compact C¹ phase test. -/
theorem integrable_coefficients (m₁ m₂ : ℝ) {ρ S b : Point → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hS : ContDiff ℝ 2 S) (hb : ContDiff ℝ 1 b) (hc : HasCompactSupport b) :
    Integrable (linear m₁ m₂ ρ S b) ∧ Integrable (quadratic m₁ m₂ ρ b) := by
  have hl : Continuous (linear m₁ m₂ ρ S b) :=
    (((continuous_D hb timeAxis).mul hρ.continuous).add
      (continuous_finsetSum _ fun j _ =>
        (continuous_D hb (axis j)).mul (contDiff_flux m₁ m₂ hρ hS j).continuous)).neg
  have hq : Continuous (quadratic m₁ m₂ ρ b) :=
    hρ.continuous.neg.mul (continuous_finsetSum _ fun j _ =>
      ((continuous_D hb (axis j)).pow 2).div_const _)
  have H := compact_coefficients m₁ m₂ ρ S hc
  exact ⟨hl.integrable_of_hasCompactSupport H.1, hq.integrable_of_hasCompactSupport H.2⟩

/-- Every affine phase perturbation produces an integrable relative density. -/
theorem integrable_difference (h m₁ m₂ : ℝ) (V : Point → ℝ) {ρ S b : Point → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hS : ContDiff ℝ 2 S) (hb : ContDiff ℝ 1 b)
    (hc : HasCompactSupport b) (s : ℝ) :
    Integrable (fun p => densityL h m₁ m₂ V ρ (fun z => S z + s*b z) p -
      densityL h m₁ m₂ V ρ S p) := by
  have H := integrable_coefficients m₁ m₂ hρ hS hb hc
  simp_rw [fun p => density_expansion h m₁ m₂ V ρ (hS.differentiable (by norm_num) p)
    (hb.differentiable (by norm_num) p) s]
  exact (H.1.const_mul s).add (H.2.const_mul (s^2))

/-- An integrable classical background remains integrable for every affine phase perturbation. -/
theorem integrable_classical_perturbed (m₁ m₂ : ℝ) (V : Point → ℝ) {ρ S b : Point → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hS : ContDiff ℝ 2 S) (hb : ContDiff ℝ 1 b)
    (hc : HasCompactSupport b) (hbase : Integrable (classicalDensity m₁ m₂ V ρ S)) (s : ℝ) :
    Integrable (classicalDensity m₁ m₂ V ρ (fun z => S z + s*b z)) := by
  apply (hbase.sub (integrable_difference 0 m₁ m₂ V hρ hS hb hc s)).congr
  filter_upwards with p
  simp only [Pi.sub_apply, classicalDensity, densityL]
  ring

/-- Exact relative action polynomial, valid for every real parameter. -/
theorem relative_polynomial (h m₁ m₂ : ℝ) (V : Point → ℝ) {ρ S b : Point → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hS : ContDiff ℝ 2 S) (hb : ContDiff ℝ 1 b)
    (hc : HasCompactSupport b) (s : ℝ) :
    relative (densityL h m₁ m₂ V ρ S) (densityL h m₁ m₂ V ρ (fun z => S z + s*b z)) =
      s * (∫ p, linear m₁ m₂ ρ S b p) + s^2 * (∫ p, quadratic m₁ m₂ ρ b p) := by
  have H := integrable_coefficients m₁ m₂ hρ hS hb hc
  unfold relative
  simp_rw [fun p => density_expansion h m₁ m₂ V ρ (hS.differentiable (by norm_num) p)
    (hb.differentiable (by norm_num) p) s]
  rw [integral_add (H.1.const_mul s) (H.2.const_mul (s^2)), integral_const_mul, integral_const_mul]

/-- The tested continuity residual is integrable, including its time component. -/
theorem integrable_test_continuity (m₁ m₂ : ℝ) {ρ S b : Point → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hS : ContDiff ℝ 2 S) (hb : Continuous b)
    (hc : HasCompactSupport b) : Integrable (fun p => b p * continuity m₁ m₂ ρ S p) := by
  have H : Continuous (continuity m₁ m₂ ρ S) :=
    (continuous_D hρ timeAxis).add (continuous_finsetSum _ fun j _ =>
      continuous_D (contDiff_flux m₁ m₂ hρ hS j) (axis j))
  exact (hb.mul H).integrable_of_hasCompactSupport hc.mul_right

/-- The first variation in the phase is the compact test paired with the continuity residual. -/
theorem hasDerivAt_relative (h m₁ m₂ : ℝ) (V : Point → ℝ) {ρ S b : Point → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hS : ContDiff ℝ 2 S) (hb : ContDiff ℝ 1 b)
    (hc : HasCompactSupport b) :
    HasDerivAt (fun s => relative (densityL h m₁ m₂ V ρ S)
      (densityL h m₁ m₂ V ρ (fun z => S z + s*b z))) (∫ p, b p * continuity m₁ m₂ ρ S p) 0 := by
  simp_rw [relative_polynomial h m₁ m₂ V hρ hS hb hc]
  have H := ((hasDerivAt_id (0 : ℝ)).mul_const (∫ p, linear m₁ m₂ ρ S b p)).fun_add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (∫ p, quadratic m₁ m₂ ρ b p))
  have heq : (∫ p, b p * continuity m₁ m₂ ρ S p) = ∫ p, linear m₁ m₂ ρ S b p := by
    rw [continuity_test m₁ m₂ hρ hS hb hc]
    simp only [linear, integral_neg]
  rw [heq]
  simpa using H

end FoliationQM.TwoBodyPhaseVariation
