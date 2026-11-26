module

public import FoliationQM.MarginalDifferentiation

/-!
# Regular marginals for smooth independent densities

Products of positive C¹ probability densities on the two spatial slices
satisfy the actual marginal derivative-envelope hypotheses. This proves the
regularity assumptions are realized for a whole class of normalized laws.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ProductDensityRegularity

open MeasureTheory Filter Set LorentzCoordinates MarginalDifferentiation TwoParticleMarginals
open scoped Topology ContDiff

/-- Independent spatial density from two probability profiles. -/
def joint (p q : Spatial → ℝ) (z : Spatial × Spatial) : ℝ := p z.1 * q z.2

/-- Swapping the particle coordinates exchanges the profiles of a product density. -/
theorem swap_joint (p q : Spatial → ℝ) : swap (joint p q) = joint q p := by
  funext z
  exact mul_comm _ _

/-- A local bound for Dp times the integrable second profile dominates every
first partial derivative of the joint density on a neighborhood of x. -/
theorem dominatedAt_joint (p q : Spatial → ℝ) (hp : ContDiff ℝ 1 p) (hq : Integrable q) (x : Spatial) :
    DominatedAt (joint p q) x := by
  let C := ‖fderiv ℝ p x‖ + 1
  let s := {u | ‖fderiv ℝ p u‖ < C}
  have hc := (hp.continuous_fderiv (by norm_num)).norm.continuousAt (x := x)
  have hs : s ∈ 𝓝 x := hc.eventually_lt continuousAt_const (by dsimp [C]; linarith)
  refine ⟨s, hs, fun y => ‖q y‖ * C, hq.norm.mul_const _, .of_forall ?_⟩
  intro y u hu
  change ‖fderiv ℝ (fun a => p a * q y) u‖ ≤ ‖q y‖ * C
  rw [fderiv_mul_const (hp.differentiable (by norm_num) u), norm_smul]
  exact mul_le_mul_of_nonneg_left (le_of_lt hu) (norm_nonneg _)

/-- A product of positive normalized and integrable C¹ spatial profiles realizes
all hypotheses for the two marginal differentiation theorems. -/
theorem regular_joint (p q : Spatial → ℝ) (hpc : ContDiff ℝ 1 p) (hqc : ContDiff ℝ 1 q)
    (hp : ∀ x, 0 < p x) (hq : ∀ y, 0 < q y) (hpi : Integrable p) (hqi : Integrable q)
    (hpm : (∫ x, p x) = 1) (hqm : (∫ y, q y) = 1) : Regular (joint p q) where
  smooth := (hpc.comp contDiff_fst).mul (hqc.comp contDiff_snd)
  pos z := mul_pos (hp _) (hq _)
  integrable := hpi.mul_prod hqi
  mass_one := (integral_prod_mul p q).trans (by rw [hpm, hqm, one_mul])
  left_fiber x := hqi.const_mul (p x)
  right_fiber y := hpi.mul_const (q y)
  left_dom := dominatedAt_joint p q hpc hqi
  right_dom := by rw [swap_joint]; exact dominatedAt_joint q p hqc hpi

end FoliationQM.ProductDensityRegularity
