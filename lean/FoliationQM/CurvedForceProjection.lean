module

public import FoliationQM.CurvedCoordinateDynamics
public import FoliationQM.CurvedLogGradientProjection

/-!
# Cancellation in the actual coordinate-time force projection

The projection obtained by differentiating coordinate-time velocity is
linear in proper acceleration and removes its velocity-parallel part.
Applying this fact to the actual projected logarithmic gradient leaves
the full inverse-metric contraction, including its temporal and
off-diagonal entries, with the exact coordinate-time normalization.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedForceProjection

open LorentzMatrixGroup CurvedCoordinateDynamics CurvedScalarGradient
  CurvedLogGradientProjection
open scoped Topology Matrix.Norms.Operator

/-- The actual coordinate-time force projection is additive in its acceleration argument. -/
theorem add (c : ℝ) (u a b : Covector) :
    forceProjection c u (a + b) = forceProjection c u a + forceProjection c u b := by
  ext r
  simp only [forceProjection, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Real scalar multiplication commutes with the actual coordinate-time force projection. -/
theorem smul (c : ℝ) (u : Covector) (k : ℝ) (a : Covector) :
    forceProjection c u (k • a) = k • forceProjection c u a := by
  ext r
  simp only [forceProjection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A velocity-parallel contribution cancels from the actual force projection at a regular temporal velocity. -/
theorem sub_parallel (c : ℝ) (u v : Covector) (k : ℝ) (h0 : u 0 ≠ 0) :
    forceProjection c u (v - k • u) = forceProjection c u v := by
  ext r
  simp only [forceProjection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [h0]
  ring

/-- Removing a parallel term from a scaled acceleration gives the exact fourth-power coordinate-time coefficient. -/
theorem scaled_sub_parallel (c : ℝ) (u v : Covector) (k s : ℝ) (h0 : u 0 ≠ 0) :
    forceProjection c u ((c ^ 2 / (2 * s)) • (v - k • u)) =
      (c ^ 4 / (2 * (u 0) ^ 2 * s)) • (v - (v 0 / u 0) • u) := by
  rw [smul, sub_parallel c u v k h0, forceProjection, smul_smul]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Subtracting the temporal velocity component from a matrix-raised covector retains the sum over all four coordinate indices. -/
theorem mulVec_sub_components (u : Covector) (A : Mat4) (ξ : Covector) (r : Fin 4) :
    (A.mulVec ξ - (A.mulVec ξ 0 / u 0) • u) r =
      ∑ b, (A r b - u r / u 0 * A 0 b) * ξ b := by
  change (∑ b, A r b * ξ b) - ((∑ b, A 0 b * ξ b) / u 0) * u r = _
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Each projected matrix-raised covector has the complete inverse-metric-minus-temporal-row contraction, without dropping any coordinate term. -/
theorem matrix_components (c : ℝ) (u : Covector) (A : Mat4) (ξ : Covector)
    (r : Fin 4) :
    forceProjection c u (A.mulVec ξ) r =
      c ^ 2 / (u 0) ^ 2 * ∑ b, (A r b - u r / u 0 * A 0 b) * ξ b := by
  change c ^ 2 / (u 0) ^ 2 * (A.mulVec ξ - (A.mulVec ξ 0 / u 0) • u) r = _
  rw [mulVec_sub_components]

variable {q : Covector → ℝ} {x : Covector}

/-- The actual logarithmic projected gradient yields the exact coordinate force after cancellation of its velocity-parallel term. -/
theorem forceProjection_projected_log (c : ℝ) (g : Covector → Mat4)
    (U : Covector → Covector) (hq : DifferentiableAt ℝ q x)
    (hp : 0 < 1 + q x) (h0 : U x 0 ≠ 0) :
    forceProjection c (U x)
      ((c ^ 2 / 2) • projectedGradient c g U (fun y => Real.log (1 + q y)) x) =
      (c ^ 4 / (2 * (U x 0) ^ 2 * (1 + q x))) •
        (grad g q x - (grad g q x 0 / U x 0) • U x) := by
  rw [projected_log_eq c g U hq hp, smul_smul]
  have hc : c ^ 2 / 2 * (1 + q x)⁻¹ = c ^ 2 / (2 * (1 + q x)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hc, projectedGradient]
  exact scaled_sub_parallel c (U x) (grad g q x)
    (fderiv ℝ q x (U x) / c ^ 2) (1 + q x) h0

end FoliationQM.CurvedForceProjection
