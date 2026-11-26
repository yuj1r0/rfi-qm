module

public import FoliationQM.CurvedAuxiliaryNorm

/-!
# A uniform Euclidean bound for the full coordinate force

The estimate retains the temporal covector derivative and every matrix
entry. A uniform temporal-velocity lower bound, a positive normalization
lower bound, bounded spatial velocity ratios, and a bound on the actual
raising operator give one explicit coefficient. No metric-signature
assumption replaces the operator bound.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedUniformForceBound

open LorentzMatrixGroup CurvedCoordinateDynamics CurvedAuxiliaryNorm
open scoped Matrix.Norms.Operator

/-- Bounded spatial velocity ratios control the temporal-row subtraction in the coordinate supremum norm. -/
theorem spatial_projection_le (u v : Covector) {Bv : ℝ} (hBv : 0 ≤ Bv)
    (hratio : ∀ i : Fin 3, |u i.succ / u 0| ≤ Bv) :
    ‖spatialPart (v - (v 0 / u 0) • u)‖ ≤ (1 + Bv) * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) (norm_nonneg v))).mpr
  intro i
  change ‖v i.succ - (v 0 / u 0) * u i.succ‖ ≤ _
  have he : (v 0 / u 0) * u i.succ = (u i.succ / u 0) * v 0 := by ring
  rw [he]
  calc
    ‖v i.succ - (u i.succ / u 0) * v 0‖ ≤
        ‖v i.succ‖ + ‖(u i.succ / u 0) * v 0‖ := norm_sub_le _ _
    _ = ‖v i.succ‖ + ‖u i.succ / u 0‖ * ‖v 0‖ := by rw [norm_mul]
    _ ≤ ‖v‖ + Bv * ‖v‖ := add_le_add (norm_le_pi_norm v i.succ)
      (mul_le_mul (by simpa only [Real.norm_eq_abs] using hratio i)
        (norm_le_pi_norm v 0) (norm_nonneg _) hBv)
    _ = (1 + Bv) * ‖v‖ := by ring

/-- Positive uniform lower bounds on temporal velocity and normalization bound the exact coordinate-force coefficient. -/
theorem coefficient_le (c : ℝ) (u : Covector) {umin δ s : ℝ}
    (hmin : 0 < umin) (humin : umin ≤ |u 0|) (hδ : 0 < δ) (hs : δ ≤ s) :
    c ^ 4 / (2 * (u 0) ^ 2 * s) ≤ c ^ 4 / (2 * umin ^ 2 * δ) := by
  have hsq : umin ^ 2 ≤ (u 0) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hmin.le (abs_nonneg (u 0))).mpr humin
  have hd : 0 < 2 * umin ^ 2 * δ := by positivity
  have hden : 2 * umin ^ 2 * δ ≤ 2 * (u 0) ^ 2 * s := by
    calc
      2 * umin ^ 2 * δ ≤ 2 * (u 0) ^ 2 * δ := by gcongr
      _ ≤ 2 * (u 0) ^ 2 * s := by gcongr
  exact div_le_div_of_nonneg_left (by positivity) hd hden

/-- The actual spatial force expression is bounded in Euclidean norm by the complete four-component covector norm with one explicit uniform constant. -/
theorem spatial_force_bound (c : ℝ) (u : Covector) (A : Mat4) (ξ : Covector)
    {umin δ s Bv Bg : ℝ} (hmin : 0 < umin) (humin : umin ≤ |u 0|)
    (hδ : 0 < δ) (hs : δ ≤ s) (hBv : 0 ≤ Bv) (hBg : 0 ≤ Bg)
    (hratio : ∀ i : Fin 3, |u i.succ / u 0| ≤ Bv) (hA : ‖raiseMap A‖ ≤ Bg) :
    norm2 (spatialPart ((c ^ 4 / (2 * (u 0) ^ 2 * s)) •
      (A.mulVec ξ - (A.mulVec ξ 0 / u 0) • u))) ≤
      (3 * c ^ 4 * (1 + Bv) * Bg / (2 * umin ^ 2 * δ)) * norm2 ξ := by
  have hspos : 0 < s := lt_of_lt_of_le hδ hs
  have hc : 0 ≤ c ^ 4 / (2 * (u 0) ^ 2 * s) := by positivity
  have hproj : norm2 (spatialPart (A.mulVec ξ - (A.mulVec ξ 0 / u 0) • u)) ≤
      3 * (1 + Bv) * Bg * norm2 ξ := by
    calc
      _ ≤ 3 * ‖spatialPart (A.mulVec ξ - (A.mulVec ξ 0 / u 0) • u)‖ :=
        spatial_norm2_le _
      _ ≤ 3 * ((1 + Bv) * ‖A.mulVec ξ‖) := by
        gcongr
        exact spatial_projection_le u (A.mulVec ξ) hBv hratio
      _ ≤ 3 * ((1 + Bv) * (Bg * norm2 ξ)) := by
        gcongr
        exact norm_mulVec_le hA ξ
      _ = 3 * (1 + Bv) * Bg * norm2 ξ := by ring
  rw [map_smul, norm2_smul, abs_of_nonneg hc]
  calc
    _ ≤ (c ^ 4 / (2 * (u 0) ^ 2 * s)) * (3 * (1 + Bv) * Bg * norm2 ξ) :=
      mul_le_mul_of_nonneg_left hproj hc
    _ ≤ (c ^ 4 / (2 * umin ^ 2 * δ)) * (3 * (1 + Bv) * Bg * norm2 ξ) :=
      mul_le_mul_of_nonneg_right (coefficient_le c u hmin humin hδ hs)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hBg)
          (norm2_nonneg ξ))
    _ = _ := by ring

end FoliationQM.CurvedUniformForceBound
