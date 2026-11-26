module

public import FoliationQM.RadialGeometry
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# The actual angular quotient of the positive-coupling cone family

Sources: v13 `eq:cone_angle`, `eq:lambda_metric`, and `lem:uniqueness`.
The source angular coordinate identifies the physical circle of period `2 * π`
homeomorphically with the angular circle of period `π * hbar / sqrt coupling`.
The same real lift occurs in the already proved actual local metric pullback.
This identifies the total angular period; it does not construct a metric
completion, assert that the cone tip is smooth, or globally develop the cone
into the ordinary Euclidean plane.
-/
@[expose] public section

namespace FoliationQM.ConeAngleQuotient

open MasterMetricAndCone RadialGeometry

/-- The angular circle in the source cone family has positive period. -/
theorem coneAngle_pos (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling) :
    0 < coneAngle hbar coupling := by
  exact div_pos (mul_pos Real.pi_pos hh) (Real.sqrt_pos.mpr hc)

/-- The source angular change preserves the positive orientation. -/
theorem angularScale_pos (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling) :
    0 < hbar / (2 * Real.sqrt coupling) := by
  exact div_pos hh (mul_pos (by norm_num) (Real.sqrt_pos.mpr hc))

/-- Advancing one physical clock period advances the actual real angular lift
by exactly the source cone angle. -/
theorem angularCoordinate_add_period (hbar coupling Φ : ℝ) :
    angularCoordinate hbar coupling (Φ + 2 * Real.pi) =
      angularCoordinate hbar coupling Φ + coneAngle hbar coupling := by
  unfold angularCoordinate
  rw [mul_add, angular_period]

/-- The actual quotient homeomorphism induced by the source angular change. -/
noncomputable def angularCircleEquiv (hbar coupling : ℝ)
    (hh : 0 < hbar) (hc : 0 < coupling) :
    AddCircle (2 * Real.pi) ≃ₜ AddCircle (coneAngle hbar coupling) :=
  AddCircle.homeomorphAddCircle (2 * Real.pi) (coneAngle hbar coupling)
    (by positivity) (ne_of_gt (coneAngle_pos hbar coupling hh hc))

/-- On every real phase representative, the global quotient map is exactly
the angular coordinate used in the source local metric calculation. -/
theorem angularCircleEquiv_apply_coe (hbar coupling : ℝ)
    (hh : 0 < hbar) (hc : 0 < coupling) (Φ : ℝ) :
    angularCircleEquiv hbar coupling hh hc (Φ : AddCircle (2 * Real.pi)) =
      (angularCoordinate hbar coupling Φ : AddCircle (coneAngle hbar coupling)) := by
  rw [angularCircleEquiv, AddCircle.homeomorphAddCircle_apply_mk]
  congr 1
  unfold angularCoordinate coneAngle
  field_simp

/-- Equality of rescaled angular classes is exactly equality of physical
phase classes. The quotient map introduces no additional identifications. -/
theorem angularCoordinate_quotient_eq_iff (hbar coupling : ℝ)
    (hh : 0 < hbar) (hc : 0 < coupling) (Φ Ψ : ℝ) :
    (angularCoordinate hbar coupling Φ : AddCircle (coneAngle hbar coupling)) =
      (angularCoordinate hbar coupling Ψ : AddCircle (coneAngle hbar coupling)) ↔
        (Φ : AddCircle (2 * Real.pi)) = (Ψ : AddCircle (2 * Real.pi)) := by
  rw [← angularCircleEquiv_apply_coe hbar coupling hh hc Φ,
    ← angularCircleEquiv_apply_coe hbar coupling hh hc Ψ]
  exact (angularCircleEquiv hbar coupling hh hc).injective.eq_iff

/-- The real angular lift descends across the physical clock seam. -/
theorem angularCoordinate_periodic (hbar coupling : ℝ) :
    Function.Periodic
      (fun Φ : ℝ =>
        (angularCoordinate hbar coupling Φ : AddCircle (coneAngle hbar coupling)))
      (2 * Real.pi) := by
  intro Φ
  dsimp only
  rw [angularCoordinate_add_period, AddCircle.coe_add_period]

/-- One half-open physical period is carried to precisely one half-open
angular period, preserving its orientation and endpoints. -/
theorem angularCoordinate_mem_Ico_iff (hbar coupling : ℝ)
    (hh : 0 < hbar) (hc : 0 < coupling) (Φ : ℝ) :
    angularCoordinate hbar coupling Φ ∈ Set.Ico 0 (coneAngle hbar coupling) ↔
      Φ ∈ Set.Ico 0 (2 * Real.pi) := by
  have hs := angularScale_pos hbar coupling hh hc
  rw [← angular_period hbar coupling]
  change (0 ≤ hbar / (2 * Real.sqrt coupling) * Φ ∧
      hbar / (2 * Real.sqrt coupling) * Φ <
        hbar / (2 * Real.sqrt coupling) * (2 * Real.pi)) ↔
    (0 ≤ Φ ∧ Φ < 2 * Real.pi)
  rw [mul_nonneg_iff_of_pos_left hs, mul_lt_mul_iff_right₀ hs]

/-- Every period of the angular quotient lift is an integer multiple of the
physical clock period, so the displayed period is not merely an upper bound. -/
theorem angularCoordinate_periods_iff (hbar coupling : ℝ)
    (hh : 0 < hbar) (hc : 0 < coupling) (T : ℝ) :
    Function.Periodic
      (fun Φ : ℝ =>
        (angularCoordinate hbar coupling Φ : AddCircle (coneAngle hbar coupling))) T ↔
      ∃ n : ℤ, T = n * (2 * Real.pi) := by
  constructor
  · intro hT
    have hzero := hT 0
    rw [zero_add, angularCoordinate_quotient_eq_iff hbar coupling hh hc] at hzero
    rw [AddCircle.coe_zero, AddCircle.coe_eq_zero_iff] at hzero
    obtain ⟨n, hn⟩ := hzero
    exact ⟨n, by simpa only [zsmul_eq_mul] using hn.symm⟩
  · rintro ⟨n, rfl⟩
    simpa only [zsmul_eq_mul] using (angularCoordinate_periodic hbar coupling).zsmul n

/-- The globally identified angular quotient and the actual local Euclidean
development use the same real angular lift. Its radial/angular pullback is
the source metric on every positive-density tangent. No tip completion is
inferred from this local differential and global period statement. -/
theorem angularCircleEquiv_local_metric (hbar coupling ρ Φ dρ dΦ : ℝ)
    (hh : 0 < hbar) (hc : 0 < coupling) (hρ : 0 < ρ) :
    angularCircleEquiv hbar coupling hh hc (Φ : AddCircle (2 * Real.pi)) =
      (angularCoordinate hbar coupling Φ : AddCircle (coneAngle hbar coupling)) ∧
    Complex.normSq (fderiv ℝ
      (amplitudeField (fun z : ℝ × ℝ => radialCoordinate hbar coupling z.1)
        (fun z => angularCoordinate hbar coupling z.2)) (ρ, Φ) (dρ, dΦ)) =
      coupling / (hbar ^ 2 * ρ) * dρ ^ 2 + ρ * dΦ ^ 2 := by
  exact ⟨angularCircleEquiv_apply_coe hbar coupling hh hc Φ,
    fderiv_radialAngularMap_normSq hbar coupling ρ Φ dρ dΦ hh hc hρ⟩

end FoliationQM.ConeAngleQuotient
