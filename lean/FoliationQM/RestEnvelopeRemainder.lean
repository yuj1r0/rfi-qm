module

public import FoliationQM.RestEnvelopeKG

/-!
# Exact norms and bounds for the actual rest-envelope remainder

Source: v13 `cor:schrodinger`, component kinds C and D. The zeroth
coordinate is physical time. Every derivative and KG source below belongs
to the same actual field. The unit rest carrier preserves the source norm.
These finite-c estimates retain the second-time derivative; a family limit
requires a bound uniform in that family or a specified subquadratic bound.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.RestEnvelopeRemainder

open RestEnvelopeKG RestEnvelopeDifferential LaboratoryKG LaboratoryCoordinates
open PolarSecondDifferential
open Madelung (coordinateVector)
open scoped ContDiff

/-- The positive coefficient of the actual second-time remainder. -/
def temporalCoefficient (p : MassiveParameters) : ℝ := p.hbar ^ 2 / (2 * p.m * p.c ^ 2)

/-- The positive coefficient of the phase-neutralized dimensional KG source. -/
def sourceCoefficient (p : MassiveParameters) : ℝ := 1 / (2 * p.m)

/-- The actual dressed KG residual after removal of its unit rest carrier. -/
def neutralizedKG (p : MassiveParameters) (u : Covector → ℂ) (x : Covector) : ℂ :=
  (carrierField p x)⁻¹ * laboratoryKG p (dressedField p u) x

/-- Positive physical scales make the temporal coefficient strictly positive. -/
theorem temporalCoefficient_pos (p : MassiveParameters) : 0 < temporalCoefficient p :=
  div_pos (sq_pos_of_pos p.hbar_pos)
    (mul_pos (mul_pos (by norm_num) p.m_pos) (sq_pos_of_pos p.c_pos))

/-- The temporal coefficient preserves inequalities between real bounds. -/
theorem temporalCoefficient_nonneg (p : MassiveParameters) : 0 ≤ temporalCoefficient p :=
  (temporalCoefficient_pos p).le

/-- Positive mass makes the source coefficient strictly positive. -/
theorem sourceCoefficient_pos (p : MassiveParameters) : 0 < sourceCoefficient p :=
  div_pos zero_lt_one (mul_pos (by norm_num) p.m_pos)

/-- The source coefficient preserves inequalities between real bounds. -/
theorem sourceCoefficient_nonneg (p : MassiveParameters) : 0 ≤ sourceCoefficient p :=
  (sourceCoefficient_pos p).le

/-- The actual spacetime rest carrier has norm one at every point. -/
theorem norm_carrierField (p : MassiveParameters) (x : Covector) : ‖carrierField p x‖ = 1 :=
  RestPhaseDerivatives.norm_carrier p (x 0)

/-- Removing the carrier preserves the norm of the actual KG residual, even at wave nodes. -/
theorem norm_neutralizedKG (p : MassiveParameters) (u : Covector → ℂ) (x : Covector) :
    ‖neutralizedKG p u x‖ = ‖laboratoryKG p (dressedField p u) x‖ := by
  simp only [neutralizedKG, norm_mul, norm_inv, norm_carrierField, inv_one, one_mul]

/-- Adding back the signed source leaves exactly the actual second-time remainder. -/
theorem corrected_residual (p : MassiveParameters) {u : Covector → ℂ} {x : Covector}
    (hu : ContDiffAt ℝ 2 u x) :
    schrodingerResidual p u x + (sourceCoefficient p : ℂ) * neutralizedKG p u x =
      (temporalCoefficient p : ℂ) * secondDirectionalDerivative u (coordinateVector 0) x := by
  rw [exact_remainder p hu]
  simp only [temporalCoefficient, sourceCoefficient, neutralizedKG]
  ring

/-- The corrected residual norm equals its positive coefficient times the actual temporal derivative norm. -/
theorem norm_corrected_residual (p : MassiveParameters) {u : Covector → ℂ} {x : Covector}
    (hu : ContDiffAt ℝ 2 u x) :
    ‖schrodingerResidual p u x + (sourceCoefficient p : ℂ) * neutralizedKG p u x‖ =
      temporalCoefficient p * ‖secondDirectionalDerivative u (coordinateVector 0) x‖ := by
  rw [corrected_residual p hu, norm_mul,
    Complex.norm_of_nonneg (temporalCoefficient_nonneg p)]

/-- The actual inhomogeneous residual is bounded by the temporal remainder and the true KG source. -/
theorem norm_residual_le (p : MassiveParameters) {u : Covector → ℂ} {x : Covector}
    (hu : ContDiffAt ℝ 2 u x) :
    ‖schrodingerResidual p u x‖ ≤
      temporalCoefficient p * ‖secondDirectionalDerivative u (coordinateVector 0) x‖ +
      sourceCoefficient p * ‖laboratoryKG p (dressedField p u) x‖ := by
  have he := (eq_sub_iff_add_eq).mpr (corrected_residual p hu)
  rw [he]
  calc
    _ ≤ ‖(temporalCoefficient p : ℂ) * secondDirectionalDerivative u (coordinateVector 0) x‖ +
        ‖(sourceCoefficient p : ℂ) * neutralizedKG p u x‖ := norm_sub_le _ _
    _ = _ := by
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg (temporalCoefficient_nonneg p),
        Complex.norm_of_nonneg (sourceCoefficient_nonneg p), norm_neutralizedKG]

/-- An actual homogeneous KG field has precisely the positive-sign temporal remainder. -/
theorem residual_eq_temporal_of_KG (p : MassiveParameters) {u : Covector → ℂ} {x : Covector}
    (hu : ContDiffAt ℝ 2 u x) (hKG : laboratoryKG p (dressedField p u) x = 0) :
    schrodingerResidual p u x =
      (temporalCoefficient p : ℂ) * secondDirectionalDerivative u (coordinateVector 0) x := by
  simpa only [neutralizedKG, hKG, mul_zero, add_zero] using corrected_residual p hu

/-- The homogeneous KG residual norm is exactly the scaled second-time derivative norm. -/
theorem norm_residual_of_KG (p : MassiveParameters) {u : Covector → ℂ} {x : Covector}
    (hu : ContDiffAt ℝ 2 u x) (hKG : laboratoryKG p (dressedField p u) x = 0) :
    ‖schrodingerResidual p u x‖ =
      temporalCoefficient p * ‖secondDirectionalDerivative u (coordinateVector 0) x‖ := by
  rw [residual_eq_temporal_of_KG p hu hKG, norm_mul,
    Complex.norm_of_nonneg (temporalCoefficient_nonneg p)]

/-- A genuine bound on the second-time derivative gives a quantitative homogeneous residual bound. -/
theorem norm_residual_le_of_KG (p : MassiveParameters) {u : Covector → ℂ} {x : Covector} {M : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hbound : ‖secondDirectionalDerivative u (coordinateVector 0) x‖ ≤ M)
    (hKG : laboratoryKG p (dressedField p u) x = 0) :
    ‖schrodingerResidual p u x‖ ≤ temporalCoefficient p * M := by
  rw [norm_residual_of_KG p hu hKG]
  exact mul_le_mul_of_nonneg_left hbound (temporalCoefficient_nonneg p)

/-- The bound for an original normal-coordinate field keeps its actual KG residual at the mapped point. -/
theorem source_norm_residual_le (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ (toNormal p.c x)) :
    ‖schrodingerResidual p (envelope p ψ) x‖ ≤
      temporalCoefficient p * ‖secondDirectionalDerivative (envelope p ψ) (coordinateVector 0) x‖ +
      sourceCoefficient p * ‖FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x)‖ := by
  have h := norm_residual_le p (contDiffAt_envelope p hψ)
  rw [dressedField_envelope, laboratoryKG_pullback p hψ] at h
  exact h

/-- Original homogeneous KG gives the exact temporal norm identity for its same actual envelope. -/
theorem source_norm_residual_of_KG (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ (toNormal p.c x))
    (hKG : FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x) = 0) :
    ‖schrodingerResidual p (envelope p ψ) x‖ =
      temporalCoefficient p * ‖secondDirectionalDerivative (envelope p ψ) (coordinateVector 0) x‖ := by
  apply norm_residual_of_KG p (contDiffAt_envelope p hψ)
  rw [dressedField_envelope, laboratoryKG_pullback p hψ]
  exact hKG

/-- A common temporal-derivative bound on a physical region gives the same region-wide original-KG error bound. -/
theorem source_norm_residual_le_on (p : MassiveParameters) {ψ : Covector → ℂ}
    {K : Set Covector} {M : ℝ}
    (hψ : ∀ x ∈ K, ContDiffAt ℝ 2 ψ (toNormal p.c x))
    (hbound : ∀ x ∈ K, ‖secondDirectionalDerivative (envelope p ψ) (coordinateVector 0) x‖ ≤ M)
    (hKG : ∀ x ∈ K, FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x) = 0) :
    ∀ x ∈ K, ‖schrodingerResidual p (envelope p ψ) x‖ ≤ temporalCoefficient p * M := by
  intro x hx
  rw [source_norm_residual_of_KG p (hψ x hx) (hKG x hx)]
  exact mul_le_mul_of_nonneg_left (hbound x hx) (temporalCoefficient_nonneg p)

end FoliationQM.RestEnvelopeRemainder
