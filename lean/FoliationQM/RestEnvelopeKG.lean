module

public import FoliationQM.RestEnvelopeDifferential
public import FoliationQM.LaboratoryKG

/-!
# Exact rest-mass cancellation for the original Klein–Gordon field

Source: v13 `cor:schrodinger`, component kinds C and D. Physical coordinate
zero is time t. The actual rest-removed envelope is defined from the original
normal-coordinate field, and restoring its carrier is a function identity.
The finite-c remainder is retained with its positive sign on the right of
the homogeneous equation. This module makes no limit or smallness claim.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.RestEnvelopeKG

open RestEnvelopeDifferential LaboratoryCoordinates LaboratoryKG PolarSecondDifferential
open Madelung (coordinateVector)
open scoped ContDiff

/-- The free Schrödinger residual in physical time, using only the mass and action scales. -/
def schrodingerResidual (p : MassiveParameters) (u : Covector → ℂ) (x : Covector) : ℂ :=
  Complex.I * (p.hbar : ℂ) * directionalDerivative u (coordinateVector 0) x +
    ((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ) * spatialLaplacian u x

/-- The actual rest-removed envelope of the original normal-coordinate field, including its nodes. -/
def envelope (p : MassiveParameters) (ψ : Covector → ℂ) (x : Covector) : ℂ :=
  (carrierField p x)⁻¹ * pullback p.c ψ x

/-- The spatial Laplacian of the dressed field retains the same spatial derivatives of its envelope. -/
theorem spatialLaplacian_dressedField (p : MassiveParameters) {u : Covector → ℂ}
    {x : Covector} (hu : ContDiffAt ℝ 2 u x) :
    spatialLaplacian (dressedField p u) x = carrierField p x * spatialLaplacian u x := by
  unfold spatialLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [coordinateVector] using
    secondDirectionalDerivative_dressedField p hu (coordinateVector i.succ)

/-- Actual time and spatial derivatives cancel the rest mass exactly in the dimensional KG operator. -/
theorem laboratoryKG_dressedField (p : MassiveParameters) {u : Covector → ℂ}
    {x : Covector} (hu : ContDiffAt ℝ 2 u x) :
    laboratoryKG p (dressedField p u) x = carrierField p x *
      (((p.hbar ^ 2 / p.c ^ 2 : ℝ) : ℂ) *
        secondDirectionalDerivative u (coordinateVector 0) x -
        (2 * (p.m : ℂ)) * schrodingerResidual p u x) := by
  have ht : secondDirectionalDerivative (dressedField p u) (coordinateVector 0) x =
      carrierField p x * (secondDirectionalDerivative u (coordinateVector 0) x -
        2 * Complex.I * (p.omega0 : ℂ) * directionalDerivative u (coordinateVector 0) x -
        (p.omega0 : ℂ) ^ 2 * u x) := by
    simpa [coordinateVector] using
      secondDirectionalDerivative_dressedField p hu (coordinateVector 0)
  have hc : (p.c : ℂ) ≠ 0 := by exact_mod_cast p.c_pos.ne'
  have hm : (p.m : ℂ) ≠ 0 := by exact_mod_cast p.m_pos.ne'
  have hh : (p.hbar : ℂ) ≠ 0 := by exact_mod_cast p.hbar_pos.ne'
  rw [laboratoryKG, laboratoryBox, ht, spatialLaplacian_dressedField p hu]
  simp only [dressedField, schrodingerResidual, Complex.real_smul, MassiveParameters.omega0]
  push_cast
  field_simp
  ring

/-- Rearranging the exact dimensional identity retains both the true second-time remainder
and the signed dressed KG residual. -/
theorem exact_remainder (p : MassiveParameters) {u : Covector → ℂ} {x : Covector}
    (hu : ContDiffAt ℝ 2 u x) :
    schrodingerResidual p u x =
      ((p.hbar ^ 2 / (2 * p.m * p.c ^ 2) : ℝ) : ℂ) *
        secondDirectionalDerivative u (coordinateVector 0) x -
      ((1 / (2 * p.m) : ℝ) : ℂ) * (carrierField p x)⁻¹ *
        laboratoryKG p (dressedField p u) x := by
  rw [laboratoryKG_dressedField p hu]
  have hc : (p.c : ℂ) ≠ 0 := by exact_mod_cast p.c_pos.ne'
  have hm : (p.m : ℂ) ≠ 0 := by exact_mod_cast p.m_pos.ne'
  have he := carrierField_ne_zero p x
  push_cast
  field_simp
  ring

/-- Local C² regularity of the original field gives local C² regularity of its actual rest-removed envelope. -/
theorem contDiffAt_envelope (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ (toNormal p.c x)) :
    ContDiffAt ℝ 2 (envelope p ψ) x :=
  (((contDiff_carrierField p).of_le (by simp)).contDiffAt.inv
    (carrierField_ne_zero p x)).mul (contDiffAt_pullback hψ)

/-- Restoring the envelope's carrier reconstructs the same original laboratory pullback as a function. -/
theorem dressedField_envelope (p : MassiveParameters) (ψ : Covector → ℂ) :
    dressedField p (envelope p ψ) = pullback p.c ψ := by
  funext x
  change carrierField p x * ((carrierField p x)⁻¹ * pullback p.c ψ x) = _
  rw [← mul_assoc, mul_inv_cancel₀ (carrierField_ne_zero p x), one_mul]

/-- The actual envelope remainder is expressed against the original normal-coordinate KG residual,
with all derivative and regularity data derived from that same field. -/
theorem source_remainder (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ (toNormal p.c x)) :
    schrodingerResidual p (envelope p ψ) x =
      ((p.hbar ^ 2 / (2 * p.m * p.c ^ 2) : ℝ) : ℂ) *
        secondDirectionalDerivative (envelope p ψ) (coordinateVector 0) x -
      ((1 / (2 * p.m) : ℝ) : ℂ) * (carrierField p x)⁻¹ *
        FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x) := by
  have h := exact_remainder p (contDiffAt_envelope p hψ)
  rw [dressedField_envelope, laboratoryKG_pullback p hψ] at h
  exact h

/-- The original KG equation is equivalent to the exact positive-sign second-time remainder equation
for its actual envelope, without deleting the finite-c remainder. -/
theorem source_KG_iff (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ (toNormal p.c x)) :
    FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x) = 0 ↔
      schrodingerResidual p (envelope p ψ) x =
        ((p.hbar ^ 2 / (2 * p.m * p.c ^ 2) : ℝ) : ℂ) *
          secondDirectionalDerivative (envelope p ψ) (coordinateVector 0) x := by
  rw [source_remainder p hψ, sub_eq_self]
  have hm : (((1 / (2 * p.m) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast one_div_ne_zero (mul_ne_zero (by norm_num) p.m_pos.ne')
  exact (mul_eq_zero_iff_left
    (mul_ne_zero hm (inv_ne_zero (carrierField_ne_zero p x)))).symm

end FoliationQM.RestEnvelopeKG
