module

public import FoliationQM.LaboratoryCoordinates
public import FoliationQM.FlatIntegrationByParts

/-!
# The Klein–Gordon operator in actual physical coordinates

Source: v13 `cor:schrodinger`, component kinds C and D, and its preceding KG equation. Here coordinate
zero is physical time t. The spatial Laplacian is the explicit sum of three
actual Cartesian second derivatives. Pullback along (t,x) ↦ (ct,x) identifies
this dimensional operator with the existing normal-coordinate KG operator.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.LaboratoryKG

open LaboratoryCoordinates PolarSecondDifferential
open Madelung (coordinateVector)

/-- The actual Cartesian spatial Laplacian, with physical time held fixed. -/
def spatialLaplacian (f : Covector → ℂ) (x : Covector) : ℂ :=
  ∑ i : Fin 3, secondDirectionalDerivative f (coordinateVector i.succ) x

/-- The actual physical-time wave operator c⁻²∂t²−Δ on complex spacetime fields. -/
def laboratoryBox (c : ℝ) (f : Covector → ℂ) (x : Covector) : ℂ :=
  (c ^ 2)⁻¹ • secondDirectionalDerivative f (coordinateVector 0) x -
    spatialLaplacian f x

/-- The dimensional physical-time Klein–Gordon operator with the source mass and action scales. -/
def laboratoryKG (p : MassiveParameters) (f : Covector → ℂ) (x : Covector) : ℂ :=
  (p.hbar : ℂ) ^ 2 * laboratoryBox p.c f x +
    (p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2 * f x

/-- Actual spatial second derivatives of the pullback give the original Cartesian Laplacian. -/
theorem spatialLaplacian_pullback {c : ℝ} {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ (toNormal c x)) :
    spatialLaplacian (pullback c ψ) x = spatialLaplacian ψ (toNormal c x) := by
  unfold spatialLaplacian
  exact Finset.sum_congr rfl fun i _ => spatial_second hψ i

/-- Physical c⁻² cancels the genuine c² second-time pullback factor when c is nonzero. -/
theorem laboratoryBox_pullback {c : ℝ} (hc : c ≠ 0) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ (toNormal c x)) :
    laboratoryBox c (pullback c ψ) x = box ψ coordinateVector (toNormal c x) := by
  unfold laboratoryBox
  rw [time_second hψ, spatialLaplacian_pullback hψ, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 hc), one_smul]
  simp only [spatialLaplacian, Fin.sum_univ_three, box]
  abel

/-- The physical-time dimensional KG residual is the original normal-coordinate residual
of the same field at the actual ct image point. -/
theorem laboratoryKG_pullback (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ (toNormal p.c x)) :
    laboratoryKG p (pullback p.c ψ) x =
      FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x) := by
  rw [laboratoryKG, laboratoryBox_pullback p.c_pos.ne' hψ]
  rfl

end FoliationQM.LaboratoryKG
