module

public import FoliationQM.CurvedAuxiliaryNorm
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive auxiliary-metric covector energy

Source: v13 `thm:wallstrom` Part (c) and `eq:weak_pde_cutoff_bound`, the positive
h-energy and its pointwise coordinate comparison, component kind A. The covector energy uses
the actual inverse of the positive metric, including all mixed entries.
The complex extension adds the real and imaginary covector energies.
Positive definiteness, not an assumed coercivity estimate, controls each
coordinate. Compact uniform estimates and integrability are later bridges.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.AuxiliaryMetricEnergy

open LorentzMatrixGroup Matrix
open scoped Matrix.Norms.Operator

/-- The actual inverse-metric quadratic energy of a real covector. -/
def realEnergy (H : Mat4) (a : Covector) : ℝ := a ⬝ᵥ H⁻¹ *ᵥ a

/-- The positive-metric energy of a complex covector is the sum of the energies of its real and imaginary parts. -/
def complexEnergy (H : Mat4) (z : Fin 4 → ℂ) : ℝ :=
  realEnergy H (fun i => (z i).re) + realEnergy H (fun i => (z i).im)

/-- The coordinate volume density of the auxiliary positive metric. -/
def density (H : Mat4) : ℝ := Real.sqrt H.det

/-- Positive definiteness of the metric makes the actual dual real energy nonnegative. -/
theorem realEnergy_nonneg {H : Mat4} (hH : H.PosDef) (a : Covector) :
    0 ≤ realEnergy H a := by
  simpa [realEnergy] using hH.inv.posSemidef.dotProduct_mulVec_nonneg a

/-- The actual complex dual energy is nonnegative for a positive metric. -/
theorem complexEnergy_nonneg {H : Mat4} (hH : H.PosDef) (z : Fin 4 → ℂ) :
    0 ≤ complexEnergy H z :=
  add_nonneg (realEnergy_nonneg hH _) (realEnergy_nonneg hH _)

/-- Each real coordinate is controlled by the corresponding original metric diagonal and the actual dual energy. -/
theorem coordinate_sq_le {H : Mat4} (hH : H.PosDef) (a : Covector) (i : Fin 4) :
    a i ^ 2 ≤ H i i * realEnergy H a := by
  have hcancel : H *ᵥ (H⁻¹ *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (H.isUnit_iff_isUnit_det.mp hH.isUnit), Matrix.one_mulVec]
  have hc := hH.star_dotProduct_mulVec_mul_le (Pi.single i 1) (H⁻¹ *ᵥ a)
  simpa [hcancel, realEnergy, dotProduct_comm, pow_two] using hc

/-- The same derived estimate controls the squared norm of each complex coordinate. -/
theorem complex_coordinate_sq_le {H : Mat4} (hH : H.PosDef)
    (z : Fin 4 → ℂ) (i : Fin 4) :
    ‖z i‖ ^ 2 ≤ H i i * complexEnergy H z := by
  have hr := coordinate_sq_le hH (fun j => (z j).re) i
  have hi := coordinate_sq_le hH (fun j => (z j).im) i
  rw [Complex.sq_norm, Complex.normSq_apply]
  dsimp only [complexEnergy]
  nlinarith

/-- The real/imaginary definition equals the full real Hermitian inverse-metric contraction. -/
theorem complexEnergy_eq_sum (H : Mat4) (z : Fin 4 → ℂ) :
    complexEnergy H z = ∑ i, ∑ j, H⁻¹ i j * (star (z i) * z j).re := by
  simp only [complexEnergy, realEnergy, dotProduct, Matrix.mulVec, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- A positive auxiliary metric has strictly positive coordinate volume density. -/
theorem density_pos {H : Mat4} (hH : H.PosDef) : 0 < density H :=
  Real.sqrt_pos.mpr hH.det_pos

/-- Squaring the actual positive volume density recovers the metric determinant. -/
theorem density_sq {H : Mat4} (hH : H.PosDef) : density H ^ 2 = H.det :=
  Real.sq_sqrt hH.det_pos.le

end FoliationQM.AuxiliaryMetricEnergy
