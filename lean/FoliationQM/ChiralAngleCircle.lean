module
public import FoliationQM.ChiralSpinorMatrix
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
/-!
# The actual four-pi chiral angle circle

Source: v13 `prop:takabayasi` and `eq:takabayasi_polar` and the startup
four-pi convention. The full chiral angle is the actual quotient by four
pi. Its homeomorphism to the unit circle evaluates to the half-angle phase.
A two-pi shift is a nontrivial antipodal operation, and the actual chiral
matrix and polar spinor descend to this quotient. This does not construct
smooth spin bundles or classify the abstract spin group.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ChiralAngleCircle
/-- The source full chiral angle modulo four pi. -/
abbrev Angle := AddCircle (4 * Real.pi)
/-- The actual homeomorphism from the four-pi angle quotient to its half-angle unit phase. -/
def phaseEquiv : Angle ≃ₜ Circle := AddCircle.homeomorphCircle (by positivity)
/-- The quotient phase is the unit-circle exponential of half the full real angle. -/
theorem phaseEquiv_coe (beta : ℝ) : phaseEquiv (beta : Angle) = Circle.exp (beta / 2) := by
  rw [phaseEquiv, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  congr 1
  field_simp
  ring
/-- The complex value of the quotient phase is exactly the source half-angle exponential. -/
theorem phaseEquiv_coe_complex (beta : ℝ) : ((phaseEquiv (beta : Angle)) : ℂ) =
    Complex.exp (Complex.I * (beta : ℂ) / 2) := by
  rw [phaseEquiv_coe, Circle.coe_exp]
  congr 1
  push_cast
  ring
/-- A two-pi full-angle shift is the antipodal map on the half-angle unit phase. -/
theorem phaseEquiv_shift (q : Angle) : phaseEquiv (q + ((2*Real.pi:ℝ) : Angle)) = -phaseEquiv q := by
  simp only [phaseEquiv, AddCircle.homeomorphCircle_apply]
  rw [AddCircle.toCircle_add, AddCircle.toCircle_apply_mk]
  have h : 2*Real.pi/(4*Real.pi)*(2*Real.pi)=Real.pi := by field_simp; ring
  rw [h]
  apply Subtype.ext
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]
/-- Two pi is a nonzero point on the full chiral angle circle. -/
theorem two_pi_ne_zero : ((2*Real.pi:ℝ) : Angle) ≠ 0 := by
  intro h
  have hq := congrArg phaseEquiv h
  have hh : phaseEquiv ((2*Real.pi:ℝ) : Angle)= -1 := by
    rw [phaseEquiv, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    have he : 2*Real.pi/(4*Real.pi)*(2*Real.pi)=Real.pi := by field_simp; ring
    rw [he]
    apply Subtype.ext
    simp [Circle.coe_exp, Complex.exp_pi_mul_I]
  rw [hh] at hq
  have hz : phaseEquiv (0:Angle)=1 := by simp [phaseEquiv, AddCircle.homeomorphCircle_apply]
  rw [hz] at hq
  have he := congrArg (fun z : Circle => (z:ℂ)) hq
  norm_num at he
/-- Four pi is exactly zero in the source full-angle quotient. -/
theorem four_pi_eq_zero : ((4 * Real.pi : ℝ) : Angle) = 0 := AddCircle.coe_period _

/-- The actual chiral Dirac matrix descends to the four-pi angle quotient. -/
def chiralOnAngle : Angle → DiracMatrices.Mat := ChiralMatrix.chiral_periodic.lift

/-- The quotient chiral matrix agrees with the actual matrix on every real representative. -/
theorem chiralOnAngle_coe (beta : ℝ) : chiralOnAngle (beta : Angle) = ChiralMatrix.chiral beta := rfl

/-- The actual quotient chiral action corresponds to its half-angle unit phase in the spinor encoding. -/
theorem toMatrix_chiralOnAngle (q : Angle) (psi : DiracMatrices.Spinor) :
    SpinorMatrix.toMatrix ((chiralOnAngle q).mulVec psi) =
      (phaseEquiv q : ℂ) • SpinorMatrix.toMatrix psi := by
  induction q using QuotientAddGroup.induction_on
  rw [chiralOnAngle_coe, phaseEquiv_coe_complex, ChiralSpinorMatrix.toMatrix_chiral]

/-- The actual polar spinor descends to the source four-pi full-angle quotient. -/
def polarOnAngle (rho : ℝ) (q : Angle) (L : DiracMatrices.Mat) : DiracMatrices.Spinor :=
  (PolarSpinorBilinears.polarSpinor_periodic rho L).lift q

/-- The quotient polar spinor is the actual source expression on every real angle representative. -/
theorem polarOnAngle_coe (rho beta : ℝ) (L : DiracMatrices.Mat) :
    polarOnAngle rho (beta : Angle) L = PolarSpinorBilinears.polarSpinor rho beta L := rfl

/-- The actual quotient polar map has precisely the stipulated simultaneous two-pi/matrix-sign invariance. -/
theorem polarOnAngle_shift_neg (rho : ℝ) (q : Angle) (L : DiracMatrices.Mat) :
    polarOnAngle rho (q + ((2 * Real.pi : ℝ) : Angle)) (-L) = polarOnAngle rho q L := by
  induction q using QuotientAddGroup.induction_on
  rw [← AddCircle.coe_add, polarOnAngle_coe, polarOnAngle_coe,
    PolarSpinorBilinears.polarSpinor_shift_neg]

end FoliationQM.ChiralAngleCircle
