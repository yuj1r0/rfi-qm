module
public import FoliationQM.LorentzCayleySmooth
public import FoliationQM.LorentzCayleyDomain
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The actual inverse Cayley derivative at the Lorentz identity

Source scope: the independent Lorentz-coordinate differential needed for
v13 `prop:takabayasi`. The actual rational inverse Cayley map has derivative
one half of the identity on real matrix space. The denominator is proved
invertible at the identity, and the product rule removes its derivative
term because the numerator vanishes there. This is an actual Frechet
derivative, with no assumed coordinate Jacobian or Spin identification.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator RightActions
namespace FoliationQM.LorentzCayleyDifferential
open LorentzMatrixGroup LorentzCayleyAlgebra

/-- The inverse of twice the identity matrix is exactly half the identity. -/
theorem inverse_twice_one : ((1 : Mat4) + 1)⁻¹ = (1/2 : ℝ) • (1 : Mat4) := by
  apply Matrix.inv_eq_right_inv
  have he : (1 : Mat4) + 1 = (2 : ℝ) • (1 : Mat4) := by simp [two_smul]
  rw [he]
  simp [smul_smul]

/-- The actual inverse Cayley map has real Frechet derivative one half of the identity at the identity matrix. -/
theorem hasFDerivAt_inverseCayley_one :
    HasFDerivAt inverseCayley ((1/2 : ℝ) • ContinuousLinearMap.id ℝ Mat4) (1 : Mat4) := by
  have hu : IsUnit ((1 : Mat4) + 1) :=
    (LorentzCayleyDomain.mem_source_iff 1).mp LorentzCayleyDomain.one_mem_source
  have hi : DifferentiableAt ℝ (fun M : Mat4 => (M + 1)⁻¹) 1 :=
    ((LorentzCayleySmooth.contDiffAt_inverse 1 hu).comp (f := fun M : Mat4 => M + 1) 1
      (contDiffAt_id.add contDiffAt_const)).differentiableAt_one
  have h := ((hasFDerivAt_id (𝕜 := ℝ) (1 : Mat4)).sub_const 1).mul' hi.hasFDerivAt
  convert! h using 1
  ext V i j
  simp [inverse_twice_one]

/-- Applied to any actual matrix direction, the inverse Cayley derivative is exactly one half of that direction. -/
theorem fderiv_inverseCayley_one_apply (V : Mat4) :
    fderiv ℝ inverseCayley (1 : Mat4) V = (1/2 : ℝ) • V := by
  rw [hasFDerivAt_inverseCayley_one.fderiv]
  rfl

end FoliationQM.LorentzCayleyDifferential
