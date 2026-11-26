module
public import FoliationQM.TwistedScalarJet
public import FoliationQM.ScalarSectorDensity
public import FoliationQM.ChiralDifferential

/-!
# Spacetime derivatives of a chirally rotated scalar field

For v13 `thm:dirac_lift` and `eq:spinor_quadratic_exact`, the field is
obtained by acting with the chiral matrix on a complex scalar times the
rest spinor. Differentiation gives both the scalar derivative and the
phase derivative with its factor of one half. A positive density and a
real scalar action phase give explicit polar factors on a neighborhood.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.TwistedScalarField
open DiracMatrices ChiralMatrix ChiralDifferential MatrixDifferential ScalarRestKinetic
open SpinorRegularity ScalarPlanePhase PolarSpinorBilinears

/-- The pointwise chiral action on the complex scalar rest-spinor field. -/
def field (β : Covector → ℝ) (z : Covector → ℂ) (x : Covector) : Spinor :=
  TwistedScalarJet.value (β x) (z x)

/-- The complex scalar can be taken outside the matrix action on the fixed reference spinor. -/
theorem field_eq_smul (β : Covector → ℝ) (z : Covector → ℂ) :
    field β z = fun x => z x • (chiral (β x)).mulVec restSpinor := by
  funext x
  exact Matrix.mulVec_smul (chiral (β x)) (z x) restSpinor

/-- The spacetime field is as smooth locally as its angle and its scalar amplitude. -/
theorem contDiffAt_field {β : Covector → ℝ} {z : Covector → ℂ} {x : Covector} {n : WithTop ℕ∞}
    (hβ : ContDiffAt ℝ n β x) (hz : ContDiffAt ℝ n z x) : ContDiffAt ℝ n (field β z) x := by
  rw [field_eq_smul]
  exact hz.smul ((mulVecCLM restSpinor).contDiff.contDiffAt.comp x ((contDiff_chiral n).contDiffAt.comp x hβ))

/-- Pointwise differentiability of the two scalar inputs suffices at all amplitudes. -/
theorem differentiableAt_field {β : Covector → ℝ} {z : Covector → ℂ} {x : Covector}
    (hβ : DifferentiableAt ℝ β x) (hz : DifferentiableAt ℝ z x) : DifferentiableAt ℝ (field β z) x := by
  rw [field_eq_smul]
  exact hz.smul ((mulVecCLM restSpinor).differentiableAt.comp x ((differentiable_chiral _).comp x hβ))

/-- The actual Fréchet derivative in any spacetime direction is the chiral scalar jet. -/
theorem fderiv_field_apply {β : Covector → ℝ} {z : Covector → ℂ} {x : Covector}
    (hβ : DifferentiableAt ℝ β x) (hz : DifferentiableAt ℝ z x) (v : Covector) :
    fderiv ℝ (field β z) x v = TwistedScalarJet.jet (β x) (z x) (fderiv ℝ z x v) (fderiv ℝ β x v) := by
  have hC : DifferentiableAt ℝ (fun y => chiral (β y)) x := (differentiable_chiral (β x)).comp x hβ
  have hV : DifferentiableAt ℝ (fun y => (chiral (β y)).mulVec restSpinor) x :=
    (mulVecCLM restSpinor).differentiableAt.comp x hC
  rw [field_eq_smul, fderiv_fun_smul hz hV, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    fderiv_mulVec_const_apply hC restSpinor, fderiv_chiral_comp_apply hβ]
  simp only [TwistedScalarJet.jet, embed, Matrix.mulVec_add, Matrix.smul_mulVec,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, (chiral_gamma5_commute (β x)).eq, smul_smul]
  rw [add_comm, mul_comm (z x)]

/-- With a scalar density and action phase, the rotated field has exactly the specified chiral angle and plane rotor. -/
theorem field_eq_polarSpinor (p : MassiveParameters) (ρ S β : Covector → ℝ) (x : Covector) :
    field β (ActionDensity.actionField p ρ S) x = polarSpinor (ρ x) (β x) (phaseRotor p S x) := by
  change (chiral (β x)).mulVec (ActionDensity.actionField p ρ S x • restSpinor) = _
  rw [← polarSpinor_eq_actionField p ρ S x, polarSpinor, chiral_zero, one_mul, Matrix.mulVec_smul, polarSpinor,
    Matrix.mulVec_mulVec]

/-- The actual invariant density is the Born density of the scalar field, even at zeros. -/
theorem invariantDensity_field (β : Covector → ℝ) (z : Covector → ℂ) (x : Covector) :
    invariantDensity (field β z x) = Complex.normSq (z x) :=
  TwistedScalarJet.invariantDensity_value _ _

/-- The field belongs to the regular polar domain precisely where the scalar does not vanish. -/
theorem regular_field_iff (β : Covector → ℝ) (z : Covector → ℂ) (x : Covector) :
    Regular (field β z x) ↔ z x ≠ 0 := TwistedScalarJet.regular_value_iff _ _

/-- On a nonnegative scalar density the explicit realization has exactly that invariant density. -/
theorem invariantDensity_actionField (p : MassiveParameters) (ρ S β : Covector → ℝ) {x : Covector} (hp : 0 ≤ ρ x) :
    invariantDensity (field β (ActionDensity.actionField p ρ S) x) = ρ x := by
  rw [invariantDensity_field]
  exact ActionDensity.polarField_normSq ρ _ x hp

/-- Strict positive density and locally C¹ inputs give genuine factors with the original
angle β and the same determinant-one plane matrix, throughout a neighborhood. -/
def factors (p : MassiveParameters) {ρ S β : Covector → ℝ} {x : Covector}
    (hρ : ContDiffAt ℝ 1 ρ x) (hS : ContDiffAt ℝ 1 S x) (hβ : ContDiffAt ℝ 1 β x) (hp : 0 < ρ x) :
    DiracHSDensity.LocalFactors (field β (ActionDensity.actionField p ρ S)) x where
  angle := β
  rotor y := planeMatrix (-(S y / p.hbar))
  density_smooth := hρ.congr_of_eventuallyEq (hρ.continuousAt.eventually (lt_mem_nhds hp) |>.mono
    (fun _ hy => invariantDensity_actionField p ρ S β hy.le))
  angle_smooth := hβ
  rotor_smooth := (contDiff_planeMatrix 1).contDiffAt.comp x (hS.div_const p.hbar).neg
  realization := by
    filter_upwards [hρ.continuousAt.eventually (lt_mem_nhds hp)] with y hy
    rw [invariantDensity_actionField p ρ S β hy.le, spin_planeMatrix]
    exact ⟨hy, det_planeMatrix _, field_eq_polarSpinor p ρ S β y⟩

end FoliationQM.TwistedScalarField
