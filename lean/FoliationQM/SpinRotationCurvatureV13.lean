module
public import FoliationQM.ScalarSpinPrimitive
public import FoliationQM.SpinLorentzSphere

/-!
# A spatial rotation field with nonzero spin-axis curvature

The nonvanishing assertion in v13 `thm:dirac_lift` (i) is witnessed by
two independent spatial rotations. Their product is a smooth unitary
determinant-one field. Its time axis remains fixed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.Operator Topology ContDiff ComplexConjugate
namespace FoliationQM.SpinRotationCurvatureV13
open SpinorMatrix DiracFieldDensity SpecialLinearConnection SpecialLinearTangent
open ScalarSpinPrimitive

/-- A trace-free skew-Hermitian spatial generator. -/
def axis (q : ℂ) : Mat2 := !![0, q; -conj q, 0]

/-- A rotation around the indicated spatial axis when the coefficient has unit modulus. -/
def rot (q : ℂ) (t : ℝ) : Mat2 := (Real.cos t : ℂ) • 1 + (Real.sin t : ℂ) • axis q

/-- Both coordinate rotations are smooth. -/
theorem smooth_rot (q : ℂ) (n : WithTop ℕ∞) : ContDiff ℝ n (rot q) :=
  ((Complex.ofRealCLM.contDiff.comp Real.contDiff_cos).smul contDiff_const).add
    ((Complex.ofRealCLM.contDiff.comp Real.contDiff_sin).smul contDiff_const)

/-- The rotation starts at the identity. -/
theorem rot_zero (q : ℂ) : rot q 0 = 1 := by simp [rot]

private theorem trig (t : ℝ) : (Real.cos t : ℂ)^2 + (Real.sin t : ℂ)^2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq t

/-- Each rotation is determinant one. -/
theorem det_rot {q : ℂ} (hq : q * conj q = 1) (t : ℝ) : (rot q t).det = 1 := by
  simp [Matrix.det_fin_two, rot, axis, -Complex.ofReal_cos, -Complex.ofReal_sin]
  linear_combination trig t + (Real.sin t : ℂ)^2 * hq

/-- Each rotation is unitary. -/
theorem unitary_rot {q : ℂ} (hq : q * conj q = 1) (t : ℝ) :
    rot q t * (rot q t).conjTranspose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, axis, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_succ, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    first | linear_combination trig t + (Real.sin t : ℂ)^2 * hq | ring

/-- The two-parameter product field, in two of the spatial coordinate directions. -/
def field (x : Covector) : Mat2 := rot 1 (x 1) * rot Complex.I (x 2)

private theorem unitI : Complex.I * conj Complex.I = 1 := by simp

/-- The surface is smooth, with determinant one and fixed observer time axis. -/
theorem spatial_field (n : WithTop ℕ∞) :
    ContDiff ℝ n field ∧ ∀ x, (field x).det = 1 ∧
      SpinLorentzAction.lorentzMatrix (field x) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  constructor
  · exact ((smooth_rot 1 n).comp (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 1)).mul
      ((smooth_rot Complex.I n).comp (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 2))
  · intro x
    have hd : (field x).det = 1 := by rw [field, Matrix.det_mul, det_rot (by simp : (1 : ℂ) * conj 1 = 1), det_rot unitI, one_mul]
    refine ⟨hd, SpinLorentzSphere.time_fixed_of_unitary _ hd ?_⟩
    rw [field, Matrix.conjTranspose_mul, mul_assoc, ← mul_assoc (rot Complex.I _) , unitary_rot unitI, one_mul,
      unitary_rot (by simp : (1 : ℂ) * conj 1 = 1)]

private theorem rot_deriv (q : ℂ) : HasDerivAt (rot q) (axis q) 0 := by
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (Real.hasDerivAt_cos 0)).smul_const (1 : Mat2)
  have hs := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (Real.hasDerivAt_sin 0)).smul_const (axis q)
  change HasDerivAt (fun t : ℝ => (Real.cos t : ℂ) • (1 : Mat2) + (Real.sin t : ℂ) • axis q) _ 0
  simpa [Function.comp_def, -Complex.ofReal_cos, -Complex.ofReal_sin] using hc.fun_add hs

/-- The actual body field in each direction at the identity. -/
theorem body_origin (v : Covector) : body2 field 0 v = v 1 • axis 1 + v 2 • axis Complex.I := by
  have h (q : ℂ) (i : Fin 4) := (rot_deriv q).hasFDerivAt.comp (f := fun x : Covector => x i) 0 (hasFDerivAt_apply i 0)
  have hd := (h 1 1).fun_mul' (h Complex.I 2)
  simp only [Function.comp_apply, Pi.zero_apply, rot_zero] at hd
  unfold body2
  rw [show field 0 = 1 by simp [field, rot_zero]]
  simp only [inv_one, one_mul]
  change fderiv ℝ (fun x : Covector => rot 1 (x 1) * rot Complex.I (x 2)) 0 v = _
  rw [hd.fderiv]
  simp [add_comm]

/-- The curvature coefficient is nonzero at the identity of this genuine rotation field. -/
theorem curvature_origin : curvature field 0 (coordinateDirections 1) (coordinateDirections 2) = -4 := by
  norm_num [curvature, bodyOmega, body_origin, coordinateDirections, SpecialLinearLieAlgebra.omega,
    axis, RealLorentzFrame.sign, Fin.sum_univ_succ]

/-- The alternating derivative of the physical spin-axis connection at the origin equals −2ℏ. -/
theorem physical_curvature_origin (p : MassiveParameters) :
    fderiv ℝ (oneForm p field) 0 (coordinateDirections 1) (coordinateDirections 2) -
    fderiv ℝ (oneForm p field) 0 (coordinateDirections 2) (coordinateDirections 1) = -2*p.hbar := by
  rw [alternatingDerivative_eq p (spatial_field 2).1.contDiffAt (Filter.Eventually.of_forall fun x => ((spatial_field 2).2 x).1), curvature_origin]
  ring

/-- No phase primitive exists on an open neighborhood containing this point of the rotation surface. -/
theorem no_primitive_near_origin (p : MassiveParameters) {U : Set Covector} (hU : IsOpen U) (h0 : 0 ∈ U) :
    ¬ ∃ S : Covector → ℝ, ∀ x ∈ U, HasFDerivAt S (oneForm p field x) x := by
  rintro ⟨S, hS⟩
  have hf := flatOn_of_primitive p hU (fun _ _ => (spatial_field 2).1.contDiffAt)
    (fun x _ => ((spatial_field 2).2 x).1) hS
  have hz := hf 0 h0 (coordinateDirections 1) (coordinateDirections 2)
  rw [curvature_origin] at hz
  norm_num at hz

end FoliationQM.SpinRotationCurvatureV13
