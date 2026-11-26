module
public import FoliationQM.DiracEquation
public import FoliationQM.DiracAdjoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Real test pairing for the actual Dirac residual

For the first-order variational component of v13 `thm:dirac_lift`, the
real part of the Dirac-adjoint contraction detects all real and imaginary
components of the Dirac residual. The time matrix converts coordinate test
spinors into tests for the ordinary complex components, with the source's
kinetic and mass coefficients retained.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracResidualPairing
open DiracMatrices DiracAdjoint DiracEquation Matrix

/-- The real part of the Dirac-adjoint contraction with the identity matrix. -/
def pair (u v : Spinor) : ℝ := (bilinear u 1 v).re

/-- Swapping the arguments conjugates the complex contraction and preserves its real part. -/
theorem pair_comm (u v : Spinor) : pair u v = pair v u := by
  have h := congrArg Complex.re (star_bilinear u v 1)
  simpa [pair, diracAdjoint_one] using h

/-- Addition of spinor tests is addition of real pairings. -/
theorem pair_add_left (u v w : Spinor) : pair (u + v) w = pair u w + pair v w := by
  simp [pair, bilinear, add_dotProduct]

/-- The residual pairing is additive in its right argument. -/
theorem pair_add_right (u v w : Spinor) : pair u (v + w) = pair u v + pair u w := by
  rw [pair_comm u, pair_add_left, pair_comm v u, pair_comm w u]

/-- A real scalar multiplying the test factors out of the real Dirac pairing. -/
theorem pair_smul_left (a : ℝ) (u v : Spinor) : pair (a • u) v = a * pair u v := by
  rw [pair, ← IsScalarTower.algebraMap_smul ℂ a u, bilinear_smul_left]
  simp [pair, Complex.mul_re]

/-- A real scalar multiplying the residual factors out of the pairing. -/
theorem pair_smul_right (a : ℝ) (u v : Spinor) : pair u (a • v) = a * pair u v := by
  rw [pair_comm u, pair_smul_left, pair_comm v u]

/-- The continuous real linear map obtained by fixing the first test spinor. -/
def pairRight (u : Spinor) : Spinor →L[ℝ] ℝ :=
  ({ toFun := pair u
     map_add' := pair_add_right u
     map_smul' := fun a v => pair_smul_right a u v } : Spinor →ₗ[ℝ] ℝ).toContinuousLinearMap

/-- The residual pairing as a continuous real bilinear map. -/
def pairCLM : Spinor →L[ℝ] Spinor →L[ℝ] ℝ :=
  ({ toFun := pairRight
     map_add' := by
       intro u v
       ext w
       exact pair_add_left u v w
     map_smul' := by
       intro a u
       ext w
       exact pair_smul_left a u w } : Spinor →ₗ[ℝ] Spinor →L[ℝ] ℝ).toContinuousLinearMap

/-- The continuous-map construction evaluates to the original Dirac pairing. -/
theorem pairCLM_apply (u v : Spinor) : pairCLM u v = pair u v := rfl

/-- Acting on the left spinor by a gamma matrix gives the same gamma insertion
as acting on the right, using Dirac self-adjointness in Lorentz signature. -/
theorem bilinear_gamma_left (u v : Spinor) (μ : Fin 4) :
    bilinear ((gamma μ).mulVec u) 1 v = bilinear u (gamma μ) v := by
  rw [bilinear_mulVec_left, diracAdjoint_gamma, mul_one]

/-- Moving the gamma matrix from the right spinor into the contraction. -/
theorem bilinear_gamma_right (u v : Spinor) (μ : Fin 4) :
    bilinear u 1 ((gamma μ).mulVec v) = bilinear u (gamma μ) v := by
  rw [← bilinear_mul_matrix, one_mul]

/-- Multiplying by the time matrix in the test spinor cancels the time matrix in its adjoint. -/
def componentTest (i : Fin 4) (z : ℂ) : Spinor := (gamma 0).mulVec (Pi.single i z)

/-- A coordinate test isolates the specified complex component of any spinor. -/
theorem bilinear_componentTest (i : Fin 4) (z : ℂ) (v : Spinor) :
    bilinear (componentTest i z) 1 v = star z * v i := by
  rw [componentTest, bilinear_gamma_left, bilinear, gamma_zero_sq, one_mulVec, Pi.star_single,
    single_dotProduct]

/-- Real coordinate tests against the residual evaluate its ordinary complex components. -/
theorem pair_componentTest (i : Fin 4) (z : ℂ) (v : Spinor) :
    pair (componentTest i z) v = (star z * v i).re :=
  congrArg Complex.re (bilinear_componentTest i z v)

/-- Unit component tests detect the real part. -/
theorem pair_componentTest_one (i : Fin 4) (v : Spinor) :
    pair (componentTest i 1) v = (v i).re := by rw [pair_componentTest, star_one, one_mul]

/-- Imaginary component tests detect the imaginary part, with positive sign. -/
theorem pair_componentTest_I (i : Fin 4) (v : Spinor) :
    pair (componentTest i Complex.I) v = (v i).im := by
  simp [pair_componentTest, Complex.mul_re]

/-- Zero pairing against every real test value is equivalent to a zero spinor. -/
theorem forall_pair_zero_iff (v : Spinor) : (∀ u : Spinor, pair u v = 0) ↔ v = 0 := by
  constructor
  · intro h
    funext i
    exact Complex.ext ((pair_componentTest_one i v).symm.trans (h _))
      ((pair_componentTest_I i v).symm.trans (h _))
  · rintro rfl u
    simp [pair, bilinear]

/-- Complex contraction of the actual Dirac jet, retaining iℏ and the mass term mc. -/
theorem bilinear_diracJet (u : Spinor) (hbar m c : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) :
    bilinear u 1 (diracJet hbar m c psi jet) =
      (Complex.I * (hbar : ℂ)) * (∑ μ, bilinear u (gamma μ) (jet μ)) -
        ((m * c : ℝ) : ℂ) * bilinear u 1 psi := by
  have hadd (v w : Spinor) : bilinear u 1 (v - w) = bilinear u 1 v - bilinear u 1 w := by
    simp [bilinear, Matrix.mulVec_sub, dotProduct_sub]
  have hsum : bilinear u 1 (slashJet jet) = ∑ μ, bilinear u (gamma μ) (jet μ) := by
    unfold slashJet
    rw [show bilinear u 1 (∑ μ, (gamma μ).mulVec (jet μ)) =
      ∑ μ, bilinear u 1 ((gamma μ).mulVec (jet μ)) by simp [bilinear, Matrix.mulVec_sum, dotProduct_sum]]
    simp_rw [bilinear_gamma_right]
  rw [diracJet, hadd, bilinear_smul_right, bilinear_smul_right, hsum]

/-- The real kinetic coefficient of the Dirac residual is minus ℏ times the
imaginary gamma contraction; the real mass coefficient is minus mc. -/
theorem pair_diracJet (u : Spinor) (hbar m c : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) :
    pair u (diracJet hbar m c psi jet) =
      -hbar * (∑ μ, bilinear u (gamma μ) (jet μ)).im - m * c * pair u psi := by
  rw [pair, bilinear_diracJet]
  simp [pair, Complex.mul_re, Complex.mul_im]

/-- Vanishing against all real test values detects the actual first-order Dirac jet equation. -/
theorem jetEquation_iff_forall_pair (hbar m c : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) :
    jetEquation hbar m c psi jet ↔ ∀ u : Spinor, pair u (diracJet hbar m c psi jet) = 0 :=
  (diracJet_eq_zero_iff hbar m c psi jet).symm.trans (forall_pair_zero_iff _).symm

/-- Pointwise detection applied to the source coordinate residual of a spinor field. -/
theorem fieldEquation_iff_forall_pair (hbar m c : ℝ) (psi : Covector → Spinor)
    (x : Covector) :
    jetEquation hbar m c (psi x) (fun μ => fderiv ℝ psi x (DiracFieldDensity.coordinateDirections μ)) ↔
      ∀ u : Spinor, pair u (diracField hbar m c psi x) = 0 :=
  (diracField_eq_zero_iff hbar m c psi x).symm.trans (forall_pair_zero_iff _).symm

end FoliationQM.DiracResidualPairing
