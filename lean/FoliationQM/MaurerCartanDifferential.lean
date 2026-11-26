module
public import FoliationQM.MatrixDifferential
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Actual first-order Maurer–Cartan and polar-frame derivatives

Source: v13 `lem:maurer_cartan` and the polar derivative calculation.
The body and spatial connections are defined from actual real Frechet
 derivatives of an invertible matrix field. Local matrix constraints are
 differentiated, rather than supplying their differentiated conclusions.
Curvature and real Lorentz coefficient reconstruction are separate results.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.MaurerCartanDifferential
open DiracMatrices DiracAdjoint MatrixDifferential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The body Maurer–Cartan coefficient of an actual matrix field in a direction. -/
def body (L : E → Mat) (x v : E) : Mat := (L x)⁻¹ * fderiv ℝ L x v

/-- The spatial Maurer–Cartan coefficient of an actual matrix field in a direction. -/
def spatial (L : E → Mat) (x v : E) : Mat := fderiv ℝ L x v * (L x)⁻¹

/-- Multiplying the body coefficient by the matrix recovers its actual derivative. -/
theorem mul_body {L : E → Mat} {x : E} (hunit : IsUnit (L x)) (v : E) :
    L x * body L x v = fderiv ℝ L x v := by
  simp [body, ← mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)]

/-- Multiplying the spatial coefficient by the matrix recovers its actual derivative. -/
theorem spatial_mul {L : E → Mat} {x : E} (hunit : IsUnit (L x)) (v : E) :
    spatial L x v * L x = fderiv ℝ L x v := by
  simp [spatial, mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)]

/-- The body and spatial actual derivative coefficients are related by conjugation. -/
theorem spatial_eq_conjugate_body {L : E → Mat} {x : E}
    (hunit : IsUnit (L x)) (v : E) :
    spatial L x v = L x * body L x v * (L x)⁻¹ := by rw [mul_body hunit]; rfl

/-- The body coefficient is additive in the tangent direction. -/
theorem body_add (L : E → Mat) (x v w : E) :
    body L x (v+w) = body L x v + body L x w := by simp [body, mul_add]

/-- The spatial coefficient is additive in the tangent direction. -/
theorem spatial_add (L : E → Mat) (x v w : E) :
    spatial L x (v+w) = spatial L x v + spatial L x w := by simp [spatial, add_mul]

/-- The body coefficient is real-linear in the tangent direction. -/
theorem body_smul (L : E → Mat) (x v : E) (r : ℝ) :
    body L x (r • v) = r • body L x v := by simp [body]

/-- The spatial coefficient is real-linear in the tangent direction. -/
theorem spatial_smul (L : E → Mat) (x v : E) (r : ℝ) :
    spatial L x (r • v) = r • spatial L x v := by simp [spatial]

/-- An invertible matrix commuting with a matrix has an inverse commuting with it. -/
theorem inverse_commute {A B : Mat} (hunit : IsUnit A) (h : Commute A B) :
    Commute A⁻¹ B := by
  have hleft := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hright := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  change A⁻¹*B = B*A⁻¹
  calc
    _ = A⁻¹*B*(A*A⁻¹) := by rw [hright, mul_one]
    _ = A⁻¹*(B*A)*A⁻¹ := by simp only [mul_assoc]
    _ = A⁻¹*(A*B)*A⁻¹ := by rw [h.eq]
    _ = _ := by simp only [← mul_assoc, hleft, one_mul]

/-- Locally commuting matrix fields have actual derivatives commuting with the same fixed matrix. -/
theorem fderiv_commute {L : E → Mat} {x : E} (hL : DifferentiableAt ℝ L x)
    (B : Mat) (hB : ∀ᶠ y in 𝓝 x, Commute (L y) B) (v : E) :
    Commute (fderiv ℝ L x v) B := by
  have heq : (fun y => L y * B) =ᶠ[𝓝 x] (fun y => B * L y) := hB.mono fun _ h => h.eq
  have hd := congrArg (fun T : E →L[ℝ] Mat => T v) heq.fderiv_eq
  have hl : fderiv ℝ (fun y => L y * B) x v = fderiv ℝ L x v * B := by
    simpa using! congrArg (fun T : E →L[ℝ] Mat => T v) (hL.hasFDerivAt.mul_const' B).fderiv
  have hr : fderiv ℝ (fun y => B * L y) x v = B * fderiv ℝ L x v := by
    simpa using! congrArg (fun T : E →L[ℝ] Mat => T v) (hL.hasFDerivAt.const_mul B).fderiv
  exact hl.symm.trans (hd.trans hr)

/-- The actual spatial connection commutes with gamma5 when the matrix field does locally. -/
theorem spatial_commute_gamma5 {L : E → Mat} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5) (v : E) :
    Commute (spatial L x v) gamma5 :=
  (fderiv_commute hL gamma5 h5 v).mul_left (inverse_commute hunit h5.self_of_nhds)

/-- The inverse of a Dirac-isometric matrix is its actual Dirac adjoint. -/
theorem inverse_eq_diracAdjoint {A : Mat} (hiso : diracAdjoint A * A = 1) :
    A⁻¹ = diracAdjoint A := Matrix.inv_eq_left_inv hiso

/-- A local Dirac isometry differentiates to the actual right product identity. -/
theorem fderiv_right_isometry {L : E → Mat} {x : E}
    (hL : DifferentiableAt ℝ L x)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y) * L y = 1) (v : E) :
    fderiv ℝ L x v * diracAdjoint (L x) + L x * diracAdjoint (fderiv ℝ L x v) = 0 := by
  have heq : (fun y => L y * diracAdjoint (L y)) =ᶠ[𝓝 x] (fun _ => (1 : Mat)) :=
    hiso.mono fun _ h => mul_eq_one_comm.mp h
  have hd := congrArg (fun T : E →L[ℝ] Mat => T v) heq.fderiv_eq
  have hp : fderiv ℝ (fun y => L y * diracAdjoint (L y)) x v =
      L x * diracAdjoint (fderiv ℝ L x v) + fderiv ℝ L x v * diracAdjoint (L x) := by
    simpa using! congrArg (fun T : E →L[ℝ] Mat => T v)
      (hL.hasFDerivAt.mul' (hasFDerivAt_diracAdjoint_field hL.hasFDerivAt)).fderiv
  rw [hp, fderiv_const_apply] at hd
  simpa only [add_comm, zero_apply] using hd

/-- The actual spatial connection is anti-self-adjoint for a locally Dirac-isometric matrix field. -/
theorem spatial_diracAdjoint {L : E → Mat} {x : E}
    (hL : DifferentiableAt ℝ L x) (_hunit : IsUnit (L x))
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y) * L y = 1) (v : E) :
    diracAdjoint (spatial L x v) = -spatial L x v := by
  have hi := inverse_eq_diracAdjoint hiso.self_of_nhds
  have hd := fderiv_right_isometry hL hiso v
  rw [← hi] at hd
  apply eq_neg_of_add_eq_zero_right
  simpa only [spatial, diracAdjoint_mul, hi, diracAdjoint_involutive] using hd

/-- A fixed matrix transported by the actual invertible matrix field. -/
def frame (L : E → Mat) (A : Mat) (x : E) : Mat := L x * A * (L x)⁻¹

/-- The actual derivative of the conjugated frame follows from the product and inverse rules. -/
theorem fderiv_frame_raw {L : E → Mat} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x)) (A : Mat) (v : E) :
    fderiv ℝ (frame L A) x v =
      fderiv ℝ L x v * A * (L x)⁻¹ - L x * A * (L x)⁻¹ * fderiv ℝ L x v * (L x)⁻¹ := by
  have hd := congrArg (fun T : E →L[ℝ] Mat => T v)
    ((hL.hasFDerivAt.mul_const' A).mul'
      (hasFDerivAt_inv_field hL.hasFDerivAt hunit)).fderiv
  have hp : fderiv ℝ (frame L A) x v =
      (L x * A) * (-((L x)⁻¹ * fderiv ℝ L x v * (L x)⁻¹)) +
      (fderiv ℝ L x v * A) * (L x)⁻¹ := by
    simpa only [frame] using! hd
  rw [hp]
  noncomm_ring

/-- The actual frame derivative is the commutator with the spatial connection. -/
theorem fderiv_frame_spatial {L : E → Mat} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x)) (A : Mat) (v : E) :
    fderiv ℝ (frame L A) x v =
      spatial L x v * frame L A x - frame L A x * spatial L x v := by
  rw [fderiv_frame_raw hL hunit]
  have hc : spatial L x v * frame L A x = fderiv ℝ L x v * A * (L x)⁻¹ := by
    calc
      _ = (spatial L x v * L x) * A * (L x)⁻¹ := by simp only [frame, mul_assoc]
      _ = _ := by rw [spatial_mul hunit]
  rw [hc]
  simp only [frame, spatial, mul_assoc]

/-- The actual frame derivative is the conjugated commutator with the body connection. -/
theorem fderiv_frame_body {L : E → Mat} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x)) (A : Mat) (v : E) :
    fderiv ℝ (frame L A) x v =
      L x * (body L x v * A - A * body L x v) * (L x)⁻¹ := by
  rw [fderiv_frame_raw hL hunit]
  have hc : L x * (body L x v * A) * (L x)⁻¹ = fderiv ℝ L x v * A * (L x)⁻¹ := by
    rw [← mul_assoc (L x), mul_body hunit]
  rw [mul_sub, sub_mul, hc]
  simp only [body, mul_assoc]

end FoliationQM.MaurerCartanDifferential
