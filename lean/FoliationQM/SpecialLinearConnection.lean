module
public import FoliationQM.SpecialLinearLieAlgebra
public import FoliationQM.SpecialLinearTangent
public import FoliationQM.SpecialLinearSpinDifferential
public import FoliationQM.LorentzCoefficientUniqueness
/-!
# Constructed real Lorentz coefficients of actual matrix connections

Source: v13 `lem:maurer_cartan` and `eq:maurer_cartan_def`.
Actual differentiation of a locally determinant-one two-by-two field
forces its body and spatial tangents to be traceless. The six explicit
real coordinates therefore expand its genuine four-by-four connections.
No generator expansion is supplied. Uniqueness, real directional linearity,
conjugacy and both derivative factorizations are consequences.
Source-index frame contraction and original-spinor field assembly are
separate bridges; no abstract covering or global bundle theorem is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.SpecialLinearConnection
open DiracMatrices SpinorMatrix SpecialLinearSpin SpecialLinearTangent
open SpecialLinearLieAlgebra SpecialLinearSpinDifferential CliffordCommutators
open MaurerCartanDifferential LorentzCoefficientUniqueness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The six real antisymmetric body coefficients extracted from the actual two-by-two derivative product. -/
def bodyOmega (A : E → Mat2) (x v : E) : Fin 4 → Fin 4 → ℝ := omega (body2 A x v)
/-- The six real antisymmetric spatial coefficients extracted from the actual two-by-two derivative product. -/
def spatialOmega (A : E → Mat2) (x v : E) : Fin 4 → Fin 4 → ℝ := omega (spatial2 A x v)
/-- The constructed body coefficients are real and antisymmetric for every input field and direction. -/
theorem bodyOmega_antisymmetric (A : E → Mat2) (x v : E) (a b : Fin 4) :
    bodyOmega A x v a b = -bodyOmega A x v b a := omega_antisymmetric _ a b
/-- The constructed spatial coefficients are real and antisymmetric for every input field and direction. -/
theorem spatialOmega_antisymmetric (A : E → Mat2) (x v : E) (a b : Fin 4) :
    spatialOmega A x v a b = -spatialOmega A x v b a := omega_antisymmetric _ a b
/-- Actual differentiability and a local determinant-one constraint derive the body Lorentz-generator expansion. -/
theorem body_eq_generator {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E) :
    body (fun y => spin (A y)) x v = generator (bodyOmega A x v) := by
  rw [spin_body hA hdet.self_of_nhds v]
  exact spin_eq_generator _ (body2_trace_zero hA hdet v)
/-- Actual differentiability and a local determinant-one constraint derive the spatial Lorentz-generator expansion. -/
theorem spatial_eq_generator {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E) :
    spatial (fun y => spin (A y)) x v = generator (spatialOmega A x v) := by
  rw [spin_spatial hA hdet.self_of_nhds v]
  exact spin_eq_generator _ (spatial2_trace_zero hA hdet v)
/-- Any real antisymmetric expansion of the actual body connection equals the explicitly extracted coefficients. -/
theorem body_generator_unique {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E)
    {w : Fin 4 → Fin 4 → ℝ} (hw : ∀ a b, w a b = -w b a)
    (he : body (fun y => spin (A y)) x v = generator w) : w = bodyOmega A x v :=
  generator_injective_on_antisymmetric hw (bodyOmega_antisymmetric A x v)
    (he.symm.trans (body_eq_generator hA hdet v))
/-- Any real antisymmetric expansion of the actual spatial connection equals the explicitly extracted coefficients. -/
theorem spatial_generator_unique {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E)
    {w : Fin 4 → Fin 4 → ℝ} (hw : ∀ a b, w a b = -w b a)
    (he : spatial (fun y => spin (A y)) x v = generator w) : w = spatialOmega A x v :=
  generator_injective_on_antisymmetric hw (spatialOmega_antisymmetric A x v)
    (he.symm.trans (spatial_eq_generator hA hdet v))
/-- The actual representative derivative equals the representative times its constructed body generator. -/
theorem fderiv_spin_eq_mul_generator {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E) :
    fderiv ℝ (fun y => spin (A y)) x v = spin (A x) * generator (bodyOmega A x v) := by
  rw [← body_eq_generator hA hdet v, mul_body (L := fun y => spin (A y)) (spin_isUnit _ hdet.self_of_nhds)]
/-- The actual representative derivative equals its constructed spatial generator times the representative. -/
theorem fderiv_spin_eq_generator_mul {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E) :
    fderiv ℝ (fun y => spin (A y)) x v = generator (spatialOmega A x v) * spin (A x) := by
  rw [← spatial_eq_generator hA hdet v, spatial_mul (L := fun y => spin (A y)) (spin_isUnit _ hdet.self_of_nhds)]
/-- The two constructed actual generators are related by the genuine representative conjugation. -/
theorem generators_conjugate {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E) :
    generator (spatialOmega A x v) =
      spin (A x) * generator (bodyOmega A x v) * (spin (A x))⁻¹ := by
  rw [← body_eq_generator hA hdet v, ← spatial_eq_generator hA hdet v]
  exact spatial_eq_conjugate_body (L := fun y => spin (A y)) (spin_isUnit _ hdet.self_of_nhds) v
/-- The actual determinant-one body connection is Dirac anti-self-adjoint by its derived real generator expansion. -/
theorem body_diracAdjoint {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E) :
    DiracAdjoint.diracAdjoint (body (fun y => spin (A y)) x v) =
      -body (fun y => spin (A y)) x v := by
  rw [body_eq_generator hA hdet v, generator_diracAdjoint]
/-- The actual determinant-one spatial connection is Dirac anti-self-adjoint by its derived real generator expansion. -/
theorem spatial_diracAdjoint {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E) :
    DiracAdjoint.diracAdjoint (spatial (fun y => spin (A y)) x v) =
      -spatial (fun y => spin (A y)) x v := by
  rw [spatial_eq_generator hA hdet v, generator_diracAdjoint]
/-- The actual determinant-one body connection commutes with gamma5 by its derived generator expansion. -/
theorem body_commute_gamma5 {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E) :
    Commute (body (fun y => spin (A y)) x v) gamma5 := by
  rw [body_eq_generator hA hdet v]
  exact generator_gamma5_commute _
/-- The actual determinant-one spatial connection commutes with gamma5 by its derived generator expansion. -/
theorem spatial_commute_gamma5 {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E) :
    Commute (spatial (fun y => spin (A y)) x v) gamma5 := by
  rw [spatial_eq_generator hA hdet v]
  exact generator_gamma5_commute _
/-- The constructed body coefficients are additive in the actual tangent direction. -/
theorem bodyOmega_add (A : E → Mat2) (x v w : E) :
    bodyOmega A x (v+w) = bodyOmega A x v + bodyOmega A x w := by
  simp only [bodyOmega, body2, map_add, mul_add, omega_add]
/-- The constructed spatial coefficients are additive in the actual tangent direction. -/
theorem spatialOmega_add (A : E → Mat2) (x v w : E) :
    spatialOmega A x (v+w) = spatialOmega A x v + spatialOmega A x w := by
  simp only [spatialOmega, spatial2, map_add, add_mul, omega_add]
/-- The constructed body coefficients respect real scaling of the actual tangent direction. -/
theorem bodyOmega_smul (A : E → Mat2) (x v : E) (r : ℝ) :
    bodyOmega A x (r • v) = r • bodyOmega A x v := by
  simp only [bodyOmega, body2, map_smul, mul_smul_comm, omega_real_smul]
/-- The constructed spatial coefficients respect real scaling of the actual tangent direction. -/
theorem spatialOmega_smul (A : E → Mat2) (x v : E) (r : ℝ) :
    spatialOmega A x (r • v) = r • spatialOmega A x v := by
  simp only [spatialOmega, spatial2, map_smul, smul_mul_assoc, omega_real_smul]
end FoliationQM.SpecialLinearConnection
