module
public import FoliationQM.SpecialLinearConnection
public import FoliationQM.LorentzConnectionCurvature

/-!
# Actual curvature of the constructed determinant-one matrix coefficients

Source: the Maurer--Cartan structure equation and spin-connection curvature
in v13 `lem:maurer_cartan` and the proof of `thm:dirac_lift`. The input is
an actual locally C2 two-by-two matrix field whose determinant is one on
a neighborhood. Its actual inverse, genuine derivative field and explicit
real coefficient map derive differentiability of the constructed body and
spatial coefficients. Local differentiability and determinant one also
derive their genuine generator expansions throughout a neighborhood.

The established matrix Maurer--Cartan equations and faithful coefficient
expansion then prove coefficient flatness: positive bracket for the body
connection and negative bracket for the spatial connection. The actual
scalar spin connection has the source positive half-hbar signed
contraction as its alternating derivative. No generator expansion,
coefficient differentiability, second-derivative symmetry or curvature
identity is supplied as a premise. Exterior-form packaging and global
bundle classification remain separate from these local identities.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.SpecialLinearCurvature
open DiracMatrices SpinorMatrix SpecialLinearSpin SpecialLinearTangent
open SpecialLinearLieAlgebra SpecialLinearConnection SpinorMatrixSmooth
open CliffordCommutators LorentzGeneratorBracket LorentzConnectionCurvature
open LorentzCoefficientUniqueness MaurerCartanDifferential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hasFDerivAt_matrix2_inv (A : Mat2) (hA : IsUnit A) :
    HasFDerivAt (fun B : Mat2 => B⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ Mat2 A⁻¹ A⁻¹) A := by
  rcases hA with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit] using
    (hasFDerivAt_ringInverse (𝕜 := ℝ) u)

private theorem matrix2_isUnit {A : Mat2} (hdet : A.det = 1) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (by rw [hdet]; exact isUnit_one)

private theorem directional_differentiable {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (w : E) :
    DifferentiableAt ℝ (fun y => fderiv ℝ A y w) x :=
  ((hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_const w)

/-- Local C2 regularity and determinant one at the point make the actual constructed body coefficient field differentiable in every fixed direction. -/
theorem differentiableAt_bodyOmega {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : (A x).det = 1) (w : E) :
    DifferentiableAt ℝ (fun y => bodyOmega A y w) x := by
  have hi := (hasFDerivAt_matrix2_inv (A x) (matrix2_isUnit hdet)).differentiableAt.comp x
    (hA.differentiableAt (by norm_num))
  exact omegaCLM.differentiableAt.comp x (hi.mul (directional_differentiable hA w))

/-- Local C2 regularity and determinant one at the point make the actual constructed spatial coefficient field differentiable in every fixed direction. -/
theorem differentiableAt_spatialOmega {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : (A x).det = 1) (w : E) :
    DifferentiableAt ℝ (fun y => spatialOmega A y w) x := by
  have hi := (hasFDerivAt_matrix2_inv (A x) (matrix2_isUnit hdet)).differentiableAt.comp x
    (hA.differentiableAt (by norm_num))
  exact omegaCLM.differentiableAt.comp x ((directional_differentiable hA w).mul hi)

/-- Every scalar entry of the constructed body coefficient field is genuinely differentiable under local C2 regularity and pointwise determinant one. -/
theorem differentiableAt_bodyOmega_entry {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : (A x).det = 1) (w : E) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => bodyOmega A y w a b) x :=
  differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_bodyOmega hA hdet w) a) b

/-- Every scalar entry of the constructed spatial coefficient field is genuinely differentiable under local C2 regularity and pointwise determinant one. -/
theorem differentiableAt_spatialOmega_entry {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : (A x).det = 1) (w : E) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => spatialOmega A y w a b) x :=
  differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_spatialOmega hA hdet w) a) b

/-- An actual locally C2 determinant-one field has its constructed body-generator expansion on a neighborhood, in every direction. -/
theorem eventual_body_expansion {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) :
    ∀ᶠ y in 𝓝 x, ∀ w, body (fun z => spin (A z)) y w = generator (bodyOmega A y w) := by
  filter_upwards [hA.eventually (by norm_num), hdet.eventually_nhds] with y hy hdy
  exact fun w => body_eq_generator (hy.differentiableAt (by norm_num)) hdy w

/-- An actual locally C2 determinant-one field has its constructed spatial-generator expansion on a neighborhood, in every direction. -/
theorem eventual_spatial_expansion {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) :
    ∀ᶠ y in 𝓝 x, ∀ w, spatial (fun z => spin (A z)) y w = generator (spatialOmega A y w) := by
  filter_upwards [hA.eventually (by norm_num), hdet.eventually_nhds] with y hy hdy
  exact fun w => spatial_eq_generator (hy.differentiableAt (by norm_num)) hdy w

/-- The actual constructed body coefficient field satisfies the positive-bracket Maurer--Cartan equation, derived solely from local C2 regularity and determinant one. -/
theorem body_coefficient_curvature {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v w : E) :
    coefficientDerivative (bodyOmega A) x v w - coefficientDerivative (bodyOmega A) x w v +
      bracket (bodyOmega A x v) (bodyOmega A x w) = 0 :=
  coefficient_curvature ((contDiff_spin 2).contDiffAt.comp x hA)
    (spin_isUnit _ hdet.self_of_nhds)
    (differentiableAt_bodyOmega_entry hA hdet.self_of_nhds)
    (Filter.Eventually.of_forall (fun y w a b => bodyOmega_antisymmetric A y w a b))
    (eventual_body_expansion hA hdet) v w

/-- Each actual body coefficient component satisfies the directional structure equation with the positive signed Lorentz bracket. -/
theorem body_coefficient_curvature_apply {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v w : E) (a b : Fin 4) :
    fderiv ℝ (fun y => bodyOmega A y w a b) x v -
      fderiv ℝ (fun y => bodyOmega A y v a b) x w +
      bracket (bodyOmega A x v) (bodyOmega A x w) a b = 0 :=
  coefficient_curvature_apply ((contDiff_spin 2).contDiffAt.comp x hA)
    (spin_isUnit _ hdet.self_of_nhds)
    (differentiableAt_bodyOmega_entry hA hdet.self_of_nhds)
    (Filter.Eventually.of_forall (fun y w a b => bodyOmega_antisymmetric A y w a b))
    (eventual_body_expansion hA hdet) v w a b

/-- The actual constructed scalar spin connection has the source positive half-hbar signed coefficient contraction as its alternating directional derivative. -/
theorem spinConnection_curvature {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (hbar : ℝ) (v w : E) :
    fderiv ℝ (fun y => spinConnection hbar (bodyOmega A) y w) x v -
      fderiv ℝ (fun y => spinConnection hbar (bodyOmega A) y v) x w =
      (hbar/2) * ∑ c, RealLorentzFrame.sign c *
        (bodyOmega A x v 1 c * bodyOmega A x w c 2 - bodyOmega A x w 1 c * bodyOmega A x v c 2) :=
  LorentzConnectionCurvature.spinConnection_curvature ((contDiff_spin 2).contDiffAt.comp x hA)
    (spin_isUnit _ hdet.self_of_nhds)
    (differentiableAt_bodyOmega_entry hA hdet.self_of_nhds)
    (Filter.Eventually.of_forall (fun y w a b => bodyOmega_antisymmetric A y w a b))
    (eventual_body_expansion hA hdet) hbar v w

/-- The actual derivative of the represented spatial connection is the generator of the actual derivative of its constructed coefficient field. -/
theorem fderiv_spatial_coefficients {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v w : E) :
    fderiv ℝ (fun y => spatial (fun z => spin (A z)) y w) x v =
      generator (coefficientDerivative (spatialOmega A) x v w) := by
  have heq : (fun y => spatial (fun z => spin (A z)) y w) =ᶠ[𝓝 x]
      (fun y => generator (spatialOmega A y w)) :=
    (eventual_spatial_expansion hA hdet).mono (fun _ hy => hy w)
  have he := congrArg (fun T : E →L[ℝ] Mat => T v) heq.fderiv_eq
  exact he.trans (fderiv_generator_comp_apply
    (differentiableAt_spatialOmega hA hdet.self_of_nhds w) v)

/-- The actual constructed spatial coefficient field satisfies the negative-bracket Maurer--Cartan equation without a supplied flatness premise. -/
theorem spatial_coefficient_curvature {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v w : E) :
    coefficientDerivative (spatialOmega A) x v w - coefficientDerivative (spatialOmega A) x w v -
      bracket (spatialOmega A x v) (spatialOmega A x w) = 0 := by
  have hcurv := MaurerCartanCurvature.spatial_curvature
    ((contDiff_spin 2).contDiffAt.comp x hA) (spin_isUnit _ hdet.self_of_nhds) v w
  simp only [Function.comp_def] at hcurv
  rw [fderiv_spatial_coefficients hA hdet v w, fderiv_spatial_coefficients hA hdet w v,
    spatial_eq_generator (hA.differentiableAt (by norm_num)) hdet v,
    spatial_eq_generator (hA.differentiableAt (by norm_num)) hdet w] at hcurv
  have hgen : generator (coefficientDerivative (spatialOmega A) x v w -
      coefficientDerivative (spatialOmega A) x w v -
      bracket (spatialOmega A x v) (spatialOmega A x w)) = 0 := by
    change generatorCLM (coefficientDerivative (spatialOmega A) x v w -
      coefficientDerivative (spatialOmega A) x w v -
      bracket (spatialOmega A x v) (spatialOmega A x w)) = 0
    rw [map_sub, map_sub]
    simp only [generatorCLM_apply]
    rw [← generator_commutator _ _ (spatialOmega_antisymmetric A x v)
      (spatialOmega_antisymmetric A x w)]
    convert hcurv using 1
    abel
  have hanti : ∀ a b,
      (coefficientDerivative (spatialOmega A) x v w -
        coefficientDerivative (spatialOmega A) x w v -
        bracket (spatialOmega A x v) (spatialOmega A x w)) a b =
      -(coefficientDerivative (spatialOmega A) x v w -
        coefficientDerivative (spatialOmega A) x w v -
        bracket (spatialOmega A x v) (spatialOmega A x w)) b a := by
    intro a b
    simp only [Pi.sub_apply]
    rw [coefficientDerivative_antisymmetric v w
        (differentiableAt_spatialOmega_entry hA hdet.self_of_nhds w)
        (Filter.Eventually.of_forall (fun y => spatialOmega_antisymmetric A y w)) a b,
      coefficientDerivative_antisymmetric w v
        (differentiableAt_spatialOmega_entry hA hdet.self_of_nhds v)
        (Filter.Eventually.of_forall (fun y => spatialOmega_antisymmetric A y v)) a b,
      bracket_antisymmetric _ _ (spatialOmega_antisymmetric A x v)
        (spatialOmega_antisymmetric A x w) a b]
    ring
  exact (generator_eq_zero_iff _ hanti).mp hgen

/-- Each actual spatial coefficient component satisfies the directional structure equation with the negative signed Lorentz bracket. -/
theorem spatial_coefficient_curvature_apply {A : E → Mat2} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v w : E) (a b : Fin 4) :
    fderiv ℝ (fun y => spatialOmega A y w a b) x v -
      fderiv ℝ (fun y => spatialOmega A y v a b) x w -
      bracket (spatialOmega A x v) (spatialOmega A x w) a b = 0 := by
  have h := congrFun (congrFun (spatial_coefficient_curvature hA hdet v w) a) b
  simpa only [Pi.sub_apply, Pi.zero_apply,
    coefficientDerivative_apply v w (differentiableAt_spatialOmega_entry hA hdet.self_of_nhds w),
    coefficientDerivative_apply w v (differentiableAt_spatialOmega_entry hA hdet.self_of_nhds v)] using h

end FoliationQM.SpecialLinearCurvature
