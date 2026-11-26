module
public import FoliationQM.SpecialLinearRicci
public import FoliationQM.VelocitySpinKinetic
/-!
# Physical velocity and spin kinetics of actual determinant-one matrix fields

Source: v13 `eq:mc_velocity_spin_identity`, using the actual lower-gamma
physical frame constructed from a differentiable two-by-two matrix field.
The local determinant-one constraint supplies its invertibility, real
frame expansion and antisymmetric body coefficients by proved theorems.
Every derivative and Fermi--Walker projection below is therefore an actual
field derivative, with no frame or connection expansion supplied as a premise.

The dimensionless time and projected spin norms are stated first, followed
by physical velocity identities on the explicit nonzero-c domain. The
four-direction formula keeps the diagonal (+---) weights and the established
spin coefficient. These are first-derivative kinematic identities; no
variational or global classification result is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.SpecialLinearPhysicalKinetic
open DiracMatrices SpinorMatrix SpecialLinearSpin SpecialLinearFrame
open SpecialLinearSpinDifferential SpecialLinearConnection SpecialLinearRicci
open RealLorentzFrame PolarVectorGeometry FermiWalkerProjection SixTermConnection
open CanonicalDiracContraction VelocitySpinKinetic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual dimensionless time-vector derivative has the negative sum of the three squared boost coefficients. The coefficients come from its actual determinant-one matrix field. -/
theorem time_derivative_squared {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) :
    minkowski (fderiv ℝ (fun y => timeVector (frame (A y))) x v)
      (fderiv ℝ (fun y => timeVector (frame (A y))) x v) =
      -((bodyOmega A x v 0 1)^2+(bodyOmega A x v 0 2)^2+(bodyOmega A x v 0 3)^2) := by
  exact VelocitySpinKinetic.time_derivative_squared (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v)

/-- The normalized projection of the actual spin derivative has exactly the two negative squared transverse rotation coefficients. The coefficients come from its actual determinant-one matrix field. -/
theorem normalized_spin_derivative_squared {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) :
    minkowski
      (normalizedProjection (timeVector (frame (A x))) (fderiv ℝ (fun y => spinVector (frame (A y))) x v))
      (normalizedProjection (timeVector (frame (A x))) (fderiv ℝ (fun y => spinVector (frame (A y))) x v)) =
      -((bodyOmega A x v 1 3)^2+(bodyOmega A x v 2 3)^2) := by
  exact VelocitySpinKinetic.normalized_spin_derivative_squared (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v)

/-- The dimensionless source identity follows from the actual time and normalized projected-spin derivative norms. The coefficients come from its actual determinant-one matrix field. -/
theorem mc_time_spin_identity {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) :
    pairedProductSum (bodyOmega A x v) (bodyOmega A x v) = (bodyOmega A x v 1 2)^2 -
      (minkowski
        (normalizedProjection (timeVector (frame (A x))) (fderiv ℝ (fun y => spinVector (frame (A y))) x v))
        (normalizedProjection (timeVector (frame (A x))) (fderiv ℝ (fun y => spinVector (frame (A y))) x v)) -
       minkowski (fderiv ℝ (fun y => timeVector (frame (A y))) x v)
         (fderiv ℝ (fun y => timeVector (frame (A y))) x v)) := by
  exact VelocitySpinKinetic.mc_time_spin_identity (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v)

/-- The actual Fermi--Walker projected spin derivative has the source transverse rotation norm at every nonzero c. The coefficients come from its actual determinant-one matrix field. -/
theorem fwSpinDerivative_squared {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (c : ℝ) (hc : c ≠ 0) :
    minkowski (fwSpinDerivative c (fun y => frame (A y)) x v) (fwSpinDerivative c (fun y => frame (A y)) x v) =
      -((bodyOmega A x v 1 3)^2+(bodyOmega A x v 2 3)^2) := by
  exact VelocitySpinKinetic.fwSpinDerivative_squared (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) c hc

/-- The actual physical velocity derivative norm divided by c squared equals the negative squared boost sum. The coefficients come from its actual determinant-one matrix field. -/
theorem velocity_derivative_squared_div {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (c : ℝ) (hc : c ≠ 0) :
    minkowski (fderiv ℝ (fun y => velocity c (frame (A y))) x v)
      (fderiv ℝ (fun y => velocity c (frame (A y))) x v) / c^2 =
      -((bodyOmega A x v 0 1)^2+(bodyOmega A x v 0 2)^2+(bodyOmega A x v 0 3)^2) := by
  exact VelocitySpinKinetic.velocity_derivative_squared_div (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) c hc

/-- The actual per-direction source identity decomposes the Lorentz six-pair square into spin rotation, projected spin derivative and physical velocity derivative. The coefficients come from its actual determinant-one matrix field. -/
theorem mc_velocity_spin_direction {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (v : E) (c : ℝ) (hc : c ≠ 0) :
    pairedProductSum (bodyOmega A x v) (bodyOmega A x v) = (bodyOmega A x v 1 2)^2 -
      (minkowski (fwSpinDerivative c (fun y => frame (A y)) x v) (fwSpinDerivative c (fun y => frame (A y)) x v) -
        (1/c^2)*minkowski (fderiv ℝ (fun y => velocity c (frame (A y))) x v)
          (fderiv ℝ (fun y => velocity c (frame (A y))) x v)) := by
  exact VelocitySpinKinetic.mc_velocity_spin_direction (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) v (bodyOmega A x v)
    (bodyOmega_antisymmetric A x v) (body_eq_generator hA hdet v) c hc

/-- The exact source velocity-spin identity holds for the actual four directional derivatives, with the diagonal spacetime metric, actual Fermi--Walker projection and established spin coefficient. The coefficients come from its actual determinant-one matrix field. -/
theorem mc_velocity_spin_identity {A : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1)
    (directions : Fin 4 → E) (rho hbar c : ℝ) (hc : c ≠ 0) :
    rho*hbar^2/4*(∑ mu, sign mu*pairedProductSum (bodyOmega A x (directions mu)) (bodyOmega A x (directions mu))) =
      rho*(∑ mu, sign mu*(spinCoefficient hbar (fun mu => bodyOmega A x (directions mu)) mu)^2) - rho*hbar^2/4*
        ((∑ mu, sign mu*minkowski (fwSpinDerivative c (fun y => frame (A y)) x (directions mu))
          (fwSpinDerivative c (fun y => frame (A y)) x (directions mu))) -
         (1/c^2)*(∑ mu, sign mu*minkowski
          (fderiv ℝ (fun y => velocity c (frame (A y))) x (directions mu))
          (fderiv ℝ (fun y => velocity c (frame (A y))) x (directions mu)))) := by
  exact VelocitySpinKinetic.mc_velocity_spin_identity (differentiableAt_spin_field hA)
    (spin_isUnit _ hdet.self_of_nhds) (differentiableAt_frame_entry hA)
    (eventual_frame_expansion hdet) directions (fun mu => bodyOmega A x (directions mu))
    (fun mu => bodyOmega_antisymmetric A x (directions mu))
    (fun mu => body_eq_generator hA hdet (directions mu)) rho hbar c hc

end FoliationQM.SpecialLinearPhysicalKinetic
