module

public import FoliationQM.PhysicalFrameDifferential
public import FoliationQM.FermiWalkerProjection
public import FoliationQM.CanonicalDiracContraction
public import FoliationQM.SixTermConnection

/-!
# Actual velocity and projected spin derivative decomposition

Source: v13 `eq:mc_velocity_spin_identity`, using the actual lower-gamma
physical frame. The genuine Frechet derivatives are derived from a local
real matrix-frame expansion and actual antisymmetric body-generator
coefficients. Their Minkowski norms are computed after the actual
Fermi--Walker projection; no derivative or kinetic conclusion is a premise.

The dimensionless identity is proved first. The source physical-velocity
identity then has the explicit nonzero-c domain, and the four spacetime
directions carry the (+---) metric weights. The spin coefficient is the
same negative half-hbar coefficient used in CanonicalDiracContraction,
which already identifies it with the scalar spin-connection field.
The two-index coefficient-lowering invariance is explicit. These are local
first-derivative kinematic identities, with no variational or phase claim.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.VelocitySpinKinetic
open DiracMatrices RealLorentzFrame PolarVectorGeometry PhysicalFrameDifferential
open FermiWalkerProjection SixTermConnection CanonicalDiracContraction
open MaurerCartanDifferential CliffordCommutators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual spin-field directional derivative projected orthogonally to the actual physical velocity. -/
def fwSpinDerivative (c : ℝ) (u : E → Fin 4 → Covector) (x v : E) : Covector :=
  projection c (velocity c (u x)) (fderiv ℝ (fun y => spinVector (u y)) x v)

/-- The actual physical Fermi--Walker projection equals the dimensionless time-vector projection when c is nonzero. -/
theorem fwSpinDerivative_eq_normalized (c : ℝ) (hc : c ≠ 0)
    (u : E → Fin 4 → Covector) (x v : E) :
    fwSpinDerivative c u x v = normalizedProjection (timeVector (u x))
      (fderiv ℝ (fun y => spinVector (u y)) x v) := by
  change projection c (c • timeVector (u x)) _ = _
  exact projection_scaled c hc _ _

/-- Raising or lowering both stored Lorentz-coefficient indices leaves the six-pair square unchanged. -/
theorem pairedProductSum_sourceOmega (omega : Fin 4 → Fin 4 → ℝ) :
    pairedProductSum (RicciRotation.sourceOmega omega) (RicciRotation.sourceOmega omega) =
      pairedProductSum omega omega := by
  simp [pairedProductSum_eq_six_terms, RicciRotation.sourceOmega, sign]

/-- The actual dimensionless time-vector derivative has the negative sum of the three squared boost coefficients. -/
theorem time_derivative_squared {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) :
    minkowski (fderiv ℝ (fun y => timeVector (u y)) x v)
      (fderiv ℝ (fun y => timeVector (u y)) x v) =
      -((omega 0 1)^2+(omega 0 2)^2+(omega 0 3)^2) := by
  rw [fderiv_timeVector hL hunit hu hframe v omega hanti hbody]
  exact timeJet_squared (physicalFrame (u x))
    (physicalFrame_orthonormal hunit hframe.self_of_nhds) _ _ _

/-- The normalized projection of the actual spin derivative has exactly the two negative squared transverse rotation coefficients. -/
theorem normalized_spin_derivative_squared {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) :
    minkowski
      (normalizedProjection (timeVector (u x)) (fderiv ℝ (fun y => spinVector (u y)) x v))
      (normalizedProjection (timeVector (u x)) (fderiv ℝ (fun y => spinVector (u y)) x v)) =
      -((omega 1 3)^2+(omega 2 3)^2) := by
  rw [fderiv_spinVector hL hunit hu hframe v omega hanti hbody,
    ← physicalFrame_zero_eq_timeVector (u x)]
  exact normalizedProjection_spinJet_squared (physicalFrame (u x))
    (physicalFrame_orthonormal hunit hframe.self_of_nhds) _ _ _

/-- The dimensionless source identity follows from the actual time and normalized projected-spin derivative norms. -/
theorem mc_time_spin_identity {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) :
    pairedProductSum omega omega = (omega 1 2)^2 -
      (minkowski
        (normalizedProjection (timeVector (u x)) (fderiv ℝ (fun y => spinVector (u y)) x v))
        (normalizedProjection (timeVector (u x)) (fderiv ℝ (fun y => spinVector (u y)) x v)) -
       minkowski (fderiv ℝ (fun y => timeVector (u y)) x v)
         (fderiv ℝ (fun y => timeVector (u y)) x v)) := by
  rw [normalized_spin_derivative_squared hL hunit hu hframe v omega hanti hbody,
    time_derivative_squared hL hunit hu hframe v omega hanti hbody,
    pairedProductSum_eq_six_terms]
  ring

/-- The actual Fermi--Walker projected spin derivative has the source transverse rotation norm at every nonzero c. -/
theorem fwSpinDerivative_squared {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (c : ℝ) (hc : c ≠ 0) :
    minkowski (fwSpinDerivative c u x v) (fwSpinDerivative c u x v) =
      -((omega 1 3)^2+(omega 2 3)^2) := by
  rw [fwSpinDerivative_eq_normalized c hc]
  exact normalized_spin_derivative_squared hL hunit hu hframe v omega hanti hbody

/-- The actual physical velocity derivative norm divided by c squared equals the negative squared boost sum. -/
theorem velocity_derivative_squared_div {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (c : ℝ) (hc : c ≠ 0) :
    minkowski (fderiv ℝ (fun y => velocity c (u y)) x v)
      (fderiv ℝ (fun y => velocity c (u y)) x v) / c^2 =
      -((omega 0 1)^2+(omega 0 2)^2+(omega 0 3)^2) := by
  rw [fderiv_velocity hL hunit hu hframe v omega hanti hbody c]
  exact physical_velocityJet_squared (physicalFrame (u x))
    (physicalFrame_orthonormal hunit hframe.self_of_nhds) c hc _ _ _

/-- The actual per-direction source identity decomposes the Lorentz six-pair square into spin rotation, projected spin derivative and physical velocity derivative. -/
theorem mc_velocity_spin_direction {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (c : ℝ) (hc : c ≠ 0) :
    pairedProductSum omega omega = (omega 1 2)^2 -
      (minkowski (fwSpinDerivative c u x v) (fwSpinDerivative c u x v) -
        (1/c^2)*minkowski (fderiv ℝ (fun y => velocity c (u y)) x v)
          (fderiv ℝ (fun y => velocity c (u y)) x v)) := by
  have hv : (1/c^2)*minkowski (fderiv ℝ (fun y => velocity c (u y)) x v)
      (fderiv ℝ (fun y => velocity c (u y)) x v) =
      -((omega 0 1)^2+(omega 0 2)^2+(omega 0 3)^2) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      velocity_derivative_squared_div hL hunit hu hframe v omega hanti hbody c hc
  rw [fwSpinDerivative_squared hL hunit hu hframe v omega hanti hbody c hc,
    hv, pairedProductSum_eq_six_terms]
  ring

private theorem weighted_identity (rho hbar c : ℝ) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (fw vel : Fin 4 → ℝ)
    (h : ∀ mu, pairedProductSum (omega mu) (omega mu) =
      (omega mu 1 2)^2 - (fw mu - (1/c^2)*vel mu)) :
    rho*hbar^2/4*(∑ mu, sign mu*pairedProductSum (omega mu) (omega mu)) =
      rho*(∑ mu, sign mu*(spinCoefficient hbar omega mu)^2) -
        rho*hbar^2/4*((∑ mu, sign mu*fw mu) - (1/c^2)*(∑ mu, sign mu*vel mu)) := by
  calc
    _ = ∑ mu, rho*hbar^2/4*(sign mu*pairedProductSum (omega mu) (omega mu)) := by
      rw [Finset.mul_sum]
    _ = ∑ mu, (rho*(sign mu*(spinCoefficient hbar omega mu)^2) -
        rho*hbar^2/4*(sign mu*fw mu - (1/c^2)*(sign mu*vel mu))) := by
      apply Finset.sum_congr rfl
      intro mu _
      rw [h mu]
      simp only [spinCoefficient]
      ring
    _ = _ := by simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The exact source velocity-spin identity holds for the actual four directional derivatives, with the diagonal spacetime metric, actual Fermi--Walker projection and established spin coefficient. -/
theorem mc_velocity_spin_identity {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (directions : Fin 4 → E) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ mu a b, omega mu a b = -omega mu b a)
    (hbody : ∀ mu, body L x (directions mu)=generator (omega mu))
    (rho hbar c : ℝ) (hc : c ≠ 0) :
    rho*hbar^2/4*(∑ mu, sign mu*pairedProductSum (omega mu) (omega mu)) =
      rho*(∑ mu, sign mu*(spinCoefficient hbar omega mu)^2) - rho*hbar^2/4*
        ((∑ mu, sign mu*minkowski (fwSpinDerivative c u x (directions mu))
          (fwSpinDerivative c u x (directions mu))) -
         (1/c^2)*(∑ mu, sign mu*minkowski
          (fderiv ℝ (fun y => velocity c (u y)) x (directions mu))
          (fderiv ℝ (fun y => velocity c (u y)) x (directions mu)))) := by
  apply weighted_identity
  intro mu
  exact mc_velocity_spin_direction hL hunit hu hframe (directions mu) (omega mu)
    (hanti mu) (hbody mu) c hc

end FoliationQM.VelocitySpinKinetic
