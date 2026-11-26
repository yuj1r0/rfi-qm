module

public import FoliationQM.CurvedCoordinateVelocity

/-!
# Genuine coordinate-time acceleration and the geodesic perturbation

For x⁰=ct the actual rescaled velocity is B=(c/U⁰)U. Its derivative
along itself splits into the coordinate geodesic acceleration and the
projection of the actual proper acceleration. The Christoffel expression
is derived from the computed Koszul connection. A trajectory satisfying
the coordinate first-order equation on a neighborhood consequently has
the stated actual second derivative.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCoordinateDynamics

open LorentzMatrixGroup CurvedScalarAtlasOverlap CurvedCovariantDerivative
  CurvedCoordinateVelocity RNCCoordinateConnection
open scoped Topology Matrix.Norms.Operator

/-- The continuous linear projection to the three spatial coordinate components. -/
def spatialPart : Covector →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

/-- The full coordinate-time projection of a supplied proper acceleration at a velocity. -/
def forceProjection (c : ℝ) (u a : Covector) : Covector :=
  (c ^ 2 / (u 0) ^ 2) • (a - (a 0 / u 0) • u)

/-- The coordinate force formed from the actual Koszul covariant acceleration of a vector field. -/
def coordinateForce (c : ℝ) (g : Covector → Mat4) (U : Covector → Covector)
    (x : Covector) : Covector :=
  forceProjection c (U x) (acceleration g U x)

/-- The geodesic coordinate acceleration at a full coordinate velocity with time component c. -/
def geodesicAcceleration (c : ℝ) (g : Covector → Mat4) (x z : Covector) : Covector :=
  -connection g x z z + (connection g x z z 0 / c) • z

/-- Each projected force component is exactly the proper-to-coordinate-time source expression. -/
theorem forceProjection_components (c : ℝ) (u a : Covector) (r : Fin 4) :
    forceProjection c u a r = c ^ 2 / (u 0) ^ 2 * (a r - u r / u 0 * a 0) := by
  simp only [forceProjection, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The projected force has zero time component wherever the time parametrization is regular. -/
theorem forceProjection_time (c : ℝ) (u a : Covector) (h0 : u 0 ≠ 0) :
    forceProjection c u a 0 = 0 := by
  rw [forceProjection_components, div_self h0, one_mul, sub_self, mul_zero]

/-- Expanding the actual connection gives the full source Christoffel formula for the coordinate geodesic acceleration. -/
theorem geodesicAcceleration_components (c : ℝ) (g : Covector → Mat4)
    (x z : Covector) (r : Fin 4) :
    geodesicAcceleration c g x z r =
      -∑ a, ∑ b, (christoffel g x r a b - z r / c * christoffel g x 0 a b) * z a * z b := by
  simp only [geodesicAcceleration, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul, connection_components]
  simp only [Finset.sum_div, Finset.sum_mul, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A full coordinate velocity with time component c has zero time-component geodesic acceleration. -/
theorem geodesicAcceleration_time (c : ℝ) (g : Covector → Mat4) (x z : Covector)
    (hc : c ≠ 0) (hz : z 0 = c) :
    geodesicAcceleration c g x z 0 = 0 := by
  change -connection g x z z 0 + (connection g x z z 0 / c) * z 0 = 0
  rw [hz, div_mul_cancel₀ _ hc, neg_add_cancel]

variable {U : Covector → Covector} {x : Covector}

/-- Differentiating the actual coordinate velocity yields the geodesic term plus the projected genuine proper acceleration. -/
theorem coordinate_equation (c : ℝ) (hc : c ≠ 0) (g : Covector → Mat4)
    (hU : DifferentiableAt ℝ U x) (h0 : U x 0 ≠ 0) :
    fderiv ℝ (coordinateVelocity c U) x (coordinateVelocity c U x) =
      geodesicAcceleration c g x (coordinateVelocity c U x) + coordinateForce c g U x := by
  rw [self_derivative c hU h0]
  unfold geodesicAcceleration
  rw [connection_rescale g c U x]
  unfold coordinateForce forceProjection acceleration covDeriv coordinateVelocity
  ext r
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [h0, hc]
  ring

variable {γ : ℝ → Covector} {t : ℝ}

/-- A genuine coordinate-time integral curve has the actual second derivative prescribed by the perturbed geodesic equation. -/
theorem trajectory_acceleration (c : ℝ) (hc : c ≠ 0) (g : Covector → Mat4)
    (hU : DifferentiableAt ℝ U (γ t)) (h0 : U (γ t) 0 ≠ 0)
    (hODE : ∀ᶠ s in 𝓝 t, HasDerivAt γ (coordinateVelocity c U (γ s)) s) :
    HasDerivAt (deriv γ)
      (geodesicAcceleration c g (γ t) (coordinateVelocity c U (γ t)) +
        coordinateForce c g U (γ t)) t := by
  have hd : deriv γ =ᶠ[𝓝 t] coordinateVelocity c U ∘ γ :=
    hODE.mono fun _ hs => hs.deriv
  have H := (differentiableAt_coordinateVelocity c hU h0).hasFDerivAt.comp_hasDerivAt t
    hODE.self_of_nhds
  rw [coordinate_equation c hc g hU h0] at H
  exact H.congr_of_eventuallyEq hd

end FoliationQM.CurvedCoordinateDynamics
