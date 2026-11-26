module

public import FoliationQM.CurvedNormalizedQuantumForce
public import FoliationQM.CurvedForceProjection

/-!
# The actual coordinate quantum force of a curved KG solution

The normalized velocity and proper acceleration come from the genuine
positive polar KG solution. Converting that acceleration to coordinate
time cancels its component parallel to the velocity. The resulting force
is the full spacetime derivative projection printed after v13's
coordinate-force equation, including the temporal and off-diagonal metric
terms. The coordinate equation uses the actual self-derivative of the
rescaled velocity, with no supplied force or independent derivative jet.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCoordinateQuantumForce

open LorentzMatrixGroup RNCCoordinateConnection CurvedGradientCovariance CurvedScalarGradient
  CurvedNormalizedQuantumForce CurvedPolarKG CurvedKGTestResidual PolarSecondDifferential
  CurvedCoordinateVelocity CurvedCoordinateDynamics
open scoped Topology Matrix.Norms.Operator

variable {g : Covector → Mat4} {R S : Covector → ℝ} {x : Covector}

/-- The actual coordinate projection of the normalized KG acceleration equals the raised mass-defect gradient with its temporal velocity component removed. -/
theorem coordinate_force (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hRpos : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hqpos : 0 < 1 + defect p g R x) (h0 : normalizedVelocity p g R S x 0 ≠ 0) :
    coordinateForce p.c g (normalizedVelocity p g R S) x =
      (p.c ^ 4 / (2 * (normalizedVelocity p g R S x 0) ^ 2 * (1 + defect p g R x))) •
        (grad g (defect p g R) x -
          (grad g (defect p g R) x 0 / normalizedVelocity p g R S x 0) •
            normalizedVelocity p g R S x) := by
  unfold coordinateForce
  rw [normalized_force p hg hd hs hR hS hRpos hKG hqpos]
  exact CurvedForceProjection.forceProjection_projected_log p.c g (normalizedVelocity p g R S)
    (CurvedMassDefectRegularity.differentiableAt_defect p hg hd hs hR hS hRpos hKG) hqpos h0

/-- Every actual coordinate-force component is the complete four-index derivative contraction from the source, with all temporal and mixed metric contributions retained. -/
theorem coordinate_force_components (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hRpos : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hqpos : 0 < 1 + defect p g R x) (h0 : normalizedVelocity p g R S x 0 ≠ 0)
    (r : Fin 4) :
    coordinateForce p.c g (normalizedVelocity p g R S) x r =
      p.c ^ 4 / (2 * (normalizedVelocity p g R S x 0) ^ 2 * (1 + defect p g R x)) *
        ∑ b, ((g x)⁻¹ r b - normalizedVelocity p g R S x r /
          normalizedVelocity p g R S x 0 * (g x)⁻¹ 0 b) *
            fderiv ℝ (defect p g R) x (axis b) := by
  rw [coordinate_force p hg hd hs hR hS hRpos hKG hqpos h0]
  change _ * ((grad g (defect p g R) x -
    (grad g (defect p g R) x 0 / normalizedVelocity p g R S x 0) •
      normalizedVelocity p g R S x) r) = _
  congr 1
  exact CurvedForceProjection.mulVec_sub_components (normalizedVelocity p g R S x)
    (g x)⁻¹ (CurvedGradientCovariance.components (defect p g R) x) r

/-- The three spatial components of the actual coordinate quantum force satisfy the printed source projection formula. -/
theorem coordinate_force_spatial (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hRpos : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hqpos : 0 < 1 + defect p g R x) (h0 : normalizedVelocity p g R S x 0 ≠ 0)
    (i : Fin 3) :
    spatialPart (coordinateForce p.c g (normalizedVelocity p g R S) x) i =
      p.c ^ 4 / (2 * (normalizedVelocity p g R S x 0) ^ 2 * (1 + defect p g R x)) *
        ∑ b, ((g x)⁻¹ i.succ b - normalizedVelocity p g R S x i.succ /
          normalizedVelocity p g R S x 0 * (g x)⁻¹ 0 b) *
            fderiv ℝ (defect p g R) x (axis b) :=
  coordinate_force_components p hg hd hs hR hS hRpos hKG hqpos h0 i.succ

/-- The actual coordinate-time velocity of a positive polar KG solution obeys the geodesic equation plus the computed full spacetime quantum-gradient force. -/
theorem coordinate_equation (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hRpos : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hqpos : 0 < 1 + defect p g R x) (h0 : normalizedVelocity p g R S x 0 ≠ 0) :
    fderiv ℝ (coordinateVelocity p.c (normalizedVelocity p g R S)) x
      (coordinateVelocity p.c (normalizedVelocity p g R S) x) =
        geodesicAcceleration p.c g x (coordinateVelocity p.c (normalizedVelocity p g R S) x) +
          (p.c ^ 4 / (2 * (normalizedVelocity p g R S x 0) ^ 2 * (1 + defect p g R x))) •
            (grad g (defect p g R) x -
              (grad g (defect p g R) x 0 / normalizedVelocity p g R S x 0) •
                normalizedVelocity p g R S x) := by
  have hU := (contDiffAt_normalizedVelocity p hg hd hs hR hS hRpos hKG hqpos).differentiableAt_one
  rw [CurvedCoordinateDynamics.coordinate_equation p.c p.c_pos.ne' g hU h0,
    coordinate_force p hg hd hs hR hS hRpos hKG hqpos h0]

end FoliationQM.CurvedCoordinateQuantumForce
