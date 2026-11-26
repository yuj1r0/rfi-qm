module

public import FoliationQM.CurvedCoordinateQuantumForce
public import FoliationQM.CurvedCoordinateTrajectories

/-!
# Actual quantum coordinate trajectories and their full spacetime force

The coordinate-time trajectory and its second derivative are genuine
curves and derivatives. Substituting the proved KG force into the actual
coordinate projection gives the exact defect-gradient forcing term.
The proper-parameter version retains the actual local inverse and both
inverse germs. Global flow existence and probability transport are separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedQuantumTrajectories

open LorentzMatrixGroup CurvedCoordinateVelocity CurvedCoordinateDynamics
  CurvedCoordinateTime CurvedCoordinateTrajectories CurvedNormalizedQuantumForce
  CurvedScalarGradient CurvedPolarKG CurvedKGTestResidual PolarSecondDifferential
open scoped Topology Matrix.Norms.Operator

variable {g : Covector → Mat4} {R S : Covector → ℝ} {γ : ℝ → Covector} {t τ₀ : ℝ}

/-- An actual coordinate-time integral curve of the normalized KG velocity has the genuine spatial acceleration with the exact projected full-spacetime defect gradient. -/
theorem spatial_quantum_acceleration (p : MassiveParameters)
    (hg : ContDiffAt ℝ 2 g (γ t)) (hd : (g (γ t)).det < 0)
    (hs : ∀ᶠ y in 𝓝 (γ t), (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R (γ t)) (hS : ContDiffAt ℝ 2 S (γ t)) (hp : 0 < R (γ t))
    (hKG : ∀ᶠ y in 𝓝 (γ t), kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hq : 0 < 1 + defect p g R (γ t))
    (h0 : normalizedVelocity p g R S (γ t) 0 ≠ 0)
    (hODE : ∀ᶠ s in 𝓝 t,
      HasDerivAt γ (coordinateVelocity p.c (normalizedVelocity p g R S) (γ s)) s)
    (htime : γ t 0 = p.c * t) :
    let U := normalizedVelocity p g R S
    let q := defect p g R
    HasDerivAt (deriv (spatialPart ∘ γ))
      (coordinateGeodesic p.c g t (spatialPart (γ t)) (deriv (spatialPart ∘ γ) t) +
        spatialPart ((p.c ^ 4 / (2 * (U (γ t) 0) ^ 2 * (1 + q (γ t)))) •
          (grad g q (γ t) - (grad g q (γ t) 0 / U (γ t) 0) • U (γ t)))) t := by
  dsimp only
  have hU := (contDiffAt_normalizedVelocity p hg hd hs hR hS hp hKG hq).differentiableAt_one
  have H := spatial_trajectory_acceleration p.c p.c_pos.ne' g hU h0 hODE htime
  rw [CurvedCoordinateQuantumForce.coordinate_force p hg hd hs hR hS hp hKG hq h0] at H
  exact H

/-- A supplied positive-time proper-parameter KG trajectory has a genuinely constructed local coordinate-time inverse whose spatial second derivative carries the exact quantum gradient force. -/
theorem exists_quantum_coordinate_dynamics (p : MassiveParameters)
    (hg : ContDiffAt ℝ 2 g (γ τ₀)) (hd : (g (γ τ₀)).det < 0)
    (hs : ∀ᶠ y in 𝓝 (γ τ₀), (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R (γ τ₀)) (hS : ContDiffAt ℝ 2 S (γ τ₀)) (hp : 0 < R (γ τ₀))
    (hKG : ∀ᶠ y in 𝓝 (γ τ₀), kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hq : 0 < 1 + defect p g R (γ τ₀)) (hγ : ContDiffAt ℝ 1 γ τ₀)
    (hODE : ∀ᶠ τ in 𝓝 τ₀, HasDerivAt γ (normalizedVelocity p g R S (γ τ)) τ)
    (hU0 : 0 < normalizedVelocity p g R S (γ τ₀) 0) :
    let U := normalizedVelocity p g R S
    let q := defect p g R
    let t₀ := coordinateTime p.c γ τ₀
    ∃ κ : ℝ → ℝ,
      κ t₀ = τ₀ ∧
      (∀ᶠ τ in 𝓝 τ₀, κ (coordinateTime p.c γ τ) = τ) ∧
      (∀ᶠ t in 𝓝 t₀, coordinateTime p.c γ (κ t) = t) ∧
      (∀ᶠ t in 𝓝 t₀, γ (κ t) 0 = p.c * t) ∧
      (∀ᶠ t in 𝓝 t₀, HasDerivAt (γ ∘ κ) (coordinateVelocity p.c U (γ (κ t))) t) ∧
      HasDerivAt (spatialPart ∘ (γ ∘ κ))
        (spatialPart (coordinateVelocity p.c U (γ τ₀))) t₀ ∧
      HasDerivAt (deriv (spatialPart ∘ (γ ∘ κ)))
        (coordinateGeodesic p.c g t₀ (spatialPart (γ τ₀))
          (spatialPart (coordinateVelocity p.c U (γ τ₀))) +
          spatialPart ((p.c ^ 4 / (2 * (U (γ τ₀) 0) ^ 2 * (1 + q (γ τ₀)))) •
            (grad g q (γ τ₀) - (grad g q (γ τ₀) 0 / U (γ τ₀) 0) • U (γ τ₀)))) t₀ := by
  dsimp only
  have hU := (contDiffAt_normalizedVelocity p hg hd hs hR hS hp hKG hq).differentiableAt_one
  obtain ⟨κ, hκ, hleft, hright, htime, hnear, hvel, hacc⟩ :=
    exists_coordinate_dynamics p.c_pos g hγ hODE hU0 hU
  rw [CurvedCoordinateQuantumForce.coordinate_force p hg hd hs hR hS hp hKG hq hU0.ne'] at hacc
  exact ⟨κ, hκ, hleft, hright, htime, hnear, hvel, hacc⟩

end FoliationQM.CurvedQuantumTrajectories
