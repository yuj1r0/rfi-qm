module

public import FoliationQM.CurvedCoordinateDynamics
public import FoliationQM.CurvedCoordinateTime

/-!
# Actual spatial trajectories in coordinate time

A local proper-parameter integral curve with positive time component is
reparameterized by its genuine coordinate-time inverse. Its spatial part
has the actual second derivative G+f. Both the spacetime position (ct,X)
and the velocity (c,dX/dt) are reconstructed from the curve, so the
Christoffel field is evaluated at the actual coordinate data.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCoordinateTrajectories

open LorentzMatrixGroup CurvedCoordinateVelocity CurvedCoordinateDynamics CurvedCoordinateTime
open scoped Topology Matrix.Norms.Operator

/-- The spacetime chart point formed from coordinate time and three spatial coordinates. -/
def coordinatePoint (c t : ℝ) (X : Fin 3 → ℝ) : Covector := Fin.cons (c * t) X

/-- The full coordinate velocity formed from the constant temporal component and the actual spatial velocity. -/
def spacetimeVelocity (c : ℝ) (b : Fin 3 → ℝ) : Covector := Fin.cons c b

/-- The source coordinate geodesic field evaluated at the actual spacetime position and spatial velocity. -/
def coordinateGeodesic (c : ℝ) (g : Covector → Mat4) (t : ℝ) (X b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  spatialPart (geodesicAcceleration c g (coordinatePoint c t X) (spacetimeVelocity c b))

/-- The actual time component and spatial projection reconstruct the full spacetime chart point. -/
theorem reconstruct_position (c t : ℝ) (z : Covector) (hz : z 0 = c * t) :
    z = coordinatePoint c t (spatialPart z) := by
  ext r
  refine Fin.cases ?_ (fun i => ?_) r
  · exact hz
  · rfl

/-- The proved constant time component reconstructs the full rescaled velocity from its three spatial components. -/
theorem reconstruct_velocity (c : ℝ) (U : Covector → Covector) (x : Covector)
    (h0 : U x 0 ≠ 0) :
    coordinateVelocity c U x = spacetimeVelocity c (spatialPart (coordinateVelocity c U x)) := by
  ext r
  refine Fin.cases ?_ (fun i => ?_) r
  · exact time_component c h0
  · rfl

variable {U : Covector → Covector} {γ : ℝ → Covector} {t : ℝ}

/-- Projecting a genuine coordinate-time trajectory gives its actual spatial second derivative G(t,X,dX/dt)+f. -/
theorem spatial_trajectory_acceleration (c : ℝ) (hc : c ≠ 0) (g : Covector → Mat4)
    (hU : DifferentiableAt ℝ U (γ t)) (h0 : U (γ t) 0 ≠ 0)
    (hODE : ∀ᶠ s in 𝓝 t, HasDerivAt γ (coordinateVelocity c U (γ s)) s)
    (htime : γ t 0 = c * t) :
    HasDerivAt (deriv (spatialPart ∘ γ))
      (coordinateGeodesic c g t (spatialPart (γ t)) (deriv (spatialPart ∘ γ) t) +
        spatialPart (coordinateForce c g U (γ t))) t := by
  have hsp := spatialPart.hasFDerivAt.comp_hasDerivAt t hODE.self_of_nhds
  have he : deriv (spatialPart ∘ γ) =ᶠ[𝓝 t] spatialPart ∘ deriv γ := by
    filter_upwards [hODE] with s hs
    change deriv (spatialPart ∘ γ) s = spatialPart (deriv γ s)
    rw [(spatialPart.hasFDerivAt.comp_hasDerivAt s hs).deriv, hs.deriv]
  have H := spatialPart.hasFDerivAt.comp_hasDerivAt t
    (trajectory_acceleration c hc g hU h0 hODE)
  rw [map_add] at H
  rw [coordinateGeodesic, hsp.deriv, ← reconstruct_position c t (γ t) htime,
    ← reconstruct_velocity c U (γ t) h0]
  exact H.congr_of_eventuallyEq he

variable {τ₀ : ℝ}

/-- An actual positive-time proper-parameter curve admits a genuine local inverse whose spatial trajectory obeys the source coordinate geodesic equation with the actual projected force. -/
theorem exists_coordinate_dynamics {c : ℝ} (hc : 0 < c) (g : Covector → Mat4)
    (hγ : ContDiffAt ℝ 1 γ τ₀) (hODE : ∀ᶠ τ in 𝓝 τ₀, HasDerivAt γ (U (γ τ)) τ)
    (hU0 : 0 < U (γ τ₀) 0) (hU : DifferentiableAt ℝ U (γ τ₀)) :
    let t₀ := coordinateTime c γ τ₀
    ∃ κ : ℝ → ℝ,
      κ t₀ = τ₀ ∧
      (∀ᶠ τ in 𝓝 τ₀, κ (coordinateTime c γ τ) = τ) ∧
      (∀ᶠ t in 𝓝 t₀, coordinateTime c γ (κ t) = t) ∧
      (∀ᶠ t in 𝓝 t₀, γ (κ t) 0 = c * t) ∧
      (∀ᶠ t in 𝓝 t₀, HasDerivAt (γ ∘ κ) (coordinateVelocity c U (γ (κ t))) t) ∧
      HasDerivAt (spatialPart ∘ (γ ∘ κ))
        (spatialPart (coordinateVelocity c U (γ τ₀))) t₀ ∧
      HasDerivAt (deriv (spatialPart ∘ (γ ∘ κ)))
        (coordinateGeodesic c g t₀ (spatialPart (γ τ₀))
          (spatialPart (coordinateVelocity c U (γ τ₀))) +
          spatialPart (coordinateForce c g U (γ τ₀))) t₀ := by
  dsimp only
  obtain ⟨κ, hκ, hleft, hright, _, hvel, hnear, htime⟩ :=
    exists_local_reparametrization hc hγ hODE hU0
  have hn : ∀ᶠ t in 𝓝 (coordinateTime c γ τ₀),
      HasDerivAt (γ ∘ κ) (coordinateVelocity c U ((γ ∘ κ) t)) t := hnear
  have hvalue : (γ ∘ κ) (coordinateTime c γ τ₀) = γ τ₀ := by
    simp only [Function.comp_apply, hκ]
  have hsp : HasDerivAt (spatialPart ∘ (γ ∘ κ))
      (spatialPart (coordinateVelocity c U (γ τ₀))) (coordinateTime c γ τ₀) :=
    spatialPart.hasFDerivAt.comp_hasDerivAt _ hvel
  have H := spatial_trajectory_acceleration c hc.ne' g
    (hvalue.symm ▸ hU) (hvalue.symm ▸ hU0.ne') hn htime.self_of_nhds
  rw [hvalue, hsp.deriv] at H
  exact ⟨κ, hκ, hleft, hright, htime, hn, hsp, H⟩

end FoliationQM.CurvedCoordinateTrajectories
