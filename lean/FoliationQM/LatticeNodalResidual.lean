module

public import FoliationQM.LatticeSchrodingerReconstruction

/-!
# Sharpness of the source regularization residual at a node

On two sites give the first amplitude value zero and the adjacent amplitude
value one, with equal phases. The complex residual at the empty site then has
the full kinetic scale for every positive regulator. A quarter-turn at that
same empty site leaves the wave unchanged and kills its radial stencil.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeNodalResidual

open LatticeSchrodingerResidual LatticeClockRegularization LatticePolarStencil
open LatticeComplexEnergy LatticeConservation PolarKahlerLattice

/-- A unit neighboring amplitude and a node at the first site. -/
def profile (i : Fin 2) : ℝ := if i = 0 then 0 else 1

/-- A freely chosen phase representative at the empty site, with zero phase at its neighbor. -/
def nodalAngle (a : ℝ) (i : Fin 2) : ℝ := if i = 0 then a else 0

/-- The raw complex profile is independent of the phase chosen at the node. -/
theorem wave_independent (a : ℝ) : wave profile (nodalAngle a) = wave profile (nodalAngle 0) := by
  funext i
  by_cases hi : i = 0 <;> simp [wave, nodalAngle, profile, hi]

/-- The nodal residual is the full kinetic scale multiplied by the radial
projection of the unit neighbor and the rotated local phase. -/
theorem residual_value (p : MassiveParameters) (h ε a : ℝ) (hε : ε ≠ 0) :
    residual p h ε profile (nodalAngle a) 0 =
      phase a * (-Complex.I) * Complex.ofReal ((p.ellC * p.c / (2*h^2)) * Real.cos a) := by
  have hn : nextNode (0 : Fin 2) = 1 := rfl
  have hp : prevNode (0 : Fin 2) = 0 := rfl
  simp [LatticeSchrodingerResidual.residual, defectFraction, radial, profile, nodalAngle, hn, hp, hε]

/-- Aligned phases realize the maximum residual magnitude at this node,
independent of the size of the nonzero regulator. -/
theorem aligned_residual_norm (p : MassiveParameters) (h : ℝ)
    (ε : ℝ) (hε : ε ≠ 0) :
    ‖residual p h ε profile (nodalAngle 0) 0‖ = p.ellC * p.c / (2*h^2) := by
  simp [residual_value p h ε 0 hε, phase, Complex.norm_real,
    abs_of_pos (ClockScales.ellC_pos p), abs_of_pos p.c_pos]

/-- A quarter-turn representative has zero residual at the same node of the same wave. -/
theorem quarter_turn_residual_zero (p : MassiveParameters) (h ε : ℝ) (hε : ε ≠ 0) :
    residual p h ε profile (nodalAngle (Real.pi/2)) 0 = 0 := by
  simp [residual_value p h ε _ hε, Real.cos_pi_div_two]

/-- A regularized solution with any prescribed nodal angle realizes the
corresponding residual in its actual initial wave derivative. -/
theorem realized_initial_rate (p : MassiveParameters) (h ε a : ℝ) (hε : 0 < ε)
    (V : Fin 2 → ℝ) :
    ∃ γ : ℝ → LatticeRegularizedFlow.State 2,
      (wave (γ 0).1 (LatticeLagHamiltonian.lagPhase p (γ 0).2) = wave profile (nodalAngle 0)) ∧
      (∃ δ > 0, ∀ t ∈ Set.Ioo (-δ) δ,
        HasDerivAt γ (LatticeRegularizedFlow.field p h ε V (γ t)) t) ∧
      HasDerivAt (fun t => wave (γ t).1 (LatticeLagHamiltonian.lagPhase p (γ t).2) 0)
        (schrodinger p h V (wave profile (nodalAngle 0)) 0 +
          phase a * (-Complex.I) * Complex.ofReal ((p.ellC * p.c / (2*h^2)) * Real.cos a)) 0 := by
  let τ (i : Fin 2) := (p.ellC / p.c) * nodalAngle a i
  have hp : LatticeLagHamiltonian.lagPhase p τ = nodalAngle a := by
    funext i
    unfold LatticeLagHamiltonian.lagPhase τ
    field_simp [(ClockScales.ellC_pos p).ne', p.c_pos.ne']
  obtain ⟨γ, hinit, δ, hδ, hsol⟩ :=
    LatticeRegularizedFlow.exists_solution p h hε V (profile, τ) 0
  have hsol' (t : ℝ) (ht : t ∈ Set.Ioo (-δ) δ) :=
    (hsol t (by simpa only [zero_sub, zero_add] using ht)).1
  have hd := LatticeSchrodingerReconstruction.wave_path_with_residual p h ε V γ 0
    (fun _ => Or.inr hε.ne') (hsol' 0 ⟨neg_lt_zero.mpr hδ, hδ⟩)
  refine ⟨γ, ?_, ⟨δ, hδ, hsol'⟩, ?_⟩
  · simpa only [hinit, hp] using wave_independent a
  · have h0 := hasDerivAt_pi.mp hd (0 : Fin 2)
    simpa only [hinit, hp, wave_independent a, Pi.add_apply, residual_value p h ε a hε.ne'] using h0

end FoliationQM.LatticeNodalResidual
