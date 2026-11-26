module

public import FoliationQM.FlowDensityConservation
public import FoliationQM.CurvedCoordinateCurrent

/-!
# Actual polar-current density along a supplied smooth flow

The actual Klein–Gordon coordinate density and normalized velocity satisfy
the spatial-slice continuity equation by a genuine joint-to-slice chain
rule. A supplied smooth flow with actual local inverse and initial germs
therefore obeys the absolute-Jacobian density law, including both endpoints.
The phase is the supplied real phase on this polar domain.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedFlowDensityConservation

open LorentzMatrixGroup CurvedPolarKG CurvedQuantumForceBound CurvedCoordinateCurrent
  CurvedNormalizedQuantumForce SpatialFlowJacobian Set Filter
open scoped Topology BigOperators Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {t T : ℝ} {x a : Fin 3 → ℝ} {Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)}

/-- The actual joint current continuity equation restricts to the genuine spatial-slice derivatives. -/
theorem continuity_equation_spatial_slice
    (h : RegularPolarAt p g R S (eventMap p.c (t, x)))
    (hq : 0 < 1 + defect p g R (eventMap p.c (t, x)))
    (h0 : normalizedVelocity p g R S (eventMap p.c (t, x)) 0 ≠ 0) :
    fderiv ℝ (density p g R S) (t, x) (1, 0) +
      ∑ i : Fin 3, fderiv ℝ
        (fun y => density p g R S (t, y) * spatialVelocity p g R S (t, y) i)
        x (Pi.single i 1) = 0 := by
  have hD := (contDiffAt_density h).differentiableAt_one
  have hb := (contDiffAt_spatialVelocity h hq h0).differentiableAt_one
  have he (i : Fin 3) :
      fderiv ℝ (fun y => density p g R S (t, y) * spatialVelocity p g R S (t, y) i)
          x (Pi.single i 1) =
        fderiv ℝ (fun q => density p g R S q * spatialVelocity p g R S q i)
          (t, x) (0, Pi.single i 1) := by
    have hbi := (hasFDerivAt_pi'.mp hb.hasFDerivAt i).differentiableAt
    exact FlowDensityConservation.fderiv_spatial_slice (hD.mul hbi) (Pi.single i 1)
  simp_rw [he]
  exact continuity_equation h hq h0

/-- Actual polar regularity, the genuine flow ODE and real inverse germs yield current-density conservation. -/
theorem density_mul_abs_det_eq_initial (hT : 0 ≤ T)
    (hPhi : ∀ s ∈ Icc 0 T, ContDiffAt ℝ 2 Phi (s, a))
    (hreg : ∀ s ∈ Icc 0 T, RegularPolarAt p g R S (eventMap p.c (s, Phi (s, a))))
    (hq : ∀ s ∈ Icc 0 T, 0 < 1 + defect p g R (eventMap p.c (s, Phi (s, a))))
    (h0 : ∀ s ∈ Icc 0 T,
      normalizedVelocity p g R S (eventMap p.c (s, Phi (s, a))) 0 ≠ 0)
    (hODE : ∀ s ∈ Ioo 0 T, ∀ᶠ z in 𝓝 a,
      HasDerivAt (fun τ => Phi (τ, z)) (spatialVelocity p g R S (s, Phi (s, z))) s)
    (hinv : ∀ s ∈ Icc 0 T, ∃ ψ : (Fin 3 → ℝ) → (Fin 3 → ℝ),
      DifferentiableAt ℝ ψ (Phi (s, a)) ∧ (fun z => ψ (Phi (s, z))) =ᶠ[𝓝 a] id)
    (hzero : (fun z => Phi (0, z)) =ᶠ[𝓝 a] id) :
    ∀ t ∈ Icc 0 T, density p g R S (t, Phi (t, a)) *
      |spatialJacobianDet Phi (t, a)| = density p g R S (0, a) := by
  apply FlowDensityConservation.density_mul_abs_det_eq_initial
    (b := fun s y => spatialVelocity p g R S (s, y)) hT hPhi
  · intro s hs
    exact (contDiffAt_density (hreg s hs)).differentiableAt_one
  · intro s hs
    have hc : (s ∈ Icc 0 T) := ⟨hs.1.le, hs.2.le⟩
    have hb := (contDiffAt_spatialVelocity (hreg s hc) (hq s hc) (h0 s hc)).differentiableAt_one
    simpa only [Function.comp_def] using!
      (hb.hasFDerivAt.comp (Phi (s, a))
        (hasFDerivAt_prodMk_right s (Phi (s, a)))).differentiableAt
  · exact hODE
  · exact hinv
  · exact hzero
  · intro s hs
    have hc : (s ∈ Icc 0 T) := ⟨hs.1.le, hs.2.le⟩
    exact continuity_equation_spatial_slice (hreg s hc) (hq s hc) (h0 s hc)

end FoliationQM.CurvedFlowDensityConservation
