module

public import FoliationQM.CurvedPolarAction

/-!
# Clock normalization of the curved master action

In v13 `eq:master_variational_equivalence`, the real action phase is
`S = −m c² τ_clock`. Dividing the entire curved action by `m² c²`
gives the eikonal, logarithmic Fisher and curvature coefficients. The
local inverse uses a real phase branch of the nonvanishing wave.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.CurvedClockNormalization

open LorentzMatrixGroup RNCCoordinateCurvature CurvedGradientCovariance
  RNCVolumeDensity CurvedPolarAction MeasureTheory

/-- The action phase associated with the synchronization clock. -/
def clockPhase {X : Type*} (p : MassiveParameters) (τ : X → ℝ) (x : X) : ℝ :=
  -(p.m * p.c ^ 2) * τ x

/-- Recover the real clock from a chosen local real phase. -/
def clockFromPhase {X : Type*} (p : MassiveParameters) (S : X → ℝ) (x : X) : ℝ :=
  S x / -(p.m * p.c ^ 2)

/-- Substituting the reconstructed clock recovers the supplied branch pointwise. -/
theorem clockPhase_fromPhase {X : Type*} (p : MassiveParameters) (S : X → ℝ) :
    clockPhase p (clockFromPhase p S) = S := by
  funext x
  unfold clockPhase clockFromPhase
  field_simp [p.m_pos.ne', p.c_pos.ne']

/-- The normalized density in the source's clock, logarithmic density and scalar curvature. -/
def normalizedClockDensity (p : MassiveParameters) (g : Covector → Mat4) (ρ τ : Covector → ℝ)
    (x : Covector) : ℝ :=
  ρ x * (p.c ^ 2 * pairing g τ τ x - 1 +
    p.ellC ^ 2 / 4 * pairing g (Real.log ∘ ρ) (Real.log ∘ ρ) x + p.ellC ^ 2 / 6 * scalar g x)

/-- Metric-volume integral of the normalized density-clock expression. -/
def normalizedClockAction (p : MassiveParameters) (g : Covector → Mat4) (ρ τ : Covector → ℝ)
    (U : Set Covector) : ℝ :=
  ∫ x in U, volumeFactor (g x) * normalizedClockDensity p g ρ τ x

variable {ρ τ : Covector → ℝ} {x : Covector} {U : Set Covector}

/-- Differentiating the actual clock phase scales both covector slots of its kinetic pairing. -/
theorem pairing_clockPhase (p : MassiveParameters) (g : Covector → Mat4)
    (hτ : DifferentiableAt ℝ τ x) :
    pairing g (clockPhase p τ) (clockPhase p τ) x = (p.m * p.c ^ 2) ^ 2 * pairing g τ τ x := by
  have he : components (clockPhase p τ) x = (-(p.m * p.c ^ 2)) • components τ x := by
    funext i
    exact congrArg (fun L : Covector →L[ℝ] ℝ => L (RNCCoordinateConnection.axis i))
      (hτ.hasFDerivAt.const_mul (-(p.m * p.c ^ 2))).fderiv
  simp only [pairing, he, map_smul, smul_apply, smul_eq_mul]
  ring

/-- Dividing the full curved phase density by the mass scale gives the normalized clock density. -/
theorem hydro_density_normalized (p : MassiveParameters) (g : Covector → Mat4) (ρ : Covector → ℝ)
    (hτ : DifferentiableAt ℝ τ x) :
    hydroDensity p g ρ (clockPhase p τ) x / (p.m ^ 2 * p.c ^ 2) = normalizedClockDensity p g ρ τ x := by
  rw [hydroDensity, pairing_clockPhase p g hτ, normalizedClockDensity, MassiveParameters.ellC]
  field_simp [p.m_pos.ne', p.c_pos.ne']

/-- The normalization holds for the actual metric-volume action on a measurable region. -/
theorem hydro_action_normalized (p : MassiveParameters) (g : Covector → Mat4) (ρ : Covector → ℝ)
    (hU : MeasurableSet U) (hτ : ∀ x ∈ U, DifferentiableAt ℝ τ x) :
    hydroAction p g ρ (clockPhase p τ) U / (p.m ^ 2 * p.c ^ 2) = normalizedClockAction p g ρ τ U := by
  rw [hydroAction, ← integral_div, normalizedClockAction]
  apply setIntegral_congr_fun hU
  intro z hz
  exact (mul_div_assoc _ _ _).trans
    (congrArg (volumeFactor (g z) * ·) (hydro_density_normalized p g ρ (hτ z hz)))

/-- Forward master-action normalization through the actual positive-density polar field. -/
theorem kg_action_normalized (p : MassiveParameters) (g : Covector → Mat4) (hU : MeasurableSet U)
    (hρ : ∀ x ∈ U, DifferentiableAt ℝ ρ x) (hτ : ∀ x ∈ U, DifferentiableAt ℝ τ x)
    (hp : ∀ x ∈ U, 0 < ρ x) :
    kgAction p g (ActionDensity.actionField p ρ (clockPhase p τ)) U / (p.m ^ 2 * p.c ^ 2) =
      normalizedClockAction p g ρ τ U := by
  rw [action_eq (S := clockPhase p τ) p g hU hρ (fun x hx => (hτ x hx).const_mul (-(p.m * p.c ^ 2))) hp]
  exact hydro_action_normalized p g ρ hU hτ

/-- Every nonzero wave has a local positive density and real clock of its differentiability class. -/
theorem local_clock_branch (p : MassiveParameters) {k : WithTop ℕ∞} {ψ : Covector → ℂ}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ k ψ U) (hx : x ∈ U) (hn : ψ x ≠ 0) :
    ∃ (V : Set Covector) (τ : Covector → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ k (fun z => Complex.normSq (ψ z)) V ∧ ContDiffOn ℝ k τ V ∧
      ∀ z ∈ V, 0 < Complex.normSq (ψ z) ∧
        ActionDensity.actionField p (fun y => Complex.normSq (ψ y)) (clockPhase p τ) z = ψ z := by
  obtain ⟨V, ho, hxV, hVU, hρ, hS, he⟩ := PolarLocalInverse.exists_local_polar_reconstruction p hU hψ hx hn
  refine ⟨V, clockFromPhase p _, ho, hxV, hVU, hρ, hS.div_const _, ?_⟩
  simpa only [clockPhase_fromPhase] using he

/-- In the reverse direction, the same local clock reconstructs the complex field and
matches its normalized curved action on every measurable subregion. -/
theorem local_clock_action (p : MassiveParameters) (g : Covector → Mat4) {ψ : Covector → ℂ}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ 1 ψ U) (hx : x ∈ U) (hn : ψ x ≠ 0) :
    ∃ (V : Set Covector) (τ : Covector → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ContDiffOn ℝ 1 τ V ∧
      (∀ z ∈ V, 0 < Complex.normSq (ψ z) ∧
        ActionDensity.actionField p (fun y => Complex.normSq (ψ y)) (clockPhase p τ) z = ψ z) ∧
      ∀ W : Set Covector, MeasurableSet W → W ⊆ V →
        kgAction p g ψ W / (p.m ^ 2 * p.c ^ 2) =
          normalizedClockAction p g (fun y => Complex.normSq (ψ y)) τ W := by
  obtain ⟨V, τ, ho, hxV, hVU, hρ, hτ, he⟩ := local_clock_branch p hU hψ hx hn
  refine ⟨V, τ, ho, hxV, hVU, hτ, he, fun W hW hw => ?_⟩
  rw [← kg_action_normalized p g hW (fun z hz => ((hρ z (hw hz)).contDiffAt
    (ho.mem_nhds (hw hz))).differentiableAt_one)
    (fun z hz => ((hτ z (hw hz)).contDiffAt (ho.mem_nhds (hw hz))).differentiableAt_one)
    (fun z hz => (he z (hw hz)).1)]
  apply congrArg (· / (p.m ^ 2 * p.c ^ 2))
  apply setIntegral_congr_fun hW
  intro z hz
  have hfield := Filter.eventually_of_mem (ho.mem_nhds (hw hz)) (fun y hy => (he y hy).2)
  exact congrArg (volumeFactor (g z) * ·) (kgDensity_congr p g hfield).symm

end FoliationQM.CurvedClockNormalization
