module

public import FoliationQM.LatticeLagHamiltonian
public import FoliationQM.LatticeClockRegularization
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Local solutions of the regularized polar lattice equations

The positive regulator makes the amplitude and lag-clock equations in v13
lines 215–220 a smooth real vector field through every signed state, including
nodes. Picard–Lindelöf gives a solution on an open interval about any specified
initial time. Its rectangular lattice mass is constant throughout that interval.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeRegularizedFlow

open LatticeConservation LatticeLagHamiltonian LatticeClockRegularization
open scoped ContDiff

/-- Signed amplitudes and real lag-clock coordinates of the finite lattice. -/
abbrev State (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

/-- The joint autonomous source field, in physical time and lag-clock coordinates. -/
def field {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (V : Fin n → ℝ)
    (x : State n) : State n :=
  (sourceAmplitudeRHS p.ellC p.c h x.1 (lagPhase p x.2),
    lagRate p h ε x.1 (lagPhase p x.2) V)

/-- A positive regulator gives a smooth field on the entire signed state space. -/
theorem field_smooth {n : ℕ} (p : MassiveParameters) (h : ℝ) {ε : ℝ} (hε : 0 < ε)
    (V : Fin n → ℝ) : ContDiff ℝ ∞ (field p h ε V) := by
  unfold field
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    unfold sourceAmplitudeRHS lagPhase
    fun_prop
  · apply contDiff_pi.mpr
    intro i
    have hr := reciprocal_smooth ε hε.ne'
    unfold lagRate LatticePolarStencil.radial lagPhase
    fun_prop

/-- Each site of a differentiable integral curve satisfies both source equations. -/
theorem component_rates {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (V : Fin n → ℝ)
    (γ : ℝ → State n) (t : ℝ) (hγ : HasDerivAt γ (field p h ε V (γ t)) t) :
    (∀ i, HasDerivAt (fun s => (γ s).1 i)
      (sourceAmplitudeRHS p.ellC p.c h (γ t).1 (lagPhase p (γ t).2) i) t) ∧
    (∀ i, HasDerivAt (fun s => (γ s).2 i)
      (lagRate p h ε (γ t).1 (lagPhase p (γ t).2) V i) t) := by
  constructor
  · apply hasDerivAt_pi.mp
    exact (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).hasFDerivAt.comp_hasDerivAt t hγ
  · apply hasDerivAt_pi.mp
    exact (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).hasFDerivAt.comp_hasDerivAt t hγ

/-- The rectangular mass has zero derivative wherever the curve satisfies the field. -/
theorem mass_path {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (V : Fin n → ℝ)
    (γ : ℝ → State n) (t : ℝ) (hγ : HasDerivAt γ (field p h ε V (γ t)) t) :
    HasDerivAt (fun s => sourceMass h (γ s).1) 0 t :=
  hasDerivAt_sourceMass_zero p.ellC p.c h (fun s => (γ s).1) (fun s => lagPhase p (γ s).2) t
    (component_rates p h ε V γ t hγ).1

/-- For arbitrary signed initial amplitudes and lag clocks, a positive regulator gives a
local solution of the joint lattice ODE that conserves rectangular mass on its interval. -/
theorem exists_solution {n : ℕ} (p : MassiveParameters) (h : ℝ) {ε : ℝ} (hε : 0 < ε)
    (V : Fin n → ℝ) (x₀ : State n) (t₀ : ℝ) :
    ∃ γ : ℝ → State n, γ t₀ = x₀ ∧ ∃ δ > 0, ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
      HasDerivAt γ (field p h ε V (γ t)) t ∧ sourceMass h (γ t).1 = sourceMass h x₀.1 := by
  have hs : ContDiffAt ℝ 1 (field p h ε V) x₀ :=
    ((field_smooth p h hε V).of_le (by simp)).contDiffAt
  obtain ⟨γ, hinit, δ, hδ, hode⟩ :=
    hs.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  have hm (s : ℝ) (hs : s ∈ Set.Ioo (t₀ - δ) (t₀ + δ)) :=
    mass_path p h ε V γ s (hode s hs)
  refine ⟨γ, hinit, δ, hδ, fun t ht => ⟨hode t ht, ?_⟩⟩
  rw [← hinit]
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun s hs => (hm s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hm s hs).deriv) ht ⟨by linarith, by linarith⟩

end FoliationQM.LatticeRegularizedFlow
