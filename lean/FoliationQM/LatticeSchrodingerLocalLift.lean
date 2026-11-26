module

public import FoliationQM.LatticeSchrodingerReconstruction
public import FoliationQM.LatticeRegularizedFlow
public import FoliationQM.PolarLocalInverse
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Local polar lifts of complex lattice trajectories

Around a time at which all complex amplitudes are nonzero, the modulus and an
anchored logarithm recover the signed-amplitude and lag coordinates in v13
Section 2 with positive amplitudes. Finitely many slit-plane neighborhoods
give a common open time interval on which the reconstructed coordinates solve
the unregularized polar lattice equations.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeSchrodingerLocalLift

open LatticeComplexEnergy LatticeLagHamiltonian LatticeRegularizedFlow
open LatticeSchrodingerResidual LatticeSchrodingerReconstruction PolarLocalInverse
open scoped Topology

/-- At each site the modulus and the action relative to its complex anchor give
an amplitude and a lag in the positive convention φ = (c / ℓ_C) τ. -/
def coordinates {n : ℕ} (p : MassiveParameters) (a z : Fin n → ℂ) : State n :=
  (fun i => ‖z i‖, fun i => (p.ellC / p.c) * (localAction p (a i) (z i) / p.hbar))

/-- Coordinates with nonzero anchors reconstruct every complex lattice profile. -/
theorem coordinates_reconstruct {n : ℕ} (p : MassiveParameters) (a z : Fin n → ℂ)
    (ha : ∀ i, a i ≠ 0) :
    wave (coordinates p a z).1 (lagPhase p (coordinates p a z).2) = z := by
  funext i
  have scale : (p.c / p.ellC) * (p.ellC / p.c) = 1 := by
    field_simp [p.c_pos.ne', (ClockScales.ellC_pos p).ne']
  simp only [coordinates, wave, lagPhase]
  rw [← mul_assoc, scale, one_mul, Complex.norm_def]
  exact localAction_reconstruction p (ha i) (z i)

/-- On its anchored slit-plane chart, a differentiable complex site has a
positive modulus and differentiable real amplitude and lag coordinates. -/
theorem coordinates_regular {n : ℕ} (p : MassiveParameters) (a : Fin n → ℂ)
    (z : ℝ → Fin n → ℂ) (t : ℝ) (i : Fin n)
    (hz : DifferentiableAt ℝ (fun s => z s i) t) (hc : z t i ∈ chartDomain (a i)) :
    0 < (coordinates p a (z t)).1 i ∧
      DifferentiableAt ℝ (fun s => (coordinates p a (z s)).1 i) t ∧
      DifferentiableAt ℝ (fun s => (coordinates p a (z s)).2 i) t := by
  have hne : z t i ≠ 0 := Complex.normSq_pos.mp (normSq_pos_of_mem_chartDomain hc)
  have hS := ((contDiffAt_localAction p hc 1).differentiableAt one_ne_zero).comp t hz
  exact ⟨norm_pos_iff.mpr hne, hz.norm ℝ hne, (hS.div_const p.hbar).const_mul _⟩

/-- Every complex Schrödinger trajectory with nonzero sites at an anchor time
has a real polar lift. The lift reconstructs the wave and solves the joint
unregularized polar ODE with positive amplitudes on a common open interval. -/
theorem exists_local_lift {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z : ℝ → Fin n → ℂ) (t₀ : ℝ)
    (hz : ∀ᶠ t in 𝓝 t₀, ∀ i, HasDerivAt (fun s => z s i) (schrodinger p h V (z t) i) t)
    (ha : ∀ i, z t₀ i ≠ 0) :
    ∃ γ : ℝ → State n, (∀ t, wave (γ t).1 (lagPhase p (γ t).2) = z t) ∧
      ∃ l u, t₀ ∈ Set.Ioo l u ∧ ∀ t ∈ Set.Ioo l u,
        (∀ i, 0 < (γ t).1 i) ∧ HasDerivAt γ (field p h 0 V (γ t)) t := by
  let γ (s : ℝ) := coordinates p (z t₀) (z s)
  have hw (s : ℝ) : wave (γ s).1 (lagPhase p (γ s).2) = z s :=
    coordinates_reconstruct p (z t₀) (z s) ha
  have hc : ∀ᶠ t in 𝓝 t₀, ∀ i, z t i ∈ chartDomain (z t₀ i) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hz.self_of_nhds i).continuousAt.eventually
      ((isOpen_chartDomain _).mem_nhds (anchor_mem_chartDomain (ha i)))
  obtain ⟨l, u, ht₀, hI⟩ := (hz.and hc).exists_Ioo_subset
  refine ⟨γ, hw, l, u, ht₀, ?_⟩
  intro t ht
  obtain ⟨hzt, hct⟩ := hI ht
  have hreg (i : Fin n) := coordinates_regular p (z t₀) z t i (hzt i).differentiableAt (hct i)
  refine ⟨fun i => (hreg i).1, ?_⟩
  have hsite (i : Fin n) := (site_iff p h (fun s => (γ s).1) (fun s => (γ s).2) V t i
    (hreg i).1.ne' (hreg i).2.1 (hreg i).2.2).mp (by simpa only [hw] using hzt i)
  exact (hasDerivAt_pi.mpr fun i => (hsite i).1).prodMk
    (hasDerivAt_pi.mpr fun i => (hsite i).2)

end FoliationQM.LatticeSchrodingerLocalLift
