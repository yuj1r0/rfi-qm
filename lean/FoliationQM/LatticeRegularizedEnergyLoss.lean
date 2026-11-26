module

public import FoliationQM.LatticeTwoSiteEnergyDrift
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Strict energy loss on an actual regularized lattice solution

Starting at the two-site quarter-turn state, the smooth regularized equations
give an integral curve for each positive regulator width. The geometric energy
starts at 5/2 and its strictly negative initial derivative forces strict loss
at every sufficiently small positive time. Both amplitudes remain positive and
the rectangular mass is five throughout a neighborhood of the initial time.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeRegularizedEnergyLoss

open LatticeConservation LatticeRegularizedFlow LatticeLagHamiltonian
open LatticePolarEnergyBalance LatticeTwoSiteEnergyDrift WeightedLatticeHamiltonian
open scoped Topology

/-- The normalized geometric energy of the quarter-turn initial state is 5/2. -/
theorem energy_seed : energyAlong units 1 potential seed = 5/2 := by
  change geometric units 1 amplitude (lagPhase units lag) potential = 5/2
  rw [phase_eq_lag]
  norm_num [geometric, Fin.sum_univ_two, weightedSite, forwardDiff, amplitude, lag, potential,
    nextNode, units, MassiveParameters.ellC, Real.cos_pi_div_two]

/-- Every regularized integral curve through the stated initial data has the
same explicit energy derivative at its initial time. -/
theorem initial_energy_derivative (ε : ℝ) (hε : 0 < ε) (γ : ℝ → State 2) (hinit : γ 0 = seed)
    (hγ : HasDerivAt γ (field units 1 ε potential (γ 0)) 0) :
    HasDerivAt (fun s => energyAlong units 1 potential (γ s))
      (-3*ε^2/((1+ε^2)*(4+ε^2))) 0 := by
  apply (energy_path units (by norm_num : (0 : ℝ) < 1) ε potential γ 0
    (fun _ => Or.inr hε.ne') hγ).congr_deriv
  rw [hinit]
  exact drift_eq ε

/-- At every positive regulator width a two-site solution has the exact initial
energy derivative, constant mass five and positive site amplitudes. Every
sufficiently small positive time has strictly lower energy than the initial time. -/
theorem exists_strict_energy_loss (ε : ℝ) (hε : 0 < ε) :
    ∃ γ : ℝ → State 2, γ 0 = seed ∧
      HasDerivAt (fun s => energyAlong units 1 potential (γ s))
        (-3*ε^2/((1+ε^2)*(4+ε^2))) 0 ∧
      ∃ δ > 0, (∀ s ∈ Set.Ioo (-δ) δ,
        HasDerivAt γ (field units 1 ε potential (γ s)) s ∧
        sourceMass 1 (γ s).1 = 5 ∧ ∀ i, 0 < (γ s).1 i) ∧
        ∀ s ∈ Set.Ioo 0 δ, energyAlong units 1 potential (γ s) < 5/2 := by
  obtain ⟨γ, hinit, r, hr, hsol⟩ := exists_solution units 1 hε potential seed 0
  simp only [zero_sub, zero_add] at hsol
  have hγ := (hsol 0 ⟨neg_lt_zero.mpr hr, hr⟩).1
  have hd := initial_energy_derivative ε hε γ hinit hγ
  let E (s : ℝ) := energyAlong units 1 potential (γ s)
  have hneg := drift_neg ε hε
  rw [drift_eq] at hneg
  have hloss : ∀ᶠ s in 𝓝[>] (0 : ℝ), E s < 5/2 := by
    have hs := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2.eventually_lt_const hneg
    filter_upwards [hs, self_mem_nhdsWithin] with s hs (hspos : 0 < s)
    have hlt : E s < E 0 := (slope_neg_iff_of_le hspos.le).mp hs
    simpa only [E, hinit, energy_seed] using hlt
  have hpos : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i, 0 < (γ s).1 i := by
    apply Filter.eventually_all.mpr
    intro i
    have hdR := (component_rates units 1 ε potential γ 0 hγ).1 i
    exact hdR.continuousAt.eventually (lt_mem_nhds (by
      change 0 < (γ 0).1 i
      rw [hinit]
      exact amplitude_pos i))
  have hlocal : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ Set.Ioo (-r) r := Ioo_mem_nhds (neg_lt_zero.mpr hr) hr
  have hnear := hlocal.and hpos
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hnear
  rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hball
  obtain ⟨b, hb, hl⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hloss
  refine ⟨γ, hinit, hd, min a b, lt_min ha hb, ?_, ?_⟩
  · intro s hs
    have hsa : s ∈ Set.Ioo (-a) a :=
      ⟨lt_of_le_of_lt (neg_le_neg (min_le_left a b)) hs.1, lt_of_lt_of_le hs.2 (min_le_left a b)⟩
    obtain ⟨hsr, hps⟩ := hball hsa
    exact ⟨(hsol s hsr).1, (hsol s hsr).2.trans mass_seed, hps⟩
  · intro s hs
    exact hl ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right a b)⟩

end FoliationQM.LatticeRegularizedEnergyLoss
