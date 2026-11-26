module

public import FoliationQM.LatticeLinkCurrent
public import FoliationQM.LatticeNeumannGreen
public import FoliationQM.LatticeRegularizedFlow

/-!
# Local continuity for the signed lattice density

At each site, the amplitude equation in v13 line 217 differentiates the
density to the incoming link current minus the outgoing link current per
unit mesh length. The replicated endpoint links carry zero current. Summing
over the whole path therefore cancels the interior fluxes.
-/

@[expose] public section
namespace FoliationQM.LatticeLocalContinuity

open LatticeConservation LatticeLinkCurrent LatticeRegularizedFlow LatticeLagHamiltonian

/-- The signed-amplitude density rate is the negative discrete divergence of
the two oriented link currents, including at a node or a replicated boundary. -/
theorem node_balance {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ : Fin n → ℝ) (i : Fin n) :
    2 * R i * sourceAmplitudeRHS p.ellC p.c h R φ i = -(plus p h R φ i - minus p h R φ i) / h := by
  unfold sourceAmplitudeRHS plus minus link
  field_simp [hh.ne']

/-- Local continuity along an arbitrary amplitude path satisfying the single
site amplitude equation. The phase does not need a time derivative. -/
theorem density_path {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ : ℝ → Fin n → ℝ) (t : ℝ) (i : Fin n)
    (hR : HasDerivAt (fun s => R s i) (sourceAmplitudeRHS p.ellC p.c h (R t) (φ t) i) t) :
    HasDerivAt (fun s => (R s i)^2) (-(plus p h (R t) (φ t) i - minus p h (R t) (φ t) i) / h) t := by
  rw [← node_balance p hh]
  simpa using hR.fun_pow 2

/-- An actual regularized source flow obeys the exact site-density law at
every width because the amplitude equation contains no reciprocal. -/
theorem flow_density_path {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h) (ε : ℝ)
    (V : Fin n → ℝ) (γ : ℝ → State n) (t : ℝ) (i : Fin n)
    (hγ : HasDerivAt γ (field p h ε V (γ t)) t) :
    HasDerivAt (fun s => ((γ s).1 i)^2)
      (-(plus p h (γ t).1 (lagPhase p (γ t).2) i - minus p h (γ t).1 (lagPhase p (γ t).2) i) / h) t :=
  density_path p hh (fun s => (γ s).1) (fun s => lagPhase p (γ s).2) t i
    ((component_rates p h ε V γ t hγ).1 i)

/-- Net unscaled outward current summed over the entire replicated path is zero. -/
theorem sum_net_flux {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ : Fin n → ℝ) :
    (∑ i, (plus p h R φ i - minus p h R φ i)) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact LatticeNeumannGreen.sum_forward_eq_backward
    (fun i j => link p h (R i) (R j) (φ i) (φ j)) (fun i => link_self p h (R i) (φ i))

/-- An isolated site has constant density to first order along the amplitude equation. -/
theorem singleton_density_path (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ : ℝ → Fin 1 → ℝ) (t : ℝ)
    (hR : HasDerivAt (fun s => R s 0) (sourceAmplitudeRHS p.ellC p.c h (R t) (φ t) 0) t) :
    HasDerivAt (fun s => (R s 0)^2) 0 t := by
  have hp : plus p h (R t) (φ t) 0 = 0 := plus_last (n := 0) p h (R t) (φ t)
  have hm := minus_first (n := 0) p h (R t) (φ t)
  simpa only [hp, hm, sub_zero, neg_zero, zero_div] using density_path p hh R φ t 0 hR

end FoliationQM.LatticeLocalContinuity
