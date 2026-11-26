module

public import FoliationQM.LatticeLocalContinuity
public import FoliationQM.LatticeNeumannGreen

/-!
# Probability balance in a lattice region

Testing the local density equation against a fixed site observable gives
its rate as a sum of link currents against forward increments. For the
indicator of any subset only edges crossing its boundary contribute.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeRegionFlux

open LatticeConservation LatticeLinkCurrent LatticeNeumannGreen

/-- Discrete weak continuity equation, including the rectangular spatial
weight and both replicated endpoints. -/
theorem observable_balance {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ w : Fin n → ℝ) :
    (∑ i, h * w i * (2 * R i * sourceAmplitudeRHS p.ellC p.c h R φ i)) =
      ∑ i, plus p h R φ i * (w (nextNode i) - w i) := by
  let F (i j : Fin n) := link p h (R i) (R j) (φ i) (φ j)
  have hd (i : Fin n) : F i i = 0 := by simp [F, link]
  rw [show (∑ i, plus p h R φ i * (w (nextNode i)-w i)) =
      ∑ i, (minus p h R φ i - plus p h R φ i) * w i from summation_by_parts F hd w]
  apply Finset.sum_congr rfl
  intro i _
  rw [LatticeLocalContinuity.node_balance p hh R φ i]
  field_simp [hh.ne']
  ring

/-- Net inward signed flux of a set of sites. Each oriented crossing has
coefficient +1 on entry or −1 on exit and every other link has coefficient zero. -/
def inwardFlux {n : ℕ} (S : Finset (Fin n)) (p : MassiveParameters) (h : ℝ)
    (R φ : Fin n → ℝ) : ℝ :=
  ∑ i, plus p h R φ i * ((if nextNode i ∈ S then (1:ℝ) else 0) -
    (if i ∈ S then 1 else 0))

/-- The actual time derivative of the rectangular mass in an arbitrary set
of sites is its net inward current under the source amplitude equation. -/
theorem region_mass_path {n : ℕ} (S : Finset (Fin n)) (p : MassiveParameters)
    {h : ℝ} (hh : 0 < h) (R φ : ℝ → Fin n → ℝ) (t : ℝ)
    (hd : ∀ i, HasDerivAt (fun s => R s i)
      (sourceAmplitudeRHS p.ellC p.c h (R t) (φ t) i) t) :
    HasDerivAt (fun s => ∑ i ∈ S, h * R s i ^ 2) (inwardFlux S p h (R t) (φ t)) t := by
  let w (i : Fin n) : ℝ := if i ∈ S then 1 else 0
  have h1 (i : Fin n) : HasDerivAt (fun s => h*w i * (R s i)^2)
      (h*w i * (2 * R t i * sourceAmplitudeRHS p.ellC p.c h (R t) (φ t) i)) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using ((hd i).fun_pow 2).const_mul (h*w i)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h1 i)
  rw [observable_balance p hh (R t) (φ t) w] at hs
  convert hs using 1
  · funext s
    simp [w, mul_ite, ite_mul, Finset.sum_ite_mem]
  · rfl

end FoliationQM.LatticeRegionFlux
