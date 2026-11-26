module

public import FoliationQM.LatticeMidpointGrid
public import FoliationQM.LatticeSiteVelocityLimit
public import FoliationQM.LatticeStaggeredVelocity

/-!
# The centered velocity on a sampled interior grid site

On an interior row the replicated finite-grid velocity is the symmetric
three-site sample of the continuous fields. A family of grids may shift
its origin and index while sampling the same physical site.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeInteriorVelocityGrid

open LatticeMidpointGrid LatticeSiteVelocityLimit LatticeStaggeredVelocity
open LatticeLagHamiltonian LatticeConservation LatticeCenteredSiteCurrent LatticeLinkCurrent
open Filter Asymptotics
open scoped Topology

/-- The finite-grid source velocity on an interior row equals the centered
sample at the physical site for arbitrary signed amplitudes and regulator. -/
theorem sampled_row {n : ℕ} (p : MassiveParameters) (a h ε : ℝ) (R τ : ℝ → ℝ)
    (i : Fin n) (hl : 0 < i.val) (hr : i.val + 1 < n) :
    siteVelocity p h ε (gridSample a h R) (lagPhase p (gridSample a h τ)) i =
      sampledVelocity p ε R τ (a+(i.val:ℝ)*h) h := by
  have hn : ((nextNode i).val : ℝ) = (i.val : ℝ) + 1 := by simp [nextNode, hr]
  have hp : ((prevNode i).val : ℝ) = (i.val : ℝ) - 1 := by
    simp only [prevNode]
    exact_mod_cast (Nat.cast_sub (R := ℝ) (show 1 ≤ i.val from hl))
  have right : a + ((i.val:ℝ)+1)*h = a + (i.val:ℝ)*h + h := by ring
  have left : a + ((i.val:ℝ)-1)*h = a + (i.val:ℝ)*h - h := by ring
  simp only [siteVelocity, sampledVelocity, centered, plus, minus, gridSample, lagPhase,
    hn, hp, right, left, div_div]

/-- Along any refining mesh family with an actual interior row at x, the
source velocity has an O(h²) error around the fixed-width continuum drift. -/
theorem refining_velocity_error {ι : Type*} (l : Filter ι) (p : MassiveParameters) (ε : ℝ)
    (R τ : ℝ → ℝ) (x : ℝ) (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ)
    (n : ι → ℕ) (a h : ι → ℝ) (i : (k : ι) → Fin (n k))
    (hh : Tendsto h l (𝓝[>] 0)) (hrow : ∀ᶠ k in l,
      0 < (i k).val ∧ (i k).val + 1 < n k ∧ a k + ((i k).val:ℝ)*h k = x) :
    (fun k => siteVelocity p (h k) ε (gridSample (a k) (h k) R)
      (lagPhase p (gridSample (a k) (h k) τ)) (i k) -
        (p.c^2 * (R x)^2 * deriv τ x / ((R x)^2 + ε^2)))
      =O[l] (fun k => (h k)^2) := by
  have hb := (velocity_error p ε R τ x hR hτ).comp_tendsto hh
  apply hb.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hrow] with k hk
  simp only [Function.comp_apply, sampled_row p (a k) (h k) ε R τ (i k) hk.1 hk.2.1, hk.2.2]

end FoliationQM.LatticeInteriorVelocityGrid
