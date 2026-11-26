module

public import FoliationQM.LatticeMidpointCurrent
public import FoliationQM.LatticeLagHamiltonian

/-!
# Sampling a physical finite link at its midpoint

The continuum estimate at a fixed midpoint applies directly to the actual
finite source current across any physical edge of a translated uniform mesh.
The origin, grid size and index may all vary with the mesh spacing.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeMidpointGrid

open LatticeMidpointCurrent LatticeLinkCurrent LatticeLagHamiltonian LatticeConservation
open Asymptotics Filter
open scoped Topology

/-- Site sampling on a uniform lattice with arbitrary origin. -/
def gridSample {n : ℕ} (a h : ℝ) (f : ℝ → ℝ) (i : Fin n) : ℝ := f (a + (i.val : ℝ)*h)

/-- A nonterminal outgoing source link equals symmetric sampling at its own midpoint. -/
theorem plus_at_midpoint {n : ℕ} (p : MassiveParameters) (a h : ℝ) (R τ : ℝ → ℝ)
    (i : Fin n) (hi : i.val + 1 < n) :
    plus p h (gridSample a h R) (lagPhase p (gridSample a h τ)) i =
      sampledLink p R τ (a + (i.val : ℝ)*h + h/2) h := by
  have hn : ((nextNode i).val : ℝ) = (i.val : ℝ) + 1 := by
    simp [nextNode, hi]
  have hl : a + (i.val : ℝ)*h + h/2 - h/2 = a + (i.val : ℝ)*h := by ring
  have hr : a + (i.val : ℝ)*h + h/2 + h/2 = a + ((i.val : ℝ)+1)*h := by ring
  simp only [plus, sampledLink, gridSample, lagPhase, hn, hl, hr]

/-- Refining finite grids may change their origin, number of sites and chosen
edge while preserving its physical midpoint. Their actual outgoing current
has the second-order error estimate at that midpoint. -/
theorem refining_grid_error {ι : Type*} (l : Filter ι) (p : MassiveParameters)
    (R τ : ℝ → ℝ) (x : ℝ) (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ)
    (n : ι → ℕ) (a h : ι → ℝ) (i : (k : ι) → Fin (n k))
    (hh : Tendsto h l (𝓝[>] 0))
    (hedge : ∀ᶠ k in l, (i k).val + 1 < n k ∧ a k + ((i k).val : ℝ)*h k + h k/2 = x) :
    (fun k => plus p (h k) (gridSample (a k) (h k) R)
      (lagPhase p (gridSample (a k) (h k) τ)) (i k) - p.c^2*(R x)^2*deriv τ x)
      =O[l] (fun k => (h k)^2) := by
  have hb := (midpoint_error p R τ x hR hτ).comp_tendsto hh
  apply hb.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hedge] with k hk
  simp only [Function.comp_apply, plus_at_midpoint p (a k) (h k) R τ (i k) hk.1, hk.2]

end FoliationQM.LatticeMidpointGrid
