module

public import FoliationQM.LatticeLeftEndpointError
public import FoliationQM.LatticeStaggeredVelocity

/-!
# First-order velocity error at a replicated endpoint

The smooth lag τ(x) = x² and constant amplitude one give zero continuum
velocity at x = 0, satisfying the no-flux condition there. The left row of
the replicated stencil in v13 Eq. 9 includes only one nonzero link. The
resulting site velocity has a nonzero first-order coefficient for each
fixed regulator width, including width zero.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeBoundaryVelocity

open LatticeConservation LatticeLinkCurrent LatticeStaggeredVelocity LatticeLagHamiltonian
open LatticeLeftEndpointError LatticeTwoSiteEnergyDrift Filter Asymptotics
open scoped Topology

/-- The actual two-site left velocity at unit amplitude, using lag samples τ(0), τ(h). -/
def leftVelocity (ε h : ℝ) : ℝ :=
  siteVelocity units h ε (fun _ : Fin 2 => 1) (lagPhase units ![0, h^2]) 0

/-- Both the amplitude and the lag have zero normal derivative at the left endpoint. -/
theorem no_flux_data :
    HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 ∧ HasDerivAt (fun x : ℝ => x^2) 0 0 := by
  exact ⟨hasDerivAt_const _ _, by simpa using hasDerivAt_pow 2 (0 : ℝ)⟩

/-- Replication kills the backward link and retains exactly half the damped forward flux. -/
theorem leftVelocity_eq (ε h : ℝ) : leftVelocity ε h = edge h / (2*(1+ε^2)) := by
  rw [leftVelocity, siteVelocity, minus_first, add_zero]
  simp [plus, nextNode, lagPhase, units, MassiveParameters.ellC, edge]

/-- Every longer uniform grid sampling the same lag has precisely the same left row. -/
theorem uniform_grid_left (N : ℕ) (ε h : ℝ) :
    siteVelocity units h ε (fun _ : Fin (N+2) => 1)
      (lagPhase units (fun j => ((j.val : ℝ)*h)^2)) 0 = leftVelocity ε h := by
  rw [leftVelocity_eq, siteVelocity, minus_first, add_zero]
  simp [plus, nextNode, lagPhase, units, MassiveParameters.ellC, edge]

/-- At every positive width, the residual after subtracting the leading
boundary velocity is bounded by h⁵ divided by 12(1+ε²). -/
theorem remainder_bound (ε : ℝ) {h : ℝ} (hh : 0 < h) :
    |leftVelocity ε h - h/(2*(1+ε^2))| ≤ h^5/(12*(1+ε^2)) := by
  have hd : 0 < 2*(1+ε^2) := by positivity
  rw [leftVelocity_eq, ← sub_div, abs_div, abs_of_pos hd]
  have hb := div_le_div_of_nonneg_right (midpoint_error_bound hh) hd.le
  rwa [div_div, show 6*(2*(1+ε^2)) = 12*(1+ε^2) by ring] at hb

/-- The error relative to the zero continuum velocity, divided by h, tends to
the strictly positive coefficient 1/[2(1+ε²)] for any fixed regulator width. -/
theorem first_order_limit (ε : ℝ) :
    Tendsto (fun h : ℝ => leftVelocity ε h / h) (𝓝[>] 0) (𝓝 (1/(2*(1+ε^2)))) := by
  apply (left_error_ratio.div_const (2*(1+ε^2))).congr
  intro h
  rw [leftVelocity_eq, div_div, div_div, mul_comm]

/-- The replicated boundary row has no quadratic error estimate relative to
the zero continuum velocity even with left-endpoint Neumann compatibility. -/
theorem boundary_not_quadratic (ε : ℝ) :
    ¬ leftVelocity ε =O[𝓝[>] 0] (fun h : ℝ => h^2) := by
  intro hb
  have hcomp : (fun h : ℝ => h^2) =o[𝓝[>] 0] (fun h => h) := by
    simpa only [pow_one] using
      ((isLittleO_pow_pow (𝕜 := ℝ) (by decide : 1 < 2)).mono nhdsWithin_le_nhds)
  have hzero := (hb.trans_isLittleO hcomp).tendsto_div_nhds_zero
  have hn : 0 < 1/(2*(1+ε^2)) := by positivity
  exact hn.ne' (tendsto_nhds_unique (first_order_limit ε) hzero)

end FoliationQM.LatticeBoundaryVelocity
