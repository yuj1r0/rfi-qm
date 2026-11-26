module

public import FoliationQM.LatticeMidpointCurrent
public import FoliationQM.LatticeTwoSiteEnergyDrift
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Location of the continuum comparison for the link current

In unit physical scales take amplitude one and the smooth lag τ(x) = x².
The link on [0,h] has current sin(h²)/h. Its continuum flux at the midpoint
is h and at the left endpoint is zero. The latter choice produces a
first-order discrepancy with leading coefficient one in Eq. 9 of v13.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeLeftEndpointError

open LatticeLinkCurrent LatticeMidpointCurrent LatticeTwoSiteEnergyDrift
open Filter Asymptotics
open scoped Topology

/-- Current on [0,h] for constant unit amplitude and quadratic lag in unit scales. -/
def edge (h : ℝ) : ℝ := link units h 1 1 0 (h^2)

/-- Sampling the general link formula at the midpoint recovers the edge on [0,h]. -/
theorem sampled_midpoint (h : ℝ) :
    sampledLink units (fun _ => 1) (fun x => x^2) (h/2) h = edge h := by
  simp [sampledLink, edge, units, MassiveParameters.ellC, show h/2 + h/2 = h by ring]

/-- The exact oriented current on this edge. -/
theorem edge_eq (h : ℝ) : edge h = Real.sin (h^2) / h := by
  simp [edge, link, units, MassiveParameters.ellC, div_eq_mul_inv, mul_comm]

/-- The continuum value c²R²τ′ is zero at the left site and h at the midpoint. -/
theorem continuum_values (h : ℝ) :
    units.c^2 * (1 : ℝ)^2 * deriv (fun x : ℝ => x^2) 0 = 0 ∧
    units.c^2 * (1 : ℝ)^2 * deriv (fun x : ℝ => x^2) (h/2) = h := by
  simp [units]
  ring

/-- In this example the exact midpoint error is bounded by h⁵/6 at every positive width. -/
theorem midpoint_error_bound {h : ℝ} (hh : 0 < h) : |edge h - h| ≤ h^5/6 := by
  have he : edge h - h = (Real.sin (h^2) - h^2) / h := by
    rw [edge_eq]
    field_simp
  rw [he, abs_div, abs_of_pos hh, abs_sub_comm, div_le_iff₀ hh]
  have hb := Real.abs_sub_sin_le (h^2)
  rw [abs_of_nonneg (sq_nonneg h)] at hb
  convert hb using 1
  ring

/-- After division by h, the discrepancy from the left endpoint value tends to one. -/
theorem left_error_ratio :
    Tendsto (fun h : ℝ => edge h / h) (𝓝[>] 0) (𝓝 1) := by
  have hs : Tendsto (fun h : ℝ => h^2) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hpow : Continuous (fun h : ℝ => h^2) := by fun_prop
      simpa using hpow.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0) (a := 0))
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      exact pow_ne_zero 2 hh.ne'
  have ht := Real.tendsto_sin_div_nhdsNE_zero.comp hs
  apply ht.congr
  intro h
  simp only [Function.comp_apply, edge_eq, div_div, pow_two]

/-- No constant bounds the left-site discrepancy by a multiple of h² near zero. -/
theorem left_error_not_quadratic :
    ¬ edge =O[𝓝[>] 0] (fun h : ℝ => h^2) := by
  intro hb
  have hcomp : (fun h : ℝ => h^2) =o[𝓝[>] 0] (fun h => h) := by
    simpa only [pow_one] using
      ((isLittleO_pow_pow (𝕜 := ℝ) (by decide : 1 < 2)).mono nhdsWithin_le_nhds)
  have hzero := (hb.trans_isLittleO hcomp).tendsto_div_nhds_zero
  exact one_ne_zero (tendsto_nhds_unique left_error_ratio hzero)

end FoliationQM.LatticeLeftEndpointError
