module

public import FoliationQM.LatticeCenteredSiteCurrent
public import Mathlib.Analysis.Asymptotics.Ring

/-!
# Consistency of the regularized site velocity

At an interior sample point the numerator of the Eq. 9 drift velocity is
the average of its two neighboring link currents. Dividing by the source
density plus ε² gives a fixed-width continuum limit. For a nonzero site
amplitude, shrinking the regulator recovers the full lag gradient; widths
of order h preserve second-order consistency.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeSiteVelocityLimit

open Asymptotics Filter LatticeCenteredSiteCurrent
open scoped Topology

/-- The centered sampled site velocity, with the denominator of v13 Eq. 9. -/
def sampledVelocity (p : MassiveParameters) (ε : ℝ) (R τ : ℝ → ℝ) (x h : ℝ) : ℝ :=
  centered p R τ x h / ((R x)^2 + ε^2)

/-- At fixed width the spatial error is second order relative to the
continuum current divided by the same regularized density. -/
theorem velocity_error (p : MassiveParameters) (ε : ℝ) (R τ : ℝ → ℝ) (x : ℝ)
    (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ) :
    (fun h => sampledVelocity p ε R τ x h -
      p.c^2*(R x)^2*deriv τ x / ((R x)^2+ε^2)) =O[𝓝[>] 0] (fun h : ℝ => h^2) := by
  apply ((centered_error p R τ x hR hτ).const_mul_left (((R x)^2+ε^2)⁻¹)).congr_left
  intro h
  unfold sampledVelocity
  ring

/-- The fixed-width velocity converges to the regularized continuum value. -/
theorem velocity_tendsto (p : MassiveParameters) (ε : ℝ) (R τ : ℝ → ℝ) (x : ℝ)
    (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ) :
    Tendsto (sampledVelocity p ε R τ x) (𝓝[>] 0)
      (𝓝 (p.c^2*(R x)^2*deriv τ x / ((R x)^2+ε^2))) :=
  (centered_tendsto p R τ x hR hτ).div_const _

/-- The site velocity at a zero amplitude vanishes for all positive regulator
widths and spacings, even without smoothness of either field. -/
theorem at_node (p : MassiveParameters) (ε : ℝ) (R τ : ℝ → ℝ) (x h : ℝ) (hx : R x = 0) :
    sampledVelocity p ε R τ x h = 0 := by
  rw [sampledVelocity, centered_eq_zero_of_node p R τ x h hx, zero_div]

private theorem zero_width_target (p : MassiveParameters) (r d : ℝ) (hr : r ≠ 0) :
    p.c^2*r^2*d / (r^2+(0 : ℝ)^2) = p.c^2*d := by
  field_simp [hr]
  ring

/-- Off nodes, the zero-width velocity agrees with c² times the lag gradient up to O(h²). -/
theorem unregularized_error (p : MassiveParameters) (R τ : ℝ → ℝ) (x : ℝ)
    (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ) (hx : R x ≠ 0) :
    (fun h => sampledVelocity p 0 R τ x h - p.c^2*deriv τ x) =O[𝓝[>] 0]
      (fun h : ℝ => h^2) := by
  simpa only [zero_width_target p _ _ hx] using velocity_error p 0 R τ x hR hτ

/-- At a nonzero amplitude the unregularized site velocity tends to the full continuum velocity. -/
theorem unregularized_tendsto (p : MassiveParameters) (R τ : ℝ → ℝ) (x : ℝ)
    (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ) (hx : R x ≠ 0) :
    Tendsto (sampledVelocity p 0 R τ x) (𝓝[>] 0) (𝓝 (p.c^2*deriv τ x)) := by
  simpa only [zero_width_target p _ _ hx] using velocity_tendsto p 0 R τ x hR hτ

/-- Every regulator converging to zero with the mesh width recovers the full
continuum velocity at a nonzero-amplitude site. -/
theorem shrinking_width_tendsto (p : MassiveParameters) (ε R τ : ℝ → ℝ) (x : ℝ)
    (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ) (hx : R x ≠ 0)
    (hε : Tendsto ε (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h => sampledVelocity p (ε h) R τ x h) (𝓝[>] 0) (𝓝 (p.c^2*deriv τ x)) := by
  have hd := (tendsto_const_nhds (x := (R x)^2) (f := 𝓝[>] (0 : ℝ))).add (hε.pow 2)
  have hn : (R x)^2+(0 : ℝ)^2 ≠ 0 := by simpa using pow_ne_zero 2 hx
  simpa only [sampledVelocity, zero_width_target p _ _ hx, Pi.div_def] using
    (centered_tendsto p R τ x hR hτ).div hd hn

/-- A width of order h preserves the second-order velocity error at every
nonzero-amplitude site, since its contribution to the density is quadratic. -/
theorem linear_width_error (p : MassiveParameters) (ε R τ : ℝ → ℝ) (x : ℝ)
    (hR : ContDiff ℝ 3 R) (hτ : ContDiff ℝ 3 τ) (hx : R x ≠ 0)
    (hε : ε =O[𝓝[>] 0] (fun h : ℝ => h)) :
    (fun h => sampledVelocity p (ε h) R τ x h - p.c^2*deriv τ x) =O[𝓝[>] 0]
      (fun h : ℝ => h^2) := by
  have hr : 0 < (R x)^2 := sq_pos_of_ne_zero hx
  have hd (h : ℝ) : 0 < (R x)^2+(ε h)^2 := add_pos_of_pos_of_nonneg hr (sq_nonneg _)
  have hb : (fun h => ((R x)^2+(ε h)^2)⁻¹) =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) := by
    apply isBigO_of_le' (c := ((R x)^2)⁻¹)
    intro h
    simp only [Real.norm_of_nonneg (inv_nonneg.mpr (hd h).le), norm_one, mul_one]
    exact inv_anti₀ hr (le_add_of_nonneg_right (sq_nonneg _))
  have he := (centered_error p R τ x hR hτ).sub ((hε.pow 2).const_mul_left (p.c^2*deriv τ x))
  apply (he.mul hb).congr
  · intro h
    unfold sampledVelocity
    field_simp [(hd h).ne']
    ring
  · intro h
    exact mul_one _

end FoliationQM.LatticeSiteVelocityLimit
