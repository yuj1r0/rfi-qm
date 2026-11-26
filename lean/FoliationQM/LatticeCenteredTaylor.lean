module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Tactic

/-!
# Centered finite differences at positive mesh width

The link-current expansion in v13 Eq. 9 uses the cancellation of the
even Taylor terms at opposite displacements. Taylor–Young at order
three gives a quantitative bound for each sufficiently small positive
mesh width, with a constant determined by the third derivative at zero.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeCenteredTaylor

open Asymptotics Filter Set
open scoped Topology

private theorem cubic (f : ℝ → ℝ) (x : ℝ) :
    taylorWithinEval f 3 univ 0 x =
      f 0 + x*deriv f 0 + x^2/2*iteratedDeriv 2 f 0 + x^3/6*iteratedDeriv 3 f 0 := by
  rw [taylorWithinEval_succ f 2, taylorWithinEval_succ f 1, taylorWithinEval_succ f 0]
  norm_num [taylor_within_zero_eval, iteratedDerivWithin_univ, iteratedDeriv_one,
    Nat.factorial, smul_eq_mul]
  ring

/-- The centered first-difference error eventually has magnitude at most
`(1 + |f'''(0)| / 6) h²` as positive spacings tend to zero. -/
theorem eventual_centered_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      |(f h - f (-h))/(2*h) - deriv f 0| ≤ (1 + |iteratedDeriv 3 f 0|/6)*h^2 := by
  let r (x : ℝ) := f x - taylorWithinEval f 3 univ 0 x
  have hR : ∀ᶠ x in 𝓝 (0 : ℝ), |r x| ≤ |x|^3 := by
    simpa only [r, sub_zero, one_mul, Real.norm_eq_abs, abs_pow] using
      (taylor_isLittleO_univ (x₀ := 0) hf).def (by norm_num : (0 : ℝ) < 1)
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hR.filter_mono nhdsWithin_le_nhds, hneg.eventually hR,
    self_mem_nhdsWithin] with h hpos hminus hh
  change 0 < h at hh
  rw [abs_of_pos hh] at hpos
  simp only [abs_neg, abs_of_pos hh] at hminus
  have herr : |(r h - r (-h))/(2*h)| ≤ h^2 := by
    rw [abs_div, abs_of_pos (show 0 < 2*h by positivity), div_le_iff₀ (by positivity)]
    calc
      |r h - r (-h)| ≤ |r h| + |r (-h)| := abs_sub _ _
      _ ≤ h^3 + h^3 := add_le_add hpos hminus
      _ = _ := by ring
  have heq : (f h - f (-h))/(2*h) - deriv f 0 =
      (r h - r (-h))/(2*h) + (iteratedDeriv 3 f 0/6)*h^2 := by
    simp only [r, cubic]
    field_simp [hh.ne']
    ring
  rw [heq]
  calc
    _ ≤ |(r h - r (-h))/(2*h)| + |(iteratedDeriv 3 f 0/6)*h^2| := abs_add_le ..
    _ ≤ h^2 + |(iteratedDeriv 3 f 0/6)*h^2| := add_le_add_left herr _
    _ = _ := by rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg h)]; norm_num; ring

/-- A C³ scalar profile has second-order centered first-difference consistency. -/
theorem centered_error (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) :
    (fun h => (f h - f (-h))/(2*h) - deriv f 0) =O[𝓝[>] 0] (fun h : ℝ => h^2) := by
  apply IsBigO.of_bound (1 + |iteratedDeriv 3 f 0|/6)
  filter_upwards [eventual_centered_bound f hf] with h hh
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)] using hh

end FoliationQM.LatticeCenteredTaylor
