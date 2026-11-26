module

public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# A genuine scalar second-order limit

Source: the analytic small-shift step in v13 `eq:kl_fisher_expansion`.
These theorems concern an actual real function and its actual derivatives.
No Taylor remainder or desired limit is supplied as a premise. A derivative
limit and l'Hôpital's theorem give the quadratic quotient limit, including
under merely local C2 regularity. Identifying a translated KL functional's
derivatives and passing a probe average through this limit remain separate.
-/

@[expose] public section

namespace FoliationQM.SecondOrderLimit

open Filter Topology

/-- The actual second derivative gives the first derivative's punctured
linear quotient limit when the first derivative vanishes at zero. -/
theorem tendsto_deriv_div {K : ℝ → ℝ} {L : ℝ}
    (hfirst : deriv K 0 = 0) (hsecond : HasDerivAt (deriv K) L 0) :
    Tendsto (fun t => deriv K t / t) (𝓝[≠] 0) (𝓝 L) := by
  simpa only [zero_add, hfirst, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
    using hsecond.tendsto_slope_zero

/-- Local differentiability and an actual second derivative at zero imply
the quadratic quotient limit. The proof derives it by l'Hôpital's theorem. -/
theorem tendsto_div_sq_of_hasDerivAt {K : ℝ → ℝ} {L : ℝ}
    (hK : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ K t)
    (hzero : K 0 = 0) (hfirst : deriv K 0 = 0)
    (hsecond : HasDerivAt (deriv K) L 0) :
    Tendsto (fun t => K t / t ^ 2) (𝓝[≠] 0) (𝓝 (L / 2)) := by
  have hf : ∀ᶠ t in 𝓝[≠] (0 : ℝ), HasDerivAt K (deriv K t) t :=
    (hK.mono (fun t ht => ht.hasDerivAt)).filter_mono nhdsWithin_le_nhds
  have hg : ∀ᶠ t in 𝓝[≠] (0 : ℝ), HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    filter_upwards [] with t
    simpa using! (hasDerivAt_id t).fun_pow 2
  have hg' : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 2 * t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero (by norm_num) ht
  have hfzero : Tendsto K (𝓝[≠] 0) (𝓝 0) := by
    simpa only [hzero] using
      (hK.self_of_nhds.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hgzero : Tendsto (fun t : ℝ => t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t ^ 2) := by fun_prop
    simpa using ((hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0))
  have hquot : Tendsto (fun t => deriv K t / (2 * t)) (𝓝[≠] 0) (𝓝 (L / 2)) := by
    convert (tendsto_deriv_div hfirst hsecond).div_const 2 using 1
    ext t
    ring
  exact HasDerivAt.lhopital_zero_nhdsNE hf hg hg' hfzero hgzero hquot

/-- Local C2 regularity supplies the analytic hypotheses; the limit is half
the actual second derivative, without any assumed expansion. -/
theorem tendsto_div_sq_of_contDiffAt {K : ℝ → ℝ}
    (hK : ContDiffAt ℝ 2 K 0) (hzero : K 0 = 0) (hfirst : deriv K 0 = 0) :
    Tendsto (fun t => K t / t ^ 2) (𝓝[≠] 0) (𝓝 (deriv (deriv K) 0 / 2)) := by
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ K t :=
    (hK.eventually (by norm_num)).mono (fun t ht => ht.differentiableAt (by norm_num))
  have hd : ContDiffAt ℝ 1 (deriv K) 0 := hK.derivWithin (by norm_num)
  exact tendsto_div_sq_of_hasDerivAt he hzero hfirst
    (hd.differentiableAt (by norm_num)).hasDerivAt

/-- An independently computed actual second derivative identifies the
quadratic quotient coefficient under local C2 regularity. -/
theorem tendsto_div_sq_of_contDiffAt_eq {K : ℝ → ℝ} {L : ℝ}
    (hK : ContDiffAt ℝ 2 K 0) (hzero : K 0 = 0) (hfirst : deriv K 0 = 0)
    (hsecond : deriv (deriv K) 0 = L) :
    Tendsto (fun t => K t / t ^ 2) (𝓝[≠] 0) (𝓝 (L / 2)) := by
  simpa only [hsecond] using tendsto_div_sq_of_contDiffAt hK hzero hfirst

/-- A globally C2 scalar function satisfies the same actual second-order
limit; only its local C2 regularity at zero is used. -/
theorem tendsto_div_sq_of_contDiff {K : ℝ → ℝ}
    (hK : ContDiff ℝ 2 K) (hzero : K 0 = 0) (hfirst : deriv K 0 = 0) :
    Tendsto (fun t => K t / t ^ 2) (𝓝[≠] 0) (𝓝 (deriv (deriv K) 0 / 2)) :=
  tendsto_div_sq_of_contDiffAt hK.contDiffAt hzero hfirst

end FoliationQM.SecondOrderLimit
