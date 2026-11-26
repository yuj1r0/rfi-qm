module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# Actual fourth-order Taylor control on a displacement segment

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`, and the
supplement's finite-displacement paragraph following `prop:audit11_kl`.
The genuine iterated Fréchet derivatives give an exact cubic Taylor formula
with an integrable fourth-order remainder. A common fourth-derivative bound
then gives the sharp factor `1/24`. The bound is supplied on the actual
density's derivative and may depend on that density. No Taylor expansion,
KL identity, probe cancellation, or universal remainder constant is an input.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FourthOrderTaylor
open MeasureTheory Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual degree-three Taylor polynomial in a displacement. -/
def cubicPolynomial (g : E → ℝ) (x a : E) : ℝ :=
  g x + fderiv ℝ g x a + (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 g x (fun _ => a) +
    (1 / 6 : ℝ) * iteratedFDeriv ℝ 3 g x (fun _ => a)

/-- Genuine fourth-order integral remainder along a segment. -/
theorem sub_cubic_eq_integral {g : E → ℝ} (x a : E)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 4 g (x + t • a)) :
    g (x + a) - cubicPolynomial g x a =
      (1 / 6 : ℝ) * ∫ t in (0 : ℝ)..1,
        (1 - t) ^ 3 * iteratedFDeriv ℝ 4 g (x + t • a) (fun _ => a) := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (n := 3) hg
  norm_num [Finset.sum_range_succ, cubicPolynomial, iteratedFDeriv_one_apply,
    iteratedFDeriv_zero_apply, smul_eq_mul] at h ⊢
  linarith

/-- The integral of the nonnegative cubic Taylor kernel is one fourth. -/
theorem integral_cubic_kernel : (∫ t in (0 : ℝ)..1, (1 - t) ^ 3) = 1 / 4 := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => -((1-s)^4)/4) ((1-t)^3) t := by
    convert ((((hasDerivAt_id t).const_sub 1).pow 4).neg.div_const 4) using 1
    · ext s
      simp
    · simp only [id_eq]
      ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) ((by fun_prop : Continuous (fun t : ℝ => (1 - t)^3)).intervalIntegrable 0 1)
  norm_num at h ⊢
  exact h

/-- Fourth-derivative operator-norm bounds imply a displacement fourth-power bound. -/
theorem norm_fourth_apply_le {g : E → ℝ} (z a : E) {M : ℝ}
    (hM : ‖iteratedFDeriv ℝ 4 g z‖ ≤ M) :
    ‖iteratedFDeriv ℝ 4 g z (fun _ => a)‖ ≤ M * ‖a‖ ^ 4 := by
  have h : ‖iteratedFDeriv ℝ 4 g z (fun _ => a)‖ ≤ ‖iteratedFDeriv ℝ 4 g z‖ * ‖a‖ ^ 4 := by
    simpa using (iteratedFDeriv ℝ 4 g z).le_opNorm (fun _ => a)
  exact h.trans (mul_le_mul_of_nonneg_right hM (by positivity))

/-- A segment fourth-derivative bound controls the actual cubic remainder. -/
theorem norm_sub_cubic_le {g : E → ℝ} (x a : E)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 4 g (x + t • a))
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 4 g (x + t • a)‖ ≤ M) :
    ‖g (x + a) - cubicPolynomial g x a‖ ≤ M * ‖a‖ ^ 4 / 24 := by
  rw [sub_cubic_eq_integral x a hg, norm_mul]
  norm_num
  have hbound : ∀ᵐ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
      ‖(1-t)^3 * iteratedFDeriv ℝ 4 g (x+t•a) (fun _=>a)‖ ≤
        (1-t)^3 * (M * ‖a‖^4) := Filter.Eventually.of_forall (by
    intro t ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) 3)]
    exact mul_le_mul_of_nonneg_left (norm_fourth_apply_le (x+t•a) a (hM t ⟨ht.1.le,ht.2⟩))
      (pow_nonneg (sub_nonneg.mpr ht.2) 3))
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by norm_num : (0:ℝ)≤1)
    hbound ((by fun_prop : Continuous (fun t : ℝ => (1-t)^3 * (M*‖a‖^4))).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_mul_const, integral_cubic_kernel] at hi
  simp only [Real.norm_eq_abs] at hi
  linarith

/-- The genuine integral remainder has an integrable kernel along the segment. -/
theorem intervalIntegrable_remainder {g : E → ℝ} (x a : E)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 4 g (x + t • a)) :
    IntervalIntegrable (fun t : ℝ =>
      (1-t)^3 * iteratedFDeriv ℝ 4 g (x+t•a) (fun _=>a)) volume 0 1 := by
  have hc : ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 4 g (x+t•a) (fun _=>a))
      (uIcc (0 : ℝ) 1) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have h := ((hg t ht').iteratedFDeriv_right (i := 4) (m := 0) (by norm_num)).continuousAt
    exact (h.comp (x := t) (by fun_prop)).continuousWithinAt.eval_const _
  exact ((by fun_prop : Continuous (fun t : ℝ => (1-t)^3)).continuousOn.mul hc).intervalIntegrable

/-- Global C4 regularity supplies all segment regularity in the remainder bound. -/
theorem norm_sub_cubic_le_of_contDiff {g : E → ℝ} (hg : ContDiff ℝ 4 g) (x a : E)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 4 g (x + t • a)‖ ≤ M) :
    ‖g (x + a) - cubicPolynomial g x a‖ ≤ M * ‖a‖ ^ 4 / 24 :=
  norm_sub_cubic_le x a (fun _ _ => hg.contDiffAt) hM

/-- The actual cubic polynomial has the usual scaled-displacement coefficients. -/
theorem cubicPolynomial_smul (g : E → ℝ) (x a : E) (ε : ℝ) :
    cubicPolynomial g x (ε • a) = g x + ε * fderiv ℝ g x a +
      (ε^2 / 2) * iteratedFDeriv ℝ 2 g x (fun _=>a) +
      (ε^3 / 6) * iteratedFDeriv ℝ 3 g x (fun _=>a) := by
  simp [cubicPolynomial, ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  ring

/-- A fourth-derivative bound yields the explicit fourth-power scaled remainder. -/
theorem norm_sub_cubic_smul_le {g : E → ℝ} (x a : E) (ε : ℝ)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 4 g (x + t • (ε • a)))
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 4 g (x + t • (ε • a))‖ ≤ M) :
    ‖g (x + ε • a) - cubicPolynomial g x (ε • a)‖ ≤
      M * ε^4 * ‖a‖^4 / 24 := by
  have h := norm_sub_cubic_le x (ε • a) hg hM
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, pow_abs, abs_of_nonneg (by positivity : 0 ≤ ε^4), mul_assoc] using h

/-- A common weighted fourth-derivative bound controls the weighted remainder;
the bound may depend on the fixed density point supplying the weight. -/
theorem norm_weighted_sub_cubic_le {g : E → ℝ} (w : ℝ) (x a : E)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 4 g (x + t • a))
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      |w| * ‖iteratedFDeriv ℝ 4 g (x + t • a)‖ ≤ M) :
    ‖w * (g (x+a) - cubicPolynomial g x a)‖ ≤ M * ‖a‖^4 / 24 := by
  have hnonneg : 0 ≤ M :=
    (mul_nonneg (abs_nonneg w) (norm_nonneg _)).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  by_cases hw : w = 0
  · simp only [hw, zero_mul, norm_zero]
    positivity
  have hwpos : 0 < |w| := abs_pos.mpr hw
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ 4 g (x+t•a)‖ ≤ M / |w| := by
    intro t ht
    apply (le_div_iff₀ hwpos).2
    simpa only [mul_comm] using hM t ht
  calc
    _ = |w| * ‖g (x+a) - cubicPolynomial g x a‖ := by rw [norm_mul, Real.norm_eq_abs]
    _ ≤ |w| * ((M / |w|) * ‖a‖^4 / 24) :=
      mul_le_mul_of_nonneg_left (norm_sub_cubic_le x a hg hb) (abs_nonneg w)
    _ = _ := by field_simp

end FoliationQM.FourthOrderTaylor
