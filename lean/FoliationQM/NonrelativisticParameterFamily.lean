module

public import FoliationQM.ReducedMassShellFrequency
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Fixed-scale nonrelativistic parameter families

Source: v13 `cor:schrodinger`, kinds C and D. An explicit positive physical
parameter sequence fixes the mass and action scales while c diverges. The
actual reduced mass-shell frequency converges uniformly on any spatial
frequency set with a common squared-speed bound. Field and derivative
convergence require the separate integral estimates for those fields.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.NonrelativisticParameterFamily

open Filter LorentzCoordinates ReducedMassShellFrequency
open scoped Topology

/-- An actual positive parameter sequence with fixed mass and action scales and c equal to its initial value plus n plus two. -/
def ramp (p : MassiveParameters) (n : ℕ) : MassiveParameters where
  c := p.c + (n : ℝ) + 2
  m := p.m
  hbar := p.hbar
  c_pos := by have := p.c_pos; positivity
  m_pos := p.m_pos
  hbar_pos := p.hbar_pos

/-- The explicit ramp preserves both physical scales, has c greater than one at every index, and tends to infinity. -/
theorem ramp_spec (p : MassiveParameters) :
    (∀ n, (ramp p n).m = p.m ∧ (ramp p n).hbar = p.hbar ∧
      (ramp p n).c = p.c + (n : ℝ) + 2 ∧ 1 < (ramp p n).c) ∧
      Tendsto (fun n => (ramp p n).c) atTop atTop := by
  constructor
  · intro n
    refine ⟨rfl, rfl, rfl, ?_⟩
    change 1 < p.c + (n : ℝ) + 2
    have := p.c_pos
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · exact tendsto_atTop_mono
      (fun n => by change (n : ℝ) ≤ p.c + (n : ℝ) + 2; linarith [p.c_pos])
      tendsto_natCast_atTop_atTop

/-- At fixed mass and action scales, diverging c gives uniform reduced-frequency convergence on any set with a common squared-speed bound. -/
theorem tendstoUniformlyOn_frequency (p : MassiveParameters)
    {P : ℕ → MassiveParameters} {K : Set Spatial} {Q : ℝ}
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hQ : 0 ≤ Q) (hbound : ∀ k ∈ K, speedSq k ≤ Q) :
    TendstoUniformlyOn (fun n => reducedFrequency (P n))
      (schrodingerFrequency p) atTop K := by
  have hsmall : Tendsto
      (fun n => p.hbar ^ 3 * Q ^ 2 / (8 * p.m ^ 3 * (P n).c ^ 2))
      atTop (𝓝 0) := by
    have h := (hc.inv_tendsto_atTop.pow 2).const_mul (p.hbar ^ 3 * Q ^ 2 / (8 * p.m ^ 3))
    simpa only [Pi.inv_apply, div_eq_mul_inv, mul_inv_rev, inv_pow,
      zero_pow two_ne_zero, mul_zero, zero_mul, mul_assoc, mul_comm, mul_left_comm] using h
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hsmall.eventually_lt_const hε] with n he k hk
  have hcmp := frequency_comparison (P n) k
  have hle : reducedFrequency (P n) k ≤ schrodingerFrequency p k := by
    simpa only [schrodingerFrequency, hm, hh] using hcmp.2.1
  have hgap : schrodingerFrequency p k - reducedFrequency (P n) k ≤
      p.hbar ^ 3 * (speedSq k) ^ 2 / (8 * p.m ^ 3 * (P n).c ^ 2) := by
    simpa only [schrodingerFrequency, hm, hh] using hcmp.2.2
  have hsq : (speedSq k) ^ 2 ≤ Q ^ 2 := by
    nlinarith [speedSq_nonneg k, hbound k hk]
  have hb : p.hbar ^ 3 * (speedSq k) ^ 2 / (8 * p.m ^ 3 * (P n).c ^ 2) ≤
      p.hbar ^ 3 * Q ^ 2 / (8 * p.m ^ 3 * (P n).c ^ 2) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (le_of_lt (pow_pos p.hbar_pos 3)))
      (by have := p.m_pos; have := (P n).c_pos; positivity)
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
  exact (hgap.trans hb).trans_lt he

end FoliationQM.NonrelativisticParameterFamily
