module

public import FoliationQM.ClockScaleLimits
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Clock lattices and the qualified dispersion-scale limit

Source: v13 rem:wkb_rates_tails, physical-scale clause. Kinds A and C.
A fixed positive-period lattice has an open gap. As positive periods tend to
zero, actual integer-floor lattice approximants converge uniformly to the
identity on the entire real line. For the physical parameters, divergence of
the dispersion ratio implies a vanishing clock period when widths are also
eventually bounded and the speed is common. A growing-width family at fixed
parameters disproves the implication from the ratio alone.

The dispersion-time conclusion is a scalar limit. Analytic wave spreading,
current transport and quantum-force estimates retain their separate inputs.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ClockLatticeScaleLimits
open Filter
open scoped Topology

/-- The actual lower integer-clock approximation to a real value. -/
def latticeApproximation (τ x : ℝ) : ℝ := (Int.floor (x / τ) : ℝ) * τ

/-- Every approximant is an actual integer multiple of the clock period. -/
theorem latticeApproximation_mem (τ x : ℝ) :
    latticeApproximation τ x ∈ AddSubgroup.zmultiples τ :=
  AddSubgroup.intCast_mul_mem_zmultiples τ (Int.floor (x / τ))

/-- The floor error lies between zero and one positive clock period. -/
theorem latticeApproximation_error {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    0 ≤ x - latticeApproximation τ x ∧ x - latticeApproximation τ x < τ := by
  have hlo := (le_div_iff₀ hτ).mp (Int.floor_le (x / τ))
  have hhi := (div_lt_iff₀ hτ).mp (Int.lt_floor_add_one (x / τ))
  unfold latticeApproximation
  constructor <;> nlinarith

/-- The distance estimate is uniform over the whole real line. -/
theorem latticeApproximation_dist_lt {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    dist x (latticeApproximation τ x) < τ := by
  rw [Real.dist_eq, abs_of_nonneg (latticeApproximation_error hτ x).1]
  exact (latticeApproximation_error hτ x).2

/-- Vanishing positive periods give genuine uniform lattice approximation. -/
theorem latticeApproximation_tendstoUniformly {I : Type*} {l : Filter I}
    {τ : I → ℝ} (hpos : ∀ i, 0 < τ i) (hzero : Tendsto τ l (𝓝 0)) :
    TendstoUniformly (fun i => latticeApproximation (τ i)) id l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hzero.eventually (eventually_lt_nhds hε)] with i hi x
  exact (latticeApproximation_dist_lt (hpos i) x).trans hi

/-- No fixed positive-period clock lattice is dense in the real line. -/
theorem fixed_lattice_not_dense {τ : ℝ} (hτ : 0 < τ) :
    ¬ Dense (AddSubgroup.zmultiples τ : Set ℝ) := by
  intro hdense
  rcases hdense.exists_between hτ with ⟨z, hz, hz0, hzτ⟩
  rcases AddSubgroup.mem_zmultiples_iff.mp hz with ⟨k, hk⟩
  have hk' : (k : ℝ) * τ = z := by simpa only [zsmul_eq_mul] using hk
  have hk0 : (0 : ℝ) < (k : ℝ) :=
    (mul_pos_iff_of_pos_right hτ).mp (by simpa only [hk'] using hz0)
  have hk1 : (k : ℝ) < 1 :=
    (mul_lt_mul_iff_left₀ hτ).mp (by simpa only [one_mul, hk'] using hzτ)
  have hi0 : (0 : ℤ) < k := by exact_mod_cast hk0
  have hi1 : k < (1 : ℤ) := by exact_mod_cast hk1
  exact (not_lt_of_ge (Int.add_one_le_iff.mpr hi0)) hi1

/-- The actual physical clock has a positive period and a nondense fixed lattice. -/
theorem physical_lattice_not_dense (p : MassiveParameters) :
    ¬ Dense (AddSubgroup.zmultiples p.period : Set ℝ) :=
  fixed_lattice_not_dense (ClockScales.period_pos p)

/-- The physical ratio governing the displayed dispersion time. -/
def dispersionRatio (p : MassiveParameters) (width : ℝ) : ℝ :=
  p.m * width ^ 2 / p.hbar

/-- The manuscript's dispersion-time scalar, twice the actual ratio. -/
def dispersionTime (p : MassiveParameters) (width : ℝ) : ℝ :=
  2 * dispersionRatio p width

/-- The exact product identity is valid even at zero width; it divides by no width. -/
theorem period_mul_dispersionRatio (p : MassiveParameters) (width : ℝ) :
    p.period * dispersionRatio p width = (2 * Real.pi / p.c ^ 2) * width ^ 2 := by
  unfold MassiveParameters.period dispersionRatio
  field_simp [p.m_pos.ne', p.hbar_pos.ne', p.c_pos.ne']

/-- Diverging dispersion ratio makes the fixed observation-time ratio vanish. -/
theorem observation_div_dispersionTime_tendsto_zero {I : Type*} {l : Filter I}
    (P : I → MassiveParameters) (width : I → ℝ) (T : ℝ)
    (hratio : Tendsto (fun i => dispersionRatio (P i) (width i)) l atTop) :
    Tendsto (fun i => T / dispersionTime (P i) (width i)) l (𝓝 0) := by
  have h := hratio.inv_tendsto_atTop.const_mul (T / 2)
  simpa only [dispersionTime, div_eq_mul_inv, mul_inv_rev, Pi.inv_apply,
    mul_zero, zero_mul, mul_assoc, mul_comm, mul_left_comm] using h

/-- At common speed, bounded widths and diverging ratio force the actual period to zero. -/
theorem period_tendsto_zero_of_bounded_width {I : Type*} {l : Filter I}
    (P : I → MassiveParameters) (width : I → ℝ) (c B : ℝ)
    (hc : ∀ i, (P i).c = c) (hB : 0 ≤ B)
    (hwidth : ∀ᶠ i in l, |width i| ≤ B)
    (hratio : Tendsto (fun i => dispersionRatio (P i) (width i)) l atTop) :
    Tendsto (fun i => (P i).period) l (𝓝 0) := by
  let C : ℝ := 2 * Real.pi / c ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : Tendsto
      (fun i => C * B ^ 2 / dispersionRatio (P i) (width i)) l (𝓝 0) := by
    simpa only [div_eq_mul_inv, Pi.inv_apply, mul_zero] using
      hratio.inv_tendsto_atTop.const_mul (C * B ^ 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound (Eventually.of_forall fun i => (ClockScales.period_pos (P i)).le)
  filter_upwards [hwidth, hratio.eventually (eventually_ge_atTop 1)] with i hi hri
  have hri0 : 0 < dispersionRatio (P i) (width i) := lt_of_lt_of_le zero_lt_one hri
  have hsquare : width i ^ 2 ≤ B ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg hB] using hi)
  have hproduct := period_mul_dispersionRatio (P i) (width i)
  rw [hc i] at hproduct
  apply (le_div_iff₀ hri0).mpr
  rw [hproduct]
  exact mul_le_mul_of_nonneg_left hsquare hC

/-- A narrowing width is a sufficient bounded-width regime for the period limit. -/
theorem period_tendsto_zero_of_width_tendsto_zero {I : Type*} {l : Filter I}
    (P : I → MassiveParameters) (width : I → ℝ) (c : ℝ)
    (hc : ∀ i, (P i).c = c) (hwidth : Tendsto width l (𝓝 0))
    (hratio : Tendsto (fun i => dispersionRatio (P i) (width i)) l atTop) :
    Tendsto (fun i => (P i).period) l (𝓝 0) := by
  have ha : Tendsto (fun i => |width i|) l (𝓝 0) := by simpa using hwidth.abs
  apply period_tendsto_zero_of_bounded_width P width c 1 hc zero_le_one _ hratio
  exact (ha.eventually (eventually_lt_nhds zero_lt_one)).mono fun _ hi => hi.le

/-- Actual vanishing clock periods give uniform approximation by their clock lattices. -/
theorem physical_lattice_tendstoUniformly {I : Type*} {l : Filter I}
    (P : I → MassiveParameters) (hperiod : Tendsto (fun i => (P i).period) l (𝓝 0)) :
    TendstoUniformly (fun i => latticeApproximation (P i).period) id l :=
  latticeApproximation_tendstoUniformly (fun i => ClockScales.period_pos (P i)) hperiod

/-- The qualified physical scale regime yields the actual uniform lattice limit. -/
theorem physical_lattice_limit_of_bounded_width {I : Type*} {l : Filter I}
    (P : I → MassiveParameters) (width : I → ℝ) (c B : ℝ)
    (hc : ∀ i, (P i).c = c) (hB : 0 ≤ B)
    (hwidth : ∀ᶠ i in l, |width i| ≤ B)
    (hratio : Tendsto (fun i => dispersionRatio (P i) (width i)) l atTop) :
    TendstoUniformly (fun i => latticeApproximation (P i).period) id l :=
  physical_lattice_tendstoUniformly P
    (period_tendsto_zero_of_bounded_width P width c B hc hB hwidth hratio)

/-- Positive growing widths at fixed physical parameters refute the ratio-only period implication. -/
theorem growing_width_counterexample (p : MassiveParameters) :
    (∀ n : ℕ, 0 < (n : ℝ) + 1) ∧
    Tendsto (fun n : ℕ => dispersionRatio p ((n : ℝ) + 1)) atTop atTop ∧
    ¬ Tendsto (fun _ : ℕ => p.period) atTop (𝓝 0) := by
  refine ⟨fun n => by positivity, ?_, ?_⟩
  · have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using!
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
          (tendsto_add_atTop_nat 1)
    have hs := (tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num)).comp hn
    exact Filter.Tendsto.atTop_div_const p.hbar_pos
      (Filter.Tendsto.const_mul_atTop p.m_pos hs)
  · intro hzero
    exact (ClockScales.period_pos p).ne' (tendsto_nhds_unique tendsto_const_nhds hzero)

end FoliationQM.ClockLatticeScaleLimits
