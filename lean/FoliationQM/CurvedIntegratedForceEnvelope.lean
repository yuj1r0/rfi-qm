module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Integrated force envelopes and eventual positive normalization

A fixed nonnegative coefficient times the actual gradient supremum gives
the force envelope used in the sufficient-condition bridge. Measurability
and interval integrability are tracked separately, and the integral
convergence theorem applies to an arbitrary asymptotic filter. Uniform
smallness of a bounded continuous scalar defect gives a lower bound for
one plus that defect only eventually along the filter, not at every index.
The physical application supplies the actual computed supremum functions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedIntegratedForceEnvelope

open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

variable {ι : Type*}

/-- The time-dependent force envelope obtained by multiplying a gradient-supremum family by a fixed coefficient. -/
def envelope (C : ℝ) (B : ι → ℝ → ℝ) (i : ι) (t : ℝ) : ℝ := C * B i t

/-- A nonnegative uniform coefficient and nonnegative gradient supremum give a pointwise nonnegative force envelope. -/
theorem envelope_nonneg {C : ℝ} {B : ι → ℝ → ℝ}
    (hC : 0 ≤ C) (hB : ∀ i t, 0 ≤ B i t) (i : ι) (t : ℝ) :
    0 ≤ envelope C B i t :=
  mul_nonneg hC (hB i t)

/-- A measurable actual gradient-supremum representative gives a measurable envelope representative. -/
theorem measurable_envelope (C : ℝ) {B : ι → ℝ → ℝ} {i : ι}
    (hB : Measurable (B i)) : Measurable (envelope C B i) :=
  hB.const_mul C

/-- Finite interval integrability of the actual gradient supremum gives finite interval integrability of its derived force envelope. -/
theorem intervalIntegrable_envelope (C : ℝ) {B : ι → ℝ → ℝ} {i : ι} {T : ℝ}
    (hB : IntervalIntegrable (B i) volume 0 T) :
    IntervalIntegrable (envelope C B i) volume 0 T :=
  hB.const_mul C

/-- The actual interval integral of the derived envelope is exactly the fixed coefficient times the gradient-supremum integral. -/
theorem integral_envelope (C : ℝ) (B : ι → ℝ → ℝ) (i : ι) (T : ℝ) :
    (∫ t in 0..T, envelope C B i t) = C * ∫ t in 0..T, B i t :=
  intervalIntegral.integral_const_mul C (B i)

/-- Convergence of the gradient-supremum integrals to zero gives convergence of the derived envelope integrals for any asymptotic filter. -/
theorem tendsto_integral_envelope (C : ℝ) {B : ι → ℝ → ℝ} {T : ℝ} {l : Filter ι}
    (hB : Tendsto (fun i => ∫ t in 0..T, B i t) l (𝓝 0)) :
    Tendsto (fun i => ∫ t in 0..T, envelope C B i t) l (𝓝 0) := by
  simpa only [integral_envelope, mul_zero] using hB.const_mul C

/-- Uniform convergence of a bounded continuous defect to zero gives the positive half-bound at every domain point eventually, including for an empty domain. -/
theorem eventually_half_le_one_add {Z : Type*} [TopologicalSpace Z]
    (Q : ι → Z →ᵇ ℝ) {l : Filter ι}
    (hQ : Tendsto (fun i => ‖Q i‖) l (𝓝 0)) :
    ∀ᶠ i in l, ∀ z : Z, (1 / 2 : ℝ) ≤ 1 + Q i z := by
  have hsmall : ∀ᶠ i in l, ‖Q i‖ < (1 / 2 : ℝ) :=
    hQ.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hsmall] with i hi
  intro z
  have hz := (Q i).neg_norm_le_apply z
  linarith

end FoliationQM.CurvedIntegratedForceEnvelope
