module

public import FoliationQM.WassersteinCoupling
public import FoliationQM.WeightedPhaseError
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Actual time suprema and uniform finite transport concentration

A common bound on the genuine coupling cost gives an actual real supremum
on the fixed nonempty time interval. Explicit finite-cost certificates
remain visible beside all real-valued estimates and limits. The limiting
family has an explicit filter, and its hypotheses may hold eventually.

These scalar aggregation lemmas are composed with proved trajectory
estimates in the source-facing modules. They do not replace dynamical
hypotheses by an assumed final concentration estimate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.UniformTransportConcentration

open MeasureTheory Set Filter WassersteinCoupling
open scoped Topology ENNReal

/-- The actual real supremum of a function's values on the fixed closed time interval. -/
def timeSup (q : ℝ → ℝ) (T : ℝ) : ℝ :=
  sSup (q '' Icc 0 T)

variable {q : ℝ → ℝ} {T B t : ℝ}

/-- A common interval bound bounds the actual supremum; nonemptiness follows from nonnegative final time. -/
theorem timeSup_le (hT : 0 ≤ T) (hbound : ∀ t ∈ Icc 0 T, q t ≤ B) :
    timeSup q T ≤ B := by
  have hn : (q '' Icc 0 T).Nonempty := ⟨q 0, 0, ⟨le_rfl, hT⟩, rfl⟩
  apply csSup_le hn
  rintro _ ⟨s, hs, rfl⟩
  exact hbound s hs

/-- Every interval value is below the actual supremum, using the proved common bound to establish boundedness. -/
theorem le_timeSup (hbound : ∀ t ∈ Icc 0 T, q t ≤ B) (ht : t ∈ Icc 0 T) :
    q t ≤ timeSup q T := by
  have hb : BddAbove (q '' Icc 0 T) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hbound s hs
  exact le_csSup hb ⟨t, ht, rfl⟩

/-- The actual bounded time supremum of nonnegative values is nonnegative on a nonempty interval. -/
theorem timeSup_nonneg (hT : 0 ≤ T) (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ q t)
    (hbound : ∀ t ∈ Icc 0 T, q t ≤ B) : 0 ≤ timeSup q T :=
  (hnonneg 0 ⟨le_rfl, hT⟩).trans (le_timeSup hbound ⟨le_rfl, hT⟩)

section Cost

variable {E : Type*} [MetricSpace E] [MeasurableSpace E]
  {ν : ℝ → Measure E} {Y : ℝ → E}

/-- An actual finite coupling-cost bound gives the source's real time supremum bound while retaining finiteness at every interval time. -/
theorem finite_cost_sup_bound (hT : 0 ≤ T)
    (h : ∀ t ∈ Icc 0 T, eW1 (ν t) (Measure.dirac (Y t)) ≠ ∞ ∧
      (eW1 (ν t) (Measure.dirac (Y t))).toReal ≤ B) :
    (∀ t ∈ Icc 0 T, eW1 (ν t) (Measure.dirac (Y t)) ≠ ∞) ∧
      0 ≤ timeSup (fun t => (eW1 (ν t) (Measure.dirac (Y t))).toReal) T ∧
      timeSup (fun t => (eW1 (ν t) (Measure.dirac (Y t))).toReal) T ≤ B := by
  have hb : ∀ t ∈ Icc 0 T, (eW1 (ν t) (Measure.dirac (Y t))).toReal ≤ B :=
    fun t ht => (h t ht).2
  exact ⟨fun t ht => (h t ht).1,
    timeSup_nonneg hT (fun _ _ => ENNReal.toReal_nonneg) hb, timeSup_le hT hb⟩

variable {ι : Type*} {ν : ι → ℝ → Measure E} {B : ι → ℝ}

/-- An eventual common bound tending to zero yields genuine finite costs eventually, uniform convergence on the fixed interval, and convergence of the actual time supremum. -/
theorem uniform_concentration_of_bound (l : Filter ι) (hT : 0 ≤ T)
    (h : ∀ᶠ i in l, ∀ t ∈ Icc 0 T, eW1 (ν i t) (Measure.dirac (Y t)) ≠ ∞ ∧
      (eW1 (ν i t) (Measure.dirac (Y t))).toReal ≤ B i)
    (hB : Tendsto B l (𝓝 0)) :
    (∀ᶠ i in l, ∀ t ∈ Icc 0 T, eW1 (ν i t) (Measure.dirac (Y t)) ≠ ∞) ∧
      TendstoUniformlyOn
        (fun i t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal)
        (fun _ => 0) l (Icc 0 T) ∧
      Tendsto (fun i => timeSup
        (fun t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal) T) l (𝓝 0) := by
  have hf : ∀ᶠ i in l, ∀ t ∈ Icc 0 T, eW1 (ν i t) (Measure.dirac (Y t)) ≠ ∞ :=
    h.mono fun i hi t ht => (hi t ht).1
  have hu : TendstoUniformlyOn
      (fun i t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal)
      (fun _ => 0) l (Icc 0 T) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [h, hB.eventually_lt_const hε] with i hi hBi t ht
    have hlt := ((hi t ht).2).trans_lt hBi
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg] using hlt
  have hlow : ∀ᶠ i in l, 0 ≤ timeSup
      (fun t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal) T :=
    h.mono fun _ hi => (finite_cost_sup_bound hT hi).2.1
  have hupp : ∀ᶠ i in l, timeSup
      (fun t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal) T ≤ B i :=
    h.mono fun _ hi => (finite_cost_sup_bound hT hi).2.2
  exact ⟨hf, hu, squeeze_zero' hlow hupp hB⟩

end Cost

/-- The explicit source coefficient is positive and independent of the asymptotic family. -/
theorem source_constant_pos (T Lx Lv : ℝ) :
    0 < Real.exp (WeightedPhaseError.rate T Lx Lv * T) :=
  Real.exp_pos _

/-- Vanishing actual position, velocity and integrated-force errors make the exact fixed-coefficient source majorant vanish along the supplied filter. -/
theorem source_majorant_tendsto {ι : Type*} (l : Filter ι) (T Lx Lv : ℝ)
    {dx db J : ι → ℝ}
    (hdx : Tendsto dx l (𝓝 0)) (hdb : Tendsto db l (𝓝 0))
    (hJ : Tendsto J l (𝓝 0)) :
    Tendsto (fun i => Real.exp (WeightedPhaseError.rate T Lx Lv * T) *
      (dx i + T * db i + T * J i)) l (𝓝 0) := by
  simpa only [mul_zero, add_zero] using
    ((hdx.add (hdb.const_mul T)).add (hJ.const_mul T)).const_mul
      (Real.exp (WeightedPhaseError.rate T Lx Lv * T))

end FoliationQM.UniformTransportConcentration
