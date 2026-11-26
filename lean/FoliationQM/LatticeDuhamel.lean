module

public import FoliationQM.LatticePropagatorUniqueness
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Duhamel formula and trajectory error for the finite Neumann evolution

Transporting an inhomogeneous Schrödinger solution to the terminal time
integrates the actual residual in the finite complex site space. The
unitary propagator preserves each instantaneous residual norm. Its time
integral bounds the error in the same-lattice comparison of v13 line 229.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeDuhamel

open LatticeUnitaryPropagator LatticePropagatorUniqueness MeasureTheory Set Filter

private theorem transport_continuous {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (b : ℝ) : Continuous (fun s => propagator p h V (b - s)) := by
  have hu : Continuous (propagator p h V) := continuous_iff_continuousAt.mpr
    fun t => (propagator_deriv_right p h V t).continuousAt
  exact hu.comp (continuous_const.sub continuous_id)

/-- Unitary transport of an interval-integrable forcing term is interval-integrable. -/
theorem transported_integrable {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (r : ℝ → Space n) {a b : ℝ} (hr : IntervalIntegrable r volume a b) :
    IntervalIntegrable (fun s => propagator p h V (b-s) (r s)) volume a b := by
  have hm := (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := Space n) (F := Space n)).continuous
    |>.comp_aestronglyMeasurable₂ (transport_continuous p h V b).aestronglyMeasurable
      hr.def'.aestronglyMeasurable
  apply (IntervalIntegrable.intervalIntegrable_norm_iff hm).mp
  simpa only [propagator_norm] using hr.norm

/-- The vector trajectory error equals the Bochner integral of the transported
residual, assuming integrability of the residual and the equation only in the interior. -/
theorem duhamel_integrable {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z r : ℝ → Space n) {a b : ℝ} (hab : a ≤ b) (hzc : ContinuousOn z (Icc a b))
    (hODE : ∀ s ∈ Ioo a b, HasDerivAt z (generator p h V (z s) + r s) s)
    (hr : IntervalIntegrable r volume a b) :
    z b - propagator p h V (b-a) (z a) = ∫ s in a..b, propagator p h V (b-s) (r s) := by
  have hc := (transport_continuous p h V b).continuousOn.clm_apply hzc
  have hd (s : ℝ) (hs : s ∈ Ioo a b) := transported_derivative p h V z b s (r s) (hODE s hs)
  simpa only [sub_self, propagator_zero, one_apply_eq_self] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd
      (transported_integrable p h V r hr)).symm

/-- For a residual continuous up to both endpoints, the Duhamel identity
requires no separate integrability hypothesis. -/
theorem duhamel {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z r : ℝ → Space n) {a b : ℝ} (hab : a ≤ b) (hzc : ContinuousOn z (Icc a b))
    (hODE : ∀ s ∈ Ioo a b, HasDerivAt z (generator p h V (z s) + r s) s)
    (hr : ContinuousOn r (Icc a b)) :
    z b - propagator p h V (b-a) (z a) = ∫ s in a..b, propagator p h V (b-s) (r s) :=
  duhamel_integrable p h V z r hab hzc hODE (hr.intervalIntegrable_of_Icc hab)

/-- Any integrable time-varying upper bound for the interior residual norm
bounds the trajectory error by its time integral. -/
theorem integral_bound {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z r : ℝ → Space n) (B : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (hzc : ContinuousOn z (Icc a b))
    (hODE : ∀ s ∈ Ioo a b, HasDerivAt z (generator p h V (z s) + r s) s)
    (hB : ∀ s ∈ Ioo a b, ‖r s‖ ≤ B s) (hBi : IntervalIntegrable B volume a b) :
    ‖z b - propagator p h V (b-a) (z a)‖ ≤ ∫ s in a..b, B s := by
  have hd (s : ℝ) (hs : s ∈ Ioo a b) := transported_derivative p h V z b s (r s) (hODE s hs)
  have he := norm_sub_le_integral_of_norm_deriv_le_of_le hab
    ((transport_continuous p h V b).continuousOn.clm_apply hzc)
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall fun s hs => by simpa only [(hd s hs).deriv, propagator_norm] using hB s hs) hBi
  simpa only [sub_self, propagator_zero, one_apply_eq_self] using he

/-- A uniform interior forcing bound accumulates at most linearly in elapsed time. -/
theorem uniform_bound {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z r : ℝ → Space n) (C : ℝ) {a b : ℝ} (hab : a ≤ b) (hzc : ContinuousOn z (Icc a b))
    (hODE : ∀ s ∈ Ioo a b, HasDerivAt z (generator p h V (z s) + r s) s)
    (hB : ∀ s ∈ Ioo a b, ‖r s‖ ≤ C) :
    ‖z b - propagator p h V (b-a) (z a)‖ ≤ C * (b-a) := by
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm C] using
    integral_bound p h V z r (fun _ => C) hab hzc hODE hB intervalIntegrable_const

/-- With different initial data, unitary propagation adds the initial discrepancy
with coefficient one to the integrated forcing bound. -/
theorem initial_data_bound {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z r : ℝ → Space n) (x : Space n) (B : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hzc : ContinuousOn z (Icc a b)) (hODE : ∀ s ∈ Ioo a b, HasDerivAt z (generator p h V (z s) + r s) s)
    (hB : ∀ s ∈ Ioo a b, ‖r s‖ ≤ B s) (hBi : IntervalIntegrable B volume a b) :
    ‖z b - propagator p h V (b-a) x‖ ≤ (∫ s in a..b, B s) + ‖z a - x‖ := by
  calc
    _ ≤ ‖z b - propagator p h V (b-a) (z a)‖ +
          ‖propagator p h V (b-a) (z a) - propagator p h V (b-a) x‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ _ := by rw [← map_sub, propagator_norm]; exact add_le_add_left (integral_bound p h V z r B hab hzc hODE hB hBi) _

end FoliationQM.LatticeDuhamel
