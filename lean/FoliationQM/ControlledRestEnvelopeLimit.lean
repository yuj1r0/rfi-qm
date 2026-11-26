module

public import FoliationQM.RestEnvelopeRemainder
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Controlled limits of actual rest envelopes

Source: v13 `cor:schrodinger`, kinds C and D. The physical mass and action
scales are fixed explicitly before passing to a limit of the actual
Schrödinger operator. Genuine homogeneous KG and a common temporal bound
give uniform residual decay when that bound grows subquadratically in c.
Actual first-time and spatial-second derivative convergence is a separate
hypothesis; it is never inferred from convergence of field values.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ControlledRestEnvelopeLimit

open Filter RestEnvelopeKG RestEnvelopeRemainder RestEnvelopeDifferential LaboratoryKG
open PolarSecondDifferential
open Madelung (coordinateVector)
open scoped Topology

/-- At fixed physical mass and action scales, the actual Schrödinger operator is independent of c. -/
theorem residual_eq_of_scales (p q : MassiveParameters)
    (hm : q.m = p.m) (hh : q.hbar = p.hbar) (u : Covector → ℂ) :
    schrodingerResidual q u = schrodingerResidual p u := by
  funext x
  simp only [schrodingerResidual, hm, hh]

/-- Convergence of the actual first-time and three spatial-second derivatives gives convergence of the same fixed operator. -/
theorem tendsto_residual (p : MassiveParameters) {u : ℕ → Covector → ℂ}
    {v : Covector → ℂ} {x : Covector}
    (ht : Tendsto (fun n => directionalDerivative (u n) (coordinateVector 0) x)
      atTop (𝓝 (directionalDerivative v (coordinateVector 0) x)))
    (hs : ∀ i : Fin 3, Tendsto
      (fun n => secondDirectionalDerivative (u n) (coordinateVector i.succ) x)
      atTop (𝓝 (secondDirectionalDerivative v (coordinateVector i.succ) x))) :
    Tendsto (fun n => schrodingerResidual p (u n) x)
      atTop (𝓝 (schrodingerResidual p v x)) := by
  have hΔ : Tendsto (fun n => spatialLaplacian (u n) x)
      atTop (𝓝 (spatialLaplacian v x)) :=
    tendsto_finsetSum Finset.univ (fun i _ => hs i)
  exact (ht.const_mul (Complex.I * (p.hbar : ℂ))).add
    (hΔ.const_mul ((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ))

/-- Diverging c makes the actual temporal coefficient vanish when mass and action scales stay fixed. -/
theorem tendsto_temporalCoefficient_of_fixed (p : MassiveParameters)
    {P : ℕ → MassiveParameters} (hm : ∀ n, (P n).m = p.m)
    (hh : ∀ n, (P n).hbar = p.hbar) (hc : Tendsto (fun n => (P n).c) atTop atTop) :
    Tendsto (fun n => temporalCoefficient (P n)) atTop (𝓝 0) := by
  have h := (hc.inv_tendsto_atTop.pow 2).const_mul (p.hbar ^ 2 / (2 * p.m))
  simpa only [temporalCoefficient, hm, hh, Pi.inv_apply, div_eq_mul_inv,
    mul_inv_rev, inv_pow, zero_pow two_ne_zero, mul_zero, zero_mul,
    mul_assoc, mul_comm, mul_left_comm] using h

/-- A genuinely subquadratic temporal bound makes its actual coefficient-weighted error tend to zero. -/
theorem tendsto_temporalCoefficient_mul_of_scaled (p : MassiveParameters)
    {P : ℕ → MassiveParameters} {M : ℕ → ℝ}
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hM : Tendsto (fun n => M n / (P n).c ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => temporalCoefficient (P n) * M n) atTop (𝓝 0) := by
  have h := hM.const_mul (p.hbar ^ 2 / (2 * p.m))
  simpa only [temporalCoefficient, hm, hh, div_eq_mul_inv, mul_inv_rev,
    mul_zero, zero_mul, mul_assoc, mul_comm, mul_left_comm] using h

/-- Actual KG and an eventual bound shared across the region give uniform residual decay under subquadratic temporal control. -/
theorem tendstoUniformlyOn_residual_of_scaled (p : MassiveParameters)
    {P : ℕ → MassiveParameters} {u : ℕ → Covector → ℂ} {K : Set Covector} {M : ℕ → ℝ}
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hreg : ∀ᶠ n in atTop, ∀ x ∈ K, ContDiffAt ℝ 2 (u n) x)
    (hKG : ∀ᶠ n in atTop, ∀ x ∈ K, laboratoryKG (P n) (dressedField (P n) (u n)) x = 0)
    (hbound : ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖secondDirectionalDerivative (u n) (coordinateVector 0) x‖ ≤ M n)
    (hM : Tendsto (fun n => M n / (P n).c ^ 2) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => schrodingerResidual p (u n)) (fun _ => 0) atTop K := by
  have hsmall := tendsto_temporalCoefficient_mul_of_scaled p hm hh hM
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hreg, hKG, hbound, hsmall.eventually_lt_const hε] with n hr hk hb he x hx
  have h := norm_residual_le_of_KG (P n) (hr x hx) (hb x hx) (hk x hx)
  rw [residual_eq_of_scales p (P n) (hm n) (hh n)] at h
  simpa only [dist_zero_left] using h.trans_lt he

/-- A fixed region-wide temporal bound and diverging c give uniform decay of the actual fixed Schrödinger residual. -/
theorem tendstoUniformlyOn_residual_of_bound (p : MassiveParameters)
    {P : ℕ → MassiveParameters} {u : ℕ → Covector → ℂ} {K : Set Covector} {M : ℝ}
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hreg : ∀ᶠ n in atTop, ∀ x ∈ K, ContDiffAt ℝ 2 (u n) x)
    (hKG : ∀ᶠ n in atTop, ∀ x ∈ K, laboratoryKG (P n) (dressedField (P n) (u n)) x = 0)
    (hbound : ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖secondDirectionalDerivative (u n) (coordinateVector 0) x‖ ≤ M) :
    TendstoUniformlyOn (fun n => schrodingerResidual p (u n)) (fun _ => 0) atTop K := by
  apply tendstoUniformlyOn_residual_of_scaled p hm hh hreg hKG hbound
  have h := (hc.inv_tendsto_atTop.pow 2).const_mul M
  simpa only [Pi.inv_apply, div_eq_mul_inv, inv_pow, zero_pow two_ne_zero, mul_zero] using h

end FoliationQM.ControlledRestEnvelopeLimit
