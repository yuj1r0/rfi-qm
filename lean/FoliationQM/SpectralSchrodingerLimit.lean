module

public import FoliationQM.SpectralEnvelopeEstimates
public import FoliationQM.SpectralRestEnvelope
public import FoliationQM.KleinGordonSchrodingerLimit

/-!
# The controlled limit of one fixed spectral Klein–Gordon family

Source: v13 `cor:schrodinger`, component kinds C and D. One continuous
amplitude with genuine polynomial moments is held fixed while the speed
parameter diverges and mass and action scale remain fixed. Actual spectral
estimates supply compact-uniform field and derivative convergence and a
common temporal bound. The original KG family then enters the controlled
source theorem, giving local L¹ convergence and the actual limiting PDE.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SpectralSchrodingerLimit

open Filter Set LorentzCoordinates PolarSecondDifferential
open ReducedMassShellFrequency PolynomialSpectralMoments
open RestEnvelopeKG LaboratoryKG SpectralEnvelopeEstimates
open Madelung (coordinateVector)
open scoped Topology ContDiff

private theorem uniform_of_inverse_sq_bound {P : ℕ → MassiveParameters}
    {F : ℕ → Covector → ℂ} {f : Covector → ℂ} {K : Set Covector} {M : ℝ}
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hbound : ∀ n, ∀ x ∈ K, ‖F n x - f x‖ ≤ M / (P n).c ^ 2) :
    TendstoUniformlyOn F f atTop K := by
  have hsmall : Tendsto (fun n => M / (P n).c ^ 2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow, Pi.inv_apply] using
      (hc.inv_tendsto_atTop.pow 2).const_mul M
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hsmall.eventually_lt_const hε] with n hn
  intro x hx
  rw [dist_eq_norm, norm_sub_rev]
  exact (hbound n x hx).trans_lt hn

/-- One fixed spectrum gives compact-uniform convergence of the actual KG envelopes and their time and spatial derivatives, with a common genuine second-time bound. -/
theorem compact_convergence (p : MassiveParameters) {P : ℕ → MassiveParameters}
    {A : Spatial → ℂ} (hA : Continuous A) (hpoly : PolynomialMoments A)
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop) :
    let ψ := fun n => MassShellFourier.wave ((P n).m * (P n).c / (P n).hbar) A
    let u := FrequencyGraphFourier.wave (schrodingerFrequency p) A
    (∀ K : Set Covector, IsCompact K →
      TendstoUniformlyOn (fun n => envelope (P n) (ψ n)) u atTop K ∧
      TendstoUniformlyOn
        (fun n => directionalDerivative (envelope (P n) (ψ n)) (coordinateVector 0))
        (directionalDerivative u (coordinateVector 0)) atTop K ∧
      ∀ i : Fin 3, TendstoUniformlyOn
        (fun n => secondDirectionalDerivative (envelope (P n) (ψ n)) (coordinateVector i.succ))
        (secondDirectionalDerivative u (coordinateVector i.succ)) atTop K) ∧
    0 ≤ (p.hbar / (2 * p.m)) ^ 2 * moment A 2 ∧
    ∀ n x, ‖secondDirectionalDerivative (envelope (P n) (ψ n)) (coordinateVector 0) x‖ ≤
      (p.hbar / (2 * p.m)) ^ 2 * moment A 2 := by
  dsimp only
  have hfreq (n : ℕ) : schrodingerFrequency (P n) = schrodingerFrequency p := by
    funext k
    simp only [schrodingerFrequency, hm n, hh n]
  have he (n : ℕ) := (SpectralRestEnvelope.source_data (P n) hA hpoly).2.2
  refine ⟨?_, (time_second_bound p hA hpoly).1, ?_⟩
  · intro K hK
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_apply 0).continuousOn
    let T : ℝ := max 0 B
    have hT : 0 ≤ T := le_max_left _ _
    have hx : ∀ x ∈ K, |x 0| ≤ T := by
      intro x hmem
      have hb : |x 0| ≤ B := by simpa only [Real.norm_eq_abs] using hB x hmem
      exact hb.trans (le_max_right _ _)
    refine ⟨?_, ?_, ?_⟩
    · apply uniform_of_inverse_sq_bound hc
        (M := T * (p.hbar ^ 3 / (8 * p.m ^ 3)) * moment A 2)
      intro n x hmem
      rw [he n]
      simpa only [hfreq n, hm n, hh n] using field_gap (P n) hA hpoly hT (hx x hmem)
    · apply uniform_of_inverse_sq_bound hc
        (M := (p.hbar ^ 3 / (8 * p.m ^ 3)) *
          (moment A 2 + T * (p.hbar / (2 * p.m)) * moment A 3))
      intro n x hmem
      rw [he n]
      simpa only [hfreq n, hm n, hh n] using time_first_gap (P n) hA hpoly hT (hx x hmem)
    · intro i
      apply uniform_of_inverse_sq_bound hc
        (M := T * (p.hbar ^ 3 / (8 * p.m ^ 3)) * moment A 3)
      intro n x hmem
      rw [he n]
      simpa only [hfreq n, hm n, hh n] using
        spatial_second_gap (P n) hA hpoly hT (hx x hmem) i
  · intro n x
    rw [he n]
    simpa only [hm n, hh n] using (time_second_bound (P n) hA hpoly).2 x

/-- The same original spectral KG family satisfies the controlled source limit: genuine local L¹ convergence, compact-uniform residual decay and the classical Schrödinger equation for its smooth limit. -/
theorem source_limit (p : MassiveParameters) {P : ℕ → MassiveParameters}
    {A : Spatial → ℂ} (hA : Continuous A) (hpoly : PolynomialMoments A)
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop) :
    let ψ := fun n => MassShellFourier.wave ((P n).m * (P n).c / (P n).hbar) A
    let u := FrequencyGraphFourier.wave (schrodingerFrequency p) A
    ContDiff ℝ ∞ u ∧
    ScalarLocalTesting.LocalL1 univ (fun n => envelope (P n) (ψ n)) u ∧
    (∀ K : Set Covector, IsCompact K →
      TendstoUniformlyOn (fun n => schrodingerResidual p (envelope (P n) (ψ n)))
        (fun _ => 0) atTop K) ∧
    ∀ x, Complex.I * (p.hbar : ℂ) * directionalDerivative u (coordinateVector 0) x =
      -(((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ) * spatialLaplacian u x) := by
  dsimp only
  have hconv := compact_convergence p hA hpoly hm hh hc
  have hu := (SpectralRestEnvelope.schrodinger_wave p hA hpoly).1
  have hsource := KleinGordonSchrodingerLimit.source_classical_limit_of_bound
    (U := univ) p hm hh hc
    (fun n _ _ => (SpectralRestEnvelope.source_data (P n) hA hpoly).1.contDiffAt.of_le
      (by norm_num))
    (fun n x _ => (SpectralRestEnvelope.source_data (P n) hA hpoly).2.1
      (LaboratoryCoordinates.toNormal (P n).c x))
    (fun _ _ => hu.contDiffAt.of_le (by norm_num))
    (fun K hK _ => (hconv.1 K hK).1)
    (fun K hK _ => (hconv.1 K hK).2.1)
    (fun i K hK _ => (hconv.1 K hK).2.2 i)
    (fun _ _ _ => ⟨_, hconv.2.1, Eventually.of_forall fun n x _ => hconv.2.2 n x⟩)
  exact ⟨hu, hsource.1, fun K hK => hsource.2.1 K hK (subset_univ K),
    fun x => (hsource.2.2 x (mem_univ x)).2⟩

end FoliationQM.SpectralSchrodingerLimit
