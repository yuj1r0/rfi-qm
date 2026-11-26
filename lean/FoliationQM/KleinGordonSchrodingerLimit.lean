module

public import FoliationQM.ControlledRestEnvelopeLimit
public import FoliationQM.ScalarLocalTesting

/-!
# The controlled Schrödinger limit of actual Klein–Gordon fields

Source: v13 `cor:schrodinger`, kinds C and D. All fields are compared on one
physical spacetime region. The original normal-coordinate KG equations and
actual rest envelopes supply the finite-parameter equations. Actual field
convergence yields genuine local L¹ convergence; separate convergence of
the actual time and spatial derivatives identifies the limiting operator.
Temporal bounds give the residual decay, rather than assuming that decay or
the limiting PDE. No global real phase or nonvanishing wave is required.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.KleinGordonSchrodingerLimit

open Filter Set LaboratoryCoordinates LaboratoryKG RestEnvelopeDifferential
open RestEnvelopeKG PolarSecondDifferential
open Madelung (coordinateVector)
open scoped Topology ContDiff

variable {P : ℕ → MassiveParameters} {ψ : ℕ → Covector → ℂ}
variable {u : Covector → ℂ} {U K : Set Covector}

/-- Original KG, actual envelope derivatives and a shared subquadratic bound give uniform
decay of the same fixed physical Schrödinger residual on any comparison set. -/
theorem source_residual_uniform_of_subquadratic (p : MassiveParameters)
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    {M : ℕ → ℝ}
    (hψ : ∀ᶠ n in atTop, ∀ x ∈ K, ContDiffAt ℝ 2 (ψ n) (toNormal (P n).c x))
    (hKG : ∀ᶠ n in atTop, ∀ x ∈ K,
      FlatIntegrationByParts.kgOperator (P n) (ψ n) coordinateVector
        (toNormal (P n).c x) = 0)
    (hbound : ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖secondDirectionalDerivative (envelope (P n) (ψ n)) (coordinateVector 0) x‖ ≤ M n)
    (hscaled : Tendsto (fun n => M n / (P n).c ^ 2) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => schrodingerResidual p (envelope (P n) (ψ n)))
      (fun _ => 0) atTop K := by
  apply ControlledRestEnvelopeLimit.tendstoUniformlyOn_residual_of_scaled p hm hh
    ?_ ?_ hbound hscaled
  · filter_upwards [hψ] with n hn
    intro x hx
    exact contDiffAt_envelope (P n) (hn x hx)
  · filter_upwards [hψ, hKG] with n hn he
    intro x hx
    rw [dressedField_envelope, laboratoryKG_pullback (P n) (hn x hx)]
    exact he x hx

/-- Actual compact-uniform field and derivative convergence, with subquadratic temporal
control, gives local L¹ convergence and the classical Schrödinger PDE for that same field. -/
theorem source_classical_limit_of_subquadratic (p : MassiveParameters)
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hψ : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (ψ n) (toNormal (P n).c x))
    (hKG : ∀ n, ∀ x ∈ U,
      FlatIntegrationByParts.kgOperator (P n) (ψ n) coordinateVector
        (toNormal (P n).c x) = 0)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hfield : ∀ K : Set Covector, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n => envelope (P n) (ψ n)) u atTop K)
    (hfirst : ∀ K : Set Covector, IsCompact K → K ⊆ U →
      TendstoUniformlyOn
        (fun n => directionalDerivative (envelope (P n) (ψ n)) (coordinateVector 0))
        (directionalDerivative u (coordinateVector 0)) atTop K)
    (hsecond : ∀ i : Fin 3, ∀ K : Set Covector, IsCompact K → K ⊆ U →
      TendstoUniformlyOn
        (fun n => secondDirectionalDerivative (envelope (P n) (ψ n)) (coordinateVector i.succ))
        (secondDirectionalDerivative u (coordinateVector i.succ)) atTop K)
    (hcontrol : ∀ K : Set Covector, IsCompact K → K ⊆ U → ∃ M : ℕ → ℝ,
      (∀ᶠ n in atTop, ∀ x ∈ K,
        ‖secondDirectionalDerivative (envelope (P n) (ψ n)) (coordinateVector 0) x‖ ≤ M n) ∧
      Tendsto (fun n => M n / (P n).c ^ 2) atTop (𝓝 0)) :
    ScalarLocalTesting.LocalL1 U (fun n => envelope (P n) (ψ n)) u ∧
      (∀ K : Set Covector, IsCompact K → K ⊆ U →
        TendstoUniformlyOn (fun n => schrodingerResidual p (envelope (P n) (ψ n)))
          (fun _ => 0) atTop K) ∧
      ∀ x ∈ U, ContDiffAt ℝ 2 u x ∧
        Complex.I * (p.hbar : ℂ) * directionalDerivative u (coordinateVector 0) x =
          -(((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ) * spatialLaplacian u x) := by
  have hR : ∀ K : Set Covector, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n => schrodingerResidual p (envelope (P n) (ψ n)))
        (fun _ => 0) atTop K := by
    intro K hK hs
    obtain ⟨M, hbound, hscaled⟩ := hcontrol K hK hs
    exact source_residual_uniform_of_subquadratic p hm hh
      (Eventually.of_forall fun n x hx => hψ n x (hs hx))
      (Eventually.of_forall fun n x hx => hKG n x (hs hx)) hbound hscaled
  refine ⟨ScalarLocalTesting.of_locally_uniform
    (fun n x hx => (contDiffAt_envelope (P n) (hψ n x hx)).continuousAt)
    (fun x hx => (hu x hx).continuousAt) hfield, hR, ?_⟩
  intro x hx
  have hs : ({x} : Set Covector) ⊆ U := singleton_subset_iff.mpr hx
  have ht := (hfirst {x} isCompact_singleton hs).tendsto_at (mem_singleton x)
  have hsp (i : Fin 3) :=
    (hsecond i {x} isCompact_singleton hs).tendsto_at (mem_singleton x)
  have hlim := ControlledRestEnvelopeLimit.tendsto_residual p ht hsp
  have hzero := (hR {x} isCompact_singleton hs).tendsto_at (mem_singleton x)
  have he : schrodingerResidual p u x = 0 := tendsto_nhds_unique hlim hzero
  exact ⟨hu x hx, eq_neg_of_add_eq_zero_left he⟩

/-- A common temporal bound on each compact region and c tending to infinity supply
the subquadratic control and hence the genuine source-family Schrödinger limit. -/
theorem source_classical_limit_of_bound (p : MassiveParameters)
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hψ : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (ψ n) (toNormal (P n).c x))
    (hKG : ∀ n, ∀ x ∈ U,
      FlatIntegrationByParts.kgOperator (P n) (ψ n) coordinateVector
        (toNormal (P n).c x) = 0)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hfield : ∀ K : Set Covector, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n => envelope (P n) (ψ n)) u atTop K)
    (hfirst : ∀ K : Set Covector, IsCompact K → K ⊆ U →
      TendstoUniformlyOn
        (fun n => directionalDerivative (envelope (P n) (ψ n)) (coordinateVector 0))
        (directionalDerivative u (coordinateVector 0)) atTop K)
    (hsecond : ∀ i : Fin 3, ∀ K : Set Covector, IsCompact K → K ⊆ U →
      TendstoUniformlyOn
        (fun n => secondDirectionalDerivative (envelope (P n) (ψ n)) (coordinateVector i.succ))
        (secondDirectionalDerivative u (coordinateVector i.succ)) atTop K)
    (hcontrol : ∀ K : Set Covector, IsCompact K → K ⊆ U → ∃ M : ℝ, 0 ≤ M ∧
      (∀ᶠ n in atTop, ∀ x ∈ K,
        ‖secondDirectionalDerivative (envelope (P n) (ψ n)) (coordinateVector 0) x‖ ≤ M)) :
    ScalarLocalTesting.LocalL1 U (fun n => envelope (P n) (ψ n)) u ∧
      (∀ K : Set Covector, IsCompact K → K ⊆ U →
        TendstoUniformlyOn (fun n => schrodingerResidual p (envelope (P n) (ψ n)))
          (fun _ => 0) atTop K) ∧
      ∀ x ∈ U, ContDiffAt ℝ 2 u x ∧
        Complex.I * (p.hbar : ℂ) * directionalDerivative u (coordinateVector 0) x =
          -(((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ) * spatialLaplacian u x) := by
  apply source_classical_limit_of_subquadratic p hm hh hψ hKG hu hfield hfirst hsecond
  intro K hK hs
  obtain ⟨M, _, hbound⟩ := hcontrol K hK hs
  refine ⟨fun _ => M, hbound, ?_⟩
  simpa [div_eq_mul_inv, inv_pow, Pi.inv_apply] using
    (hc.inv_tendsto_atTop.pow 2).const_mul M

end FoliationQM.KleinGordonSchrodingerLimit
