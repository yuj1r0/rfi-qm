module

public import FoliationQM.WeakRestEnvelopeLimit

/-!
# Weak Schrödinger limits of actual Klein–Gordon fields

Source: v13 `cor:schrodinger`, component kinds C and D. The same physical
rest envelopes and genuinely phase-neutralized original KG sources converge
in local L¹ on a fixed open region. Compact testing gives the weak limiting
equation without bounds or convergence of the envelope derivatives. Actual
regularity of the limit is required separately for a classical equation.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.KleinGordonWeakLimit

open MeasureTheory Filter Set ScalarLocalTesting PolarSecondDifferential
open LaboratoryCoordinates LaboratoryKG RestEnvelopeDifferential
open RestEnvelopeKG RestEnvelopeRemainder WeakSchrodingerEquation
open Madelung (coordinateVector)
open scoped Topology ContDiff

variable {P : ℕ → MassiveParameters} {ψ : ℕ → Covector → ℂ}
variable {u g : Covector → ℂ} {U : Set Covector}

private theorem localL1_congr {F G : ℕ → Covector → ℂ} {f : Covector → ℂ}
    (h : LocalL1 U F f) (he : ∀ n, ∀ x ∈ U, F n x = G n x) : LocalL1 U G f := by
  intro K hK hs
  obtain ⟨hi, hf, ht⟩ := h K hK hs
  have hae (n : ℕ) : F n =ᵐ[volume.restrict K] G n := by
    filter_upwards [ae_restrict_mem (μ := volume) hK.measurableSet] with x hx
    exact he n x (hs hx)
  refine ⟨fun n => (hi n).congr (hae n), hf, ?_⟩
  have hseq : (fun n => ∫ x in K, ‖G n x - f x‖) =
      (fun n => ∫ x in K, ‖F n x - f x‖) := by
    funext n
    apply integral_congr_ae
    filter_upwards [hae n] with x hx
    rw [hx]
  rwa [hseq]

/-- Local L¹ convergence of actual rest envelopes and phase-neutralized original KG sources
gives the weak Schrödinger equation for the same limiting field and source. -/
theorem source_weak_limit (p : MassiveParameters) (hU : IsOpen U)
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hψ : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (ψ n) (toNormal (P n).c x))
    (hfield : LocalL1 U (fun n => envelope (P n) (ψ n)) u)
    (hsource : LocalL1 U (fun n x => (carrierField (P n) x)⁻¹ *
      FlatIntegrationByParts.kgOperator (P n) (ψ n) coordinateVector
        (toNormal (P n).c x)) g) :
    WeakEquation p u g U := by
  apply WeakRestEnvelopeLimit.weak_of_remainders p hU hm hh hc
    (fun n x hx => contDiffAt_envelope (P n) (hψ n x hx)) hfield
  apply localL1_congr hsource
  intro n x hx
  change _ = (carrierField (P n) x)⁻¹ *
    laboratoryKG (P n) (dressedField (P n) (envelope (P n) (ψ n))) x
  rw [dressedField_envelope, laboratoryKG_pullback (P n) (hψ n x hx)]

/-- When the actual weak limit is C² and its limiting source is continuous, the same
source-family limit satisfies the classical equation with the negative source term. -/
theorem source_classical_limit (p : MassiveParameters) (hU : IsOpen U)
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hψ : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (ψ n) (toNormal (P n).c x))
    (hfield : LocalL1 U (fun n => envelope (P n) (ψ n)) u)
    (hsource : LocalL1 U (fun n x => (carrierField (P n) x)⁻¹ *
      FlatIntegrationByParts.kgOperator (P n) (ψ n) coordinateVector
        (toNormal (P n).c x)) g)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hg : ContinuousOn g U) :
    ∀ x ∈ U, schrodingerResidual p u x = -(sourceCoefficient p : ℂ) * g x := by
  have h := classical_of_weak p hU hu hg
    (source_weak_limit p hU hm hh hc hψ hfield hsource)
  intro x hx
  simpa only [neg_mul] using eq_neg_of_add_eq_zero_left (h x hx)

/-- An actual homogeneous original KG family needs only local L¹ convergence of its rest
envelopes: the zero-source convergence is derived from the original equations. -/
theorem source_weak_limit_of_KG (p : MassiveParameters) (hU : IsOpen U)
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hψ : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (ψ n) (toNormal (P n).c x))
    (hKG : ∀ n, ∀ x ∈ U,
      FlatIntegrationByParts.kgOperator (P n) (ψ n) coordinateVector
        (toNormal (P n).c x) = 0)
    (hfield : LocalL1 U (fun n => envelope (P n) (ψ n)) u) :
    WeakEquation p u (fun _ => 0) U := by
  apply source_weak_limit p hU hm hh hc hψ hfield
  have hz : LocalL1 U (fun _ _ => (0 : ℂ)) (fun _ => 0) := by
    intro K _ _
    refine ⟨fun _ => integrable_zero _ _ _, integrable_zero _ _ _, ?_⟩
    simp
  apply localL1_congr hz
  intro n x hx
  simp [hKG n x hx]

/-- A C² local L¹ limit of the same original homogeneous KG rest envelopes satisfies the
literal physical Schrödinger PDE, without assumptions on approximating derivative limits. -/
theorem source_classical_limit_of_KG (p : MassiveParameters) (hU : IsOpen U)
    (hm : ∀ n, (P n).m = p.m) (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hψ : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (ψ n) (toNormal (P n).c x))
    (hKG : ∀ n, ∀ x ∈ U,
      FlatIntegrationByParts.kgOperator (P n) (ψ n) coordinateVector
        (toNormal (P n).c x) = 0)
    (hfield : LocalL1 U (fun n => envelope (P n) (ψ n)) u)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) :
    ∀ x ∈ U,
      Complex.I * (p.hbar : ℂ) * directionalDerivative u (coordinateVector 0) x =
        -(((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ) * spatialLaplacian u x) := by
  have h := classical_of_weak p hU hu continuousOn_const
    (source_weak_limit_of_KG p hU hm hh hc hψ hKG hfield)
  intro x hx
  have he : schrodingerResidual p u x = 0 := by simpa only [mul_zero, add_zero] using h x hx
  exact eq_neg_of_add_eq_zero_left he

end FoliationQM.KleinGordonWeakLimit
