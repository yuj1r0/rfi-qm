module

public import FoliationQM.TestedRestEnvelopeRemainder
public import FoliationQM.WeakSchrodingerEquation
public import FoliationQM.ControlledRestEnvelopeLimit

/-!
# Weak limits of actual rest envelopes and KG sources

Source: v13 `cor:schrodinger`, kinds C and D. At fixed physical mass and
action scales, local L¹ convergence of the actual fields and their
phase-neutralized KG sources determines the limiting compact-test equation.
Moving the temporal derivatives onto a fixed smooth test leaves a finite
pairing multiplied by the actual vanishing temporal coefficient.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.WeakRestEnvelopeLimit

open Filter ScalarLocalTesting PolarSecondDifferential RestEnvelopeKG
open RestEnvelopeRemainder ControlledRestEnvelopeLimit
open Madelung (coordinateVector)
open scoped Topology

/-- At fixed mass and action scales, local L¹ limits of actual fields and their neutralized KG sources satisfy the weak Schrödinger equation as c diverges. -/
theorem weak_of_remainders (p : MassiveParameters)
    {P : ℕ → MassiveParameters} {U : Set Covector}
    {u : ℕ → Covector → ℂ} {v g : Covector → ℂ}
    (hU : IsOpen U) (hm : ∀ n, (P n).m = p.m)
    (hh : ∀ n, (P n).hbar = p.hbar)
    (hc : Tendsto (fun n => (P n).c) atTop atTop)
    (hu : ∀ n, ∀ x ∈ U, ContDiffAt ℝ 2 (u n) x)
    (hfields : LocalL1 U u v)
    (hsources : LocalL1 U (fun n => neutralizedKG (P n) (u n)) g) :
    WeakSchrodingerEquation.WeakEquation p v g U := by
  intro η hη hcompact hs
  have hL := tendsto_tested hU hfields
    (SchrodingerGreen.contDiff_residual_test p hη).continuous
    (SchrodingerGreen.compact_residual_test p η hcompact)
    ((SchrodingerGreen.tsupport_residual_subset p η).trans hs)
  have hN := tendsto_tested hU hsources hη.continuous hcompact hs
  have hT := tendsto_tested hU hfields
    (CompactComplexGreen.contDiff_second_test hη (coordinateVector 0)).continuous
    ((hcompact.fderiv_apply ℝ (coordinateVector 0)).fderiv_apply ℝ (coordinateVector 0))
    ((CompactComplexGreen.tsupport_second_subset η (coordinateVector 0)).trans hs)
  have hright : Tendsto
      (fun n => temporalCoefficient (P n) *
        tested U (secondDirectionalDerivative η (coordinateVector 0)) (u n))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_temporalCoefficient_of_fixed p hm hh hc).mul hT
  have he :
      (fun n => tested U (schrodingerResidual p η) (u n) +
        sourceCoefficient p * tested U η (neutralizedKG (P n) (u n))) =
      (fun n => temporalCoefficient (P n) *
        tested U (secondDirectionalDerivative η (coordinateVector 0)) (u n)) := by
    funext n
    have hn := TestedRestEnvelopeRemainder.tested_corrected (P n) hη (hu n) hcompact hs
    rw [residual_eq_of_scales p (P n) (hm n) (hh n)] at hn
    simpa only [sourceCoefficient, hm n] using hn
  apply tendsto_nhds_unique (hL.add (hN.const_mul (sourceCoefficient p)))
  rw [he]
  exact hright

end FoliationQM.WeakRestEnvelopeLimit
