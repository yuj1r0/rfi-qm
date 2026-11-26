module

public import FoliationQM.SchrodingerGreen
public import FoliationQM.RestEnvelopeRemainder
public import FoliationQM.ScalarLocalTesting

/-!
# Weak and classical equations for the physical Schrödinger operator

Source: v13 `cor:schrodinger`, component kinds C and D. The compact-tested
equation retains the real coefficient of the phase-neutralized KG source.
For a locally C² field and continuous source, genuine integrability of both
test products and the actual Green identity identify this equation with the
pointwise PDE. No derivative convergence or finite background action is used.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.WeakSchrodingerEquation

open MeasureTheory ScalarLocalTesting RestEnvelopeKG RestEnvelopeRemainder
open scoped ContDiff ComplexConjugate

/-- The real compact-tested Schrödinger equation with the actual phase-neutralized source coefficient. -/
def WeakEquation (p : MassiveParameters) (u g : Covector → ℂ)
    (U : Set Covector) : Prop :=
  ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
    tested U (schrodingerResidual p η) u + sourceCoefficient p * tested U η g = 0

private theorem tested_forcing (p : MassiveParameters) {U : Set Covector}
    {η u g : Covector → ℂ} (hη : ContDiff ℝ ∞ η)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hg : ContinuousOn g U)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    tested U η (fun x => schrodingerResidual p u x + (sourceCoefficient p : ℂ) * g x) =
      tested U (schrodingerResidual p η) u + sourceCoefficient p * tested U η g := by
  have hL : IntegrableOn (fun x => (conj (η x) * schrodingerResidual p u x).re) U := by
    simpa only [RCLike.re_eq_complex_re] using
      ((SchrodingerGreen.integrable_pairings p hη hu hc hs).1.integrableOn (s := U)).re
  have hG : IntegrableOn (fun x => (conj (η x) * g x).re) U := by
    simpa only [RCLike.re_eq_complex_re] using
      ((OpenFundamentalLemma.integrable_test_pairing hg hη.continuous hc hs).integrableOn
        (s := U)).re
  have he (x : Covector) :
      (conj (η x) * (schrodingerResidual p u x + (sourceCoefficient p : ℂ) * g x)).re =
        (conj (η x) * schrodingerResidual p u x).re +
          sourceCoefficient p * (conj (η x) * g x).re := by
    simp only [mul_add, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold tested
  simp_rw [he]
  rw [integral_add hL (hG.const_mul (sourceCoefficient p)), integral_const_mul,
    SchrodingerGreen.green p hη hu hc hs]

/-- Actual local C² regularity and source continuity turn the weak equation into the pointwise equation on an open region. -/
theorem classical_of_weak (p : MassiveParameters) {U : Set Covector} {u g : Covector → ℂ}
    (hU : IsOpen U) (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hg : ContinuousOn g U)
    (hw : WeakEquation p u g U) :
    ∀ x ∈ U, schrodingerResidual p u x + (sourceCoefficient p : ℂ) * g x = 0 := by
  apply OpenFundamentalLemma.continuousOn_eq_zero_of_test_pairings hU _
    ((SchrodingerGreen.continuousOn_residual p hu).add (hg.const_mul _))
  intro η hη hc hs
  change tested U η (fun x => schrodingerResidual p u x + (sourceCoefficient p : ℂ) * g x) = 0
  rw [tested_forcing p hη hu hg hc hs]
  exact hw η hη hc hs

/-- With genuine classical regularity, compact-tested and pointwise Schrödinger equations are equivalent for the same field and source. -/
theorem weak_iff_classical (p : MassiveParameters) {U : Set Covector} {u g : Covector → ℂ}
    (hU : IsOpen U) (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hg : ContinuousOn g U) :
    WeakEquation p u g U ↔
      ∀ x ∈ U, schrodingerResidual p u x + (sourceCoefficient p : ℂ) * g x = 0 := by
  constructor
  · exact classical_of_weak p hU hu hg
  · intro he η hη hc hs
    rw [← tested_forcing p hη hu hg hc hs]
    unfold tested
    exact setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by
      simp only [he x hx, mul_zero, Complex.zero_re])

end FoliationQM.WeakSchrodingerEquation
