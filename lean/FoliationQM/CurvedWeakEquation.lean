module

public import FoliationQM.OpenFundamentalLemma
public import FoliationQM.CurvedWaveDivergence
public import FoliationQM.CurvedFluxRegularity

/-!
# Detecting a curved scalar field equation by compact tests

The metric volume factor is continuous and strictly positive on a Lorentz
coordinate patch. Real pairings with independent complex test fields
therefore detect a continuous residual at every point of the patch.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator ComplexConjugate ContDiff
namespace FoliationQM.CurvedWeakEquation

open MeasureTheory LorentzMatrixGroup RNCVolumeDensity

/-- The coordinate volume multiplier is continuous as a function of all real matrix entries. -/
theorem volumeFactor_continuous : Continuous volumeFactor :=
  Real.continuous_sqrt.comp ((continuous_id.matrix_det : Continuous (Matrix.det : Mat4 → ℝ)).neg)

/-- Weighted test pairing used by the curved Euler–Lagrange equation. -/
def testIntegral (U : Set Covector) (g : Covector → Mat4) (η F : Covector → ℂ) : ℝ :=
  ∫ x in U, volumeFactor (g x) * (conj (η x) * F x).re

/-- The integrand is the real test pairing with the metric-weighted residual. -/
theorem weighted_pair (a : ℝ) (u z : ℂ) :
    (conj u * (a • z)).re = a * (conj u * z).re := by
  simp only [mul_smul_comm, Complex.smul_re, smul_eq_mul]

/-- Interior compact test pairings with a locally continuous weighted residual are integrable. -/
theorem integrable_pair {U : Set Covector} {g : Covector → Mat4} {F η : Covector → ℂ}
    (hg : ContinuousOn g U) (hF : ContinuousOn F U) (hη : Continuous η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    Integrable (fun x => volumeFactor (g x) • (conj (η x) * F x)) := by
  have hv : ContinuousOn (fun x => volumeFactor (g x)) U :=
    volumeFactor_continuous.comp_continuousOn hg
  have hi := OpenFundamentalLemma.integrable_test_pairing (hv.smul hF) hη hc hs
  apply hi.congr
  filter_upwards with x
  change conj (η x) * (volumeFactor (g x) • F x) = volumeFactor (g x) • (conj (η x) * F x)
  rw [mul_smul_comm]

/-- Compact smooth complex tests detect a continuous residual pointwise in an open Lorentz coordinate patch. -/
theorem zero_iff_tests {U : Set Covector} (hU : IsOpen U) {g : Covector → Mat4}
    (hg : ContinuousOn g U) (hd : ∀ x ∈ U, (g x).det < 0) {F : Covector → ℂ}
    (hF : ContinuousOn F U) :
    (∀ x ∈ U, F x = 0) ↔
    ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      testIntegral U g η F = 0 := by
  constructor
  · intro hz η _ _ _
    unfold testIntegral
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    simp [hz x hx]
  · intro ht
    have hv : ContinuousOn (fun x => volumeFactor (g x)) U :=
      volumeFactor_continuous.comp_continuousOn hg
    have hz := OpenFundamentalLemma.continuousOn_eq_zero_of_test_pairings hU
      (fun x => volumeFactor (g x) • F x) (hv.smul hF) (fun η hη hc hs => by
        simpa only [weighted_pair, testIntegral] using ht η hη hc hs)
    intro x hx
    exact (smul_eq_zero.mp (hz x hx)).resolve_left (Real.sqrt_pos.2 (neg_pos.mpr (hd x hx))).ne'

/-- Agreement of the divergence-form wave with a continuous source is determined by the weighted compact tests. -/
theorem wave_iff_tests {U : Set Covector} (hU : IsOpen U) {g : Covector → Mat4} {f q : Covector → ℂ}
    (hg : ∀ x ∈ U, ContDiffAt ℝ 1 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x) (hq : ContinuousOn q U) :
    (∀ x ∈ U, CurvedWaveDivergence.wave g f x = q x) ↔
    ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      testIntegral U g η (fun x => CurvedWaveDivergence.wave g f x - q x) = 0 := by
  have hw : ContinuousOn (CurvedWaveDivergence.wave g f) U := fun x hx =>
    (CurvedFluxRegularity.wave_continuousAt (hg x hx) (hd x hx) (hf x hx)).continuousWithinAt
  exact (forall₂_congr fun _ _ => sub_eq_zero.symm).trans <|
    zero_iff_tests hU (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hd (hw.sub hq)

end FoliationQM.CurvedWeakEquation
