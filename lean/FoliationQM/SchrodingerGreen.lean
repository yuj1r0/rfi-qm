module

public import FoliationQM.RestEnvelopeKG
public import FoliationQM.CompactComplexGreen
public import FoliationQM.OpenFundamentalLemma

/-!
# Compact-test Green identity for the physical Schrödinger operator

Source: v13 `cor:schrodinger`. Actual first-time and spatial-second
derivatives move to the same compact test. Conjugating the imaginary time
coefficient cancels the first integration-by-parts sign. The background is
locally C²; no boundary or regularity assumption outside the region occurs.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SchrodingerGreen

open MeasureTheory Filter RestEnvelopeKG LaboratoryKG PolarSecondDifferential
open Madelung (coordinateVector)
open scoped ContDiff ComplexConjugate Topology

/-- The actual Schrödinger image vanishes off the closed support of its argument. -/
theorem residual_zero_of_notMem (p : MassiveParameters) (η : Covector → ℂ)
    {x : Covector} (hx : x ∉ tsupport η) : schrodingerResidual p η x = 0 := by
  have ht : directionalDerivative η (coordinateVector 0) x = 0 := by
    change (fderiv ℝ η x) (coordinateVector 0) = 0
    rw [fderiv_of_notMem_tsupport ℝ hx]
    rfl
  have hs (i : Fin 3) : secondDirectionalDerivative η (coordinateVector i.succ) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h =>
      hx (CompactComplexGreen.tsupport_second_subset η (coordinateVector i.succ) h))
  simp [schrodingerResidual, spatialLaplacian, ht, hs]

/-- The closed support of the Schrödinger test image lies in the original closed support. -/
theorem tsupport_residual_subset (p : MassiveParameters) (η : Covector → ℂ) :
    tsupport (schrodingerResidual p η) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro x hx
  by_contra hn
  exact hx (residual_zero_of_notMem p η hn)

/-- The actual Schrödinger operator maps a smooth test to a smooth test. -/
theorem contDiff_residual_test (p : MassiveParameters) {η : Covector → ℂ}
    (hη : ContDiff ℝ ∞ η) : ContDiff ℝ ∞ (schrodingerResidual p η) := by
  have hs : ContDiff ℝ ∞ (spatialLaplacian η) := by
    unfold spatialLaplacian
    apply ContDiff.sum
    intro i _
    exact CompactComplexGreen.contDiff_second_test hη (coordinateVector i.succ)
  exact (contDiff_const.mul
    (CompactComplexGreen.contDiff_directional_test hη (coordinateVector 0))).add
    (contDiff_const.mul hs)

/-- Compact support passes to the actual Schrödinger image without a regularity premise. -/
theorem compact_residual_test (p : MassiveParameters) (η : Covector → ℂ)
    (hc : HasCompactSupport η) : HasCompactSupport (schrodingerResidual p η) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_residual_subset p η)

/-- Local C² regularity gives continuity of the actual physical Schrödinger residual on the region. -/
theorem continuousOn_residual (p : MassiveParameters) {U : Set Covector}
    {u : Covector → ℂ} (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) :
    ContinuousOn (schrodingerResidual p u) U := by
  intro x hx
  have hs (i : Fin 3) : ContinuousAt
      (secondDirectionalDerivative u (coordinateVector i.succ)) x :=
    ((OpenIntegrationByParts.contDiffAt_directionalDerivative (hu x hx)
      (coordinateVector i.succ)).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
        continuousAt_const
  have hΔ : ContinuousAt (spatialLaplacian u) x :=
    tendsto_finsetSum Finset.univ (fun i _ => hs i)
  exact (((OpenIntegrationByParts.contDiffAt_directionalDerivative (hu x hx)
    (coordinateVector 0)).continuousAt.const_mul (Complex.I * (p.hbar : ℂ))).add
      (hΔ.const_mul ((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ))).continuousWithinAt

/-- Both actual Green pairings are genuinely integrable on ambient volume for a compact interior test. -/
theorem integrable_pairings (p : MassiveParameters) {U : Set Covector}
    {η u : Covector → ℂ} (hη : ContDiff ℝ ∞ η)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U) :
    Integrable (fun x => conj (η x) * schrodingerResidual p u x) ∧
      Integrable (fun x => conj (schrodingerResidual p η x) * u x) := by
  exact ⟨OpenFundamentalLemma.integrable_test_pairing (continuousOn_residual p hu)
    hη.continuous hc hs,
    OpenFundamentalLemma.integrable_test_pairing
      (fun x hx => (hu x hx).continuousAt.continuousWithinAt)
      (contDiff_residual_test p hη).continuous (compact_residual_test p η hc)
      ((tsupport_residual_subset p η).trans hs)⟩

/-- The complex Green identity moves the actual Schrödinger operator to the same compact interior test. -/
theorem complex_green (p : MassiveParameters) {U : Set Covector}
    {η u : Covector → ℂ} (hη : ContDiff ℝ ∞ η)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U) :
    (∫ x in U, conj (η x) * schrodingerResidual p u x) =
      ∫ x in U, conj (schrodingerResidual p η x) * u x := by
  let A : ℂ := Complex.I * (p.hbar : ℂ)
  let B : ℂ := ((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ)
  let f₀ := fun x => conj (η x) * directionalDerivative u (coordinateVector 0) x
  let g₀ := fun x => conj (directionalDerivative η (coordinateVector 0) x) * u x
  let f := fun (i : Fin 3) x => conj (η x) *
    secondDirectionalDerivative u (coordinateVector i.succ) x
  let g := fun (i : Fin 3) x =>
    conj (secondDirectionalDerivative η (coordinateVector i.succ) x) * u x
  have hf₀ : IntegrableOn f₀ U :=
    (CompactComplexGreen.integrable_first_pairings hη hu hc hs (coordinateVector 0)).1.integrableOn
  have hg₀ : IntegrableOn g₀ U :=
    (CompactComplexGreen.integrable_first_pairings hη hu hc hs (coordinateVector 0)).2.integrableOn
  have hf (i : Fin 3) : IntegrableOn (f i) U :=
    (CompactComplexGreen.integrable_second_pairings hη hu hc hs (coordinateVector i.succ)).1.integrableOn
  have hg (i : Fin 3) : IntegrableOn (g i) U :=
    (CompactComplexGreen.integrable_second_pairings hη hu hc hs (coordinateVector i.succ)).2.integrableOn
  have hfs : IntegrableOn (fun x => ∑ i, f i x) U :=
    integrable_finsetSum Finset.univ (fun i _ => hf i)
  have hgs : IntegrableOn (fun x => ∑ i, g i x) U :=
    integrable_finsetSum Finset.univ (fun i _ => hg i)
  have hl : (fun x => conj (η x) * schrodingerResidual p u x) =
      fun x => A * f₀ x + B * ∑ i, f i x := by
    funext x
    simp only [f₀, f, schrodingerResidual, spatialLaplacian, A, B, ← Finset.mul_sum]
    ring
  have hr : (fun x => conj (schrodingerResidual p η x) * u x) =
      fun x => -A * g₀ x + B * ∑ i, g i x := by
    funext x
    simp only [g₀, g, schrodingerResidual, spatialLaplacian, A, B, map_add, map_mul,
      map_sum, Complex.conj_I, Complex.conj_ofReal, ← Finset.sum_mul]
    ring
  have h₀ : (∫ x in U, f₀ x) = -(∫ x in U, g₀ x) :=
    CompactComplexGreen.first_transfer hη hu hc hs (coordinateVector 0)
  have hi (i : Fin 3) : (∫ x in U, f i x) = ∫ x in U, g i x :=
    CompactComplexGreen.second_transfer hη hu hc hs (coordinateVector i.succ)
  rw [hl, hr, integral_add (hf₀.const_mul A) (hfs.const_mul B),
    integral_add (hg₀.const_mul (-A)) (hgs.const_mul B)]
  simp only [integral_const_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => hf i),
    integral_finsetSum Finset.univ (fun i _ => hg i), h₀]
  simp_rw [hi]
  ring

/-- Taking real parts gives the actual real tested Green identity, with both integrabilities established first. -/
theorem green (p : MassiveParameters) {U : Set Covector}
    {η u : Covector → ℂ} (hη : ContDiff ℝ ∞ η)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U) :
    (∫ x in U, (conj (η x) * schrodingerResidual p u x).re) =
      ∫ x in U, (conj (schrodingerResidual p η x) * u x).re := by
  have hint := integrable_pairings p hη hu hc hs
  have hl := integral_re (μ := volume.restrict U) (hint.1.integrableOn (s := U))
  have hr := integral_re (μ := volume.restrict U) (hint.2.integrableOn (s := U))
  simp only [RCLike.re_eq_complex_re] at hl hr
  exact hl.trans ((congrArg Complex.re (complex_green p hη hu hc hs)).trans hr.symm)

end FoliationQM.SchrodingerGreen
