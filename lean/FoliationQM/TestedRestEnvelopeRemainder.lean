module

public import FoliationQM.SchrodingerGreen
public import FoliationQM.RestEnvelopeRemainder
public import FoliationQM.ScalarLocalTesting

/-!
# Compact testing of the actual rest-envelope remainder

Source: v13 `cor:schrodinger`, component kinds C and D. Genuine compact
pairings move the physical time derivatives onto the test. The actual
phase-neutralized KG source and the positive temporal coefficient remain
in the exact identity. No bound on envelope derivatives is assumed.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.TestedRestEnvelopeRemainder

open MeasureTheory Filter Set ScalarLocalTesting PolarSecondDifferential
open RestEnvelopeKG RestEnvelopeRemainder RestEnvelopeDifferential
open LaboratoryCoordinates LaboratoryKG
open Madelung (coordinateVector)
open scoped ContDiff ComplexConjugate

variable {U : Set Covector} {η u ψ : Covector → ℂ}

private theorem integrable_source_pair (p : MassiveParameters)
    (hη : ContDiff ℝ ∞ η) (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    Integrable (fun x => conj (η x) * neutralizedKG p u x) := by
  let a : ℂ := temporalCoefficient p
  let b : ℂ := sourceCoefficient p
  have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (sourceCoefficient_pos p))
  have hL := (SchrodingerGreen.integrable_pairings p hη hu hc hs).1
  have hT := (CompactComplexGreen.integrable_second_pairings hη hu hc hs
    (coordinateVector 0)).1
  apply (((hT.const_mul a).sub hL).const_mul b⁻¹).congr
  apply Eventually.of_forall
  intro x
  change b⁻¹ * (a * (conj (η x) * secondDirectionalDerivative u (coordinateVector 0) x) -
    conj (η x) * schrodingerResidual p u x) = conj (η x) * neutralizedKG p u x
  by_cases hx : x ∈ U
  · have he := corrected_residual p (hu x hx)
    change schrodingerResidual p u x + b * neutralizedKG p u x =
      a * secondDirectionalDerivative u (coordinateVector 0) x at he
    have he' : a * secondDirectionalDerivative u (coordinateVector 0) x -
        schrodingerResidual p u x = b * neutralizedKG p u x := by
      rw [← he]
      ring
    calc
      _ = b⁻¹ * (conj (η x) * (a * secondDirectionalDerivative u (coordinateVector 0) x -
          schrodingerResidual p u x)) := by ring
      _ = b⁻¹ * (conj (η x) * (b * neutralizedKG p u x)) := by rw [he']
      _ = (b⁻¹ * b) * (conj (η x) * neutralizedKG p u x) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hb, one_mul]
  · have hzero : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hs hx'))
    simp [hzero]

/-- Compact tests transfer the actual Schrödinger operator and temporal remainder to the test,
while retaining the genuine phase-neutralized KG source with its exact coefficient. -/
theorem tested_corrected (p : MassiveParameters)
    (hη : ContDiff ℝ ∞ η) (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    tested U (schrodingerResidual p η) u + sourceCoefficient p *
        tested U η (neutralizedKG p u) =
      temporalCoefficient p * tested U (secondDirectionalDerivative η (coordinateVector 0)) u := by
  obtain ⟨hL, hL'⟩ := SchrodingerGreen.integrable_pairings p hη hu hc hs
  obtain ⟨_, hT'⟩ := CompactComplexGreen.integrable_second_pairings hη hu hc hs
    (coordinateVector 0)
  have hN := integrable_source_pair p hη hu hc hs
  have hpoint (x : Covector) :
      conj (η x) * schrodingerResidual p u x +
          (sourceCoefficient p : ℂ) * (conj (η x) * neutralizedKG p u x) =
        (temporalCoefficient p : ℂ) *
          (conj (η x) * secondDirectionalDerivative u (coordinateVector 0) x) := by
    by_cases hx : x ∈ U
    · calc
        _ = conj (η x) * (schrodingerResidual p u x +
            (sourceCoefficient p : ℂ) * neutralizedKG p u x) := by ring
        _ = _ := by rw [corrected_residual p (hu x hx)]; ring
    · have hzero : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hs hx'))
      simp [hzero]
  have hi : (∫ x in U, conj (η x) * schrodingerResidual p u x) +
      (sourceCoefficient p : ℂ) * (∫ x in U, conj (η x) * neutralizedKG p u x) =
        (temporalCoefficient p : ℂ) *
          (∫ x in U, conj (η x) * secondDirectionalDerivative u (coordinateVector 0) x) := by
    rw [← integral_const_mul, ← integral_add hL.integrableOn
      (hN.integrableOn.const_mul (sourceCoefficient p : ℂ)), ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hpoint)
  rw [SchrodingerGreen.complex_green p hη hu hc hs,
    CompactComplexGreen.second_transfer hη hu hc hs (coordinateVector 0)] at hi
  have hr := congrArg Complex.re hi
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hr
  have hre (f : Covector → ℂ) (hf : IntegrableOn f U) :
      (∫ x in U, f x).re = ∫ x in U, (f x).re := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hf).symm
  rw [hre _ hL'.integrableOn, hre _ hN.integrableOn, hre _ hT'.integrableOn] at hr
  exact hr

/-- Testing an original normal-coordinate field retains its actual KG source at the same
physical-to-normal image, with the same envelope and positive temporal remainder. -/
theorem source_tested_corrected (p : MassiveParameters)
    (hη : ContDiff ℝ ∞ η)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ (toNormal p.c x))
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    tested U (schrodingerResidual p η) (envelope p ψ) + sourceCoefficient p *
        tested U η (fun x => (carrierField p x)⁻¹ *
          FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x)) =
      temporalCoefficient p * tested U (secondDirectionalDerivative η (coordinateVector 0))
        (envelope p ψ) := by
  have h := tested_corrected p hη (fun x hx => contDiffAt_envelope p (hψ x hx)) hc hs
  have he : tested U η (neutralizedKG p (envelope p ψ)) =
      tested U η (fun x => (carrierField p x)⁻¹ *
        FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x)) := by
    unfold tested
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ U
    · change (conj (η x) * ((carrierField p x)⁻¹ *
        laboratoryKG p (dressedField p (envelope p ψ)) x)).re = _
      rw [dressedField_envelope, laboratoryKG_pullback p (hψ x hx)]
    · have hzero : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hs hx'))
      simp [hzero]
  rwa [he] at h

/-- An actual original homogeneous KG equation gives the tested temporal remainder law,
without a magnitude bound on the envelope's time derivatives. -/
theorem source_tested_of_KG (p : MassiveParameters)
    (hη : ContDiff ℝ ∞ η)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ (toNormal p.c x))
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U)
    (hKG : ∀ x ∈ U,
      FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x) = 0) :
    tested U (schrodingerResidual p η) (envelope p ψ) =
      temporalCoefficient p * tested U (secondDirectionalDerivative η (coordinateVector 0))
        (envelope p ψ) := by
  have hz : tested U η (fun x => (carrierField p x)⁻¹ *
      FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x)) = 0 := by
    unfold tested
    apply integral_eq_zero_of_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ U
    · simp [hKG x hx]
    · have hzero : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hs hx'))
      simp [hzero]
  simpa only [hz, mul_zero, add_zero] using source_tested_corrected p hη hψ hc hs

end FoliationQM.TestedRestEnvelopeRemainder
