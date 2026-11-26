module

public import FoliationQM.ScaledChiralAction
public import FoliationQM.OpenFundamentalLemma

/-!
# First variation of the chirally twisted relative action

For v13 `thm:dirac_lift`, independent compact variations of the complex
scalar at fixed angle see the true chiral gradient potential. The
potential correction is quadratic along each affine variation. Its
first derivative adds the potential times the field to the scalar
Klein–Gordon residual.
-/

@[expose] public section
noncomputable section
open scoped ContDiff ComplexConjugate
namespace FoliationQM.TwistedScalarVariation
open MeasureTheory DiracFieldDensity ActionVariation FlatIntegrationByParts
open TwistedScalarAction TwistedScalarDensity ScaledChiralAction

/-- The scalar Euler–Lagrange residual at fixed chiral angle, including the signed gradient potential. -/
def force (p : MassiveParameters) (β : Covector → ℝ) (z : Covector → ℂ) (x : Covector) : ℂ :=
  kgOperator p z coordinateDirections x + (potential p β x : ℂ) * z x

/-- The linear potential contribution paired with a complex scalar test. -/
def testPotential (p : MassiveParameters) (β : Covector → ℝ) (η z : Covector → ℂ) (x : Covector) : ℝ :=
  potential p β x * (conj (η x) * z x).re

/-- The pointwise potential increment is exactly a real quadratic polynomial in the test parameter. -/
theorem correctionDiff_affine (p : MassiveParameters) (β : Covector → ℝ) (z η : Covector → ℂ) (t : ℝ) (x : Covector) :
    correctionDiff p β z (fun y => z y + (t : ℂ)*η y) x =
      2*t * testPotential p β η z x + t^2 * testPotential p β η η x := by
  simp [correctionDiff, testPotential, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

variable (p : MassiveParameters) {β : Covector → ℝ} {z η : Covector → ℂ} {U : Set Covector}

/-- The full forced residual is continuous throughout the domain under C¹ angle and C² scalar regularity. -/
theorem continuousOn_force (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : ∀ x ∈ U, ContDiffAt ℝ 2 z x) :
    ContinuousOn (force p β z) U := by
  refine (OpenIntegrationByParts.continuousOn_kgOperator p hz coordinateDirections).add ?_
  intro x hx
  exact ((Complex.continuous_ofReal.continuousAt.comp (continuousAt_potential p (hb x hx))).mul
    (hz x hx).continuousAt).continuousWithinAt

/-- Multiplication by a compact interior test gives an integrable potential pairing. -/
theorem integrableOn_testPotential (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : ContinuousOn z U)
    (hη : Continuous η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    IntegrableOn (testPotential p β η z) U := by
  apply DiracActionSupport.integrableOn_of_compact_support hc hs
  · intro x hx
    exact (continuousAt_potential p (hb x hx)).continuousWithinAt.mul
      (Complex.continuous_re.continuousAt.comp_continuousWithinAt
        (((Complex.continuous_conj.comp hη).continuousAt.continuousWithinAt).mul (hz x hx)))
  · intro x hx
    simp [testPotential, image_eq_zero_of_notMem_tsupport hx]

/-- The compactly tested residual is integrable even when the background density is not integrable. -/
theorem integrableOn_test_force (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : ∀ x ∈ U, ContDiffAt ℝ 2 z x)
    (hη : Continuous η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    IntegrableOn (fun x => conj (η x) * force p β z x) U :=
  (OpenFundamentalLemma.integrable_test_pairing (continuousOn_force p hb hz) hη hc hs).integrableOn

private theorem integrable_correction_affine (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x)
    (hz : ContinuousOn z U) (hη : Continuous η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (t : ℝ) :
    IntegrableOn (correctionDiff p β z (fun y => z y + (t : ℂ)*η y)) U := by
  simp_rw [funext (correctionDiff_affine p β z η t)]
  exact ((integrableOn_testPotential p hb hz hη hc hs).const_mul (2*t)).add
    ((integrableOn_testPotential p hb hη.continuousOn hη hc hs).const_mul (t^2))

/-- The integrated potential correction has its exact linear and quadratic coefficients for every t. -/
theorem integral_correction_affine (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : ContinuousOn z U)
    (hη : Continuous η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (t : ℝ) :
    (∫ x in U, correctionDiff p β z (fun y => z y + (t : ℂ)*η y) x) =
      2*t * (∫ x in U, testPotential p β η z x) + t^2 * (∫ x in U, testPotential p β η η x) := by
  simp_rw [correctionDiff_affine]
  rw [integral_add ((integrableOn_testPotential p hb hz hη hc hs).const_mul (2*t))
    ((integrableOn_testPotential p hb hη.continuousOn hη hc hs).const_mul (t^2)),
    integral_const_mul, integral_const_mul]

private theorem hasDerivAt_correction (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : ContinuousOn z U)
    (hη : Continuous η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    HasDerivAt (fun t : ℝ => ∫ x in U, correctionDiff p β z (fun y => z y + (t : ℂ)*η y) x)
      (2 * ∫ x in U, testPotential p β η z x) 0 := by
  simp_rw [integral_correction_affine p hb hz hη hc hs]
  convert ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (∫ x in U, testPotential p β η z x))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (∫ x in U, testPotential p β η η x)) using 1
  · funext t
    rfl
  · norm_num

section Interior
variable (hU : IsOpen U) (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : ∀ x ∈ U, ContDiffAt ℝ 2 z x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U)
include hU hb hz hη hc hs

/-- For every real variation parameter the actual massive density increment is integrable on U. -/
theorem integrableOn_increment (t : ℝ) : IntegrableOn (fun x =>
    density p β (fun y => z y + (t : ℂ)*η y) x - density p β z x) U := by
  have hr := RelativeAction.integrableOn_relativeDensity_affine p hU coordinateDirections hz hη hc hs t
  have hp := integrable_correction_affine p hb (fun x hx => (hz x hx).continuousAt.continuousWithinAt)
    hη.continuous hc hs t
  apply (hr.sub hp).congr_fun _ hU.measurableSet
  intro x hx
  have hd := (hz x hx).differentiableAt (by norm_num)
  exact (increment_eq p (hb x hx).differentiableAt_one hd
    (hd.add ((hη.differentiable (by simp) x).const_mul _))).symm

private theorem relative_affine_eq (t : ℝ) :
    relativeAction p β z (fun y => z y + (t : ℂ)*η y) U =
      RelativeAction.relativeAction p z (fun y => z y + (t : ℂ)*η y) coordinateDirections U -
        ∫ x in U, correctionDiff p β z (fun y => z y + (t : ℂ)*η y) x := by
  apply ScaledChiralAction.relative_eq p hU.measurableSet (fun x hx => (hb x hx).differentiableAt_one)
    (fun x hx => (hz x hx).differentiableAt (by norm_num)) (fun x hx => ?_)
    (RelativeAction.integrableOn_relativeDensity_affine p hU coordinateDirections hz hη hc hs t)
    (integrable_correction_affine p hb (fun x hx => (hz x hx).continuousAt.continuousWithinAt) hη.continuous hc hs t)
  exact ((hz x hx).differentiableAt (by norm_num)).add ((hη.differentiable (by simp) x).const_mul _)

/-- The finite relative action has the tested field-pairing derivative before integration by parts. -/
theorem hasDerivAt_weak :
    HasDerivAt (fun t : ℝ => relativeAction p β z (fun y => z y + (t : ℂ)*η y) U)
      (2 * ∫ x in U, (fieldPairing p η z coordinateDirections x).re -
        potential p β x * (conj (η x) * z x).re) 0 := by
  have hzc : ContinuousOn z U := fun x hx => (hz x hx).continuousAt.continuousWithinAt
  simp_rw [relative_affine_eq p hU hb hz hη hc hs]
  have hi := (OpenIntegrationByParts.integrable_fieldPairing p (hη.of_le (by norm_num)) hz hc hs coordinateDirections).re
  simp only [RCLike.re_eq_complex_re] at hi
  change HasDerivAt _ (2 * ∫ x in U, (fieldPairing p η z coordinateDirections x).re - testPotential p β η z x) _
  rw [integral_sub hi (integrableOn_testPotential p hb hzc hη.continuous hc hs), mul_sub]
  exact (RelativeAction.hasDerivAt_relativeAction_affine p hU coordinateDirections hz hη hc hs).sub
    (hasDerivAt_correction p hb hzc hη.continuous hc hs)

/-- Integration by parts identifies the derivative with minus twice the tested forced residual. -/
theorem hasDerivAt_residual :
    HasDerivAt (fun t : ℝ => relativeAction p β z (fun y => z y + (t : ℂ)*η y) U)
      (-2 * ∫ x in U, (conj (η x) * force p β z x).re) 0 := by
  have hzc : ContinuousOn z U := fun x hx => (hz x hx).continuousAt.continuousWithinAt
  have he (x : Covector) : (conj (η x) * force p β z x).re =
      (conj (η x) * kgOperator p z coordinateDirections x).re + testPotential p β η z x := by
    simp only [force, mul_add, Complex.add_re, mul_left_comm (conj (η x)), Complex.re_ofReal_mul, testPotential]
  simp_rw [relative_affine_eq p hU hb hz hη hc hs, he]
  have hi := (OpenIntegrationByParts.integrable_test_kgOperator p (hη.of_le (by norm_num)) hz hc hs coordinateDirections).re
  simp only [RCLike.re_eq_complex_re] at hi
  rw [integral_add hi (integrableOn_testPotential p hb hzc hη.continuous hc hs), mul_add]
  have hd := (RelativeAction.hasDerivAt_relativeAction_affine_eq_kg_pairing p hU coordinateDirections hz hη hc hs).sub
    (hasDerivAt_correction p hb hzc hη.continuous hc hs)
  convert hd using 1
  ring

end Interior
end FoliationQM.TwistedScalarVariation
