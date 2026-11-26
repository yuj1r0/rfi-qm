module
public import FoliationQM.OpenFundamentalLemma
public import FoliationQM.DiracResidualField

/-!
# Detection of a continuous spinor residual by compact interior tests

For the physical variational part of v13 `thm:dirac_lift`, the real
Dirac-adjoint pairing with every smooth compact interior spinor test
detects each complex residual component pointwise on the open domain.
The scalar fundamental lemma is applied through explicit time-gamma
coordinate tests.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracFundamentalLemma
open MeasureTheory Set Function Matrix DiracMatrices DiracResidualPairing
open DiracResidualField DiracActionSupport DiracEquation
open scoped Topology ContDiff ComplexConjugate

/-- A scalar test field placed in one Dirac-adjoint coordinate test. -/
def coordinateTest (i : Fin 4) (φ : Covector → ℂ) (x : Covector) : Spinor :=
  componentTest i (φ x)

/-- Each coordinate field is a scalar multiple of a single fixed time-gamma test. -/
theorem coordinateTest_smul (i : Fin 4) (φ : Covector → ℂ) (x : Covector) :
    coordinateTest i φ x = φ x • componentTest i 1 := by
  unfold coordinateTest componentTest
  rw [← Matrix.mulVec_smul, ← Pi.single_smul' i (φ x) (1 : ℂ), smul_eq_mul, mul_one]

/-- Putting a smooth scalar test in one spinor component preserves smoothness. -/
theorem contDiff_coordinateTest {n : WithTop ℕ∞} (i : Fin 4) {φ : Covector → ℂ} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (coordinateTest i φ) := by
  simpa only [show coordinateTest i φ = fun x => φ x • componentTest i 1 from
    funext (coordinateTest_smul i φ)] using hφ.smul_const (componentTest i 1)

/-- The spinor test is supported inside the scalar test's closed support. -/
theorem tsupport_coordinateTest_subset (i : Fin 4) (φ : Covector → ℂ) :
    tsupport (coordinateTest i φ) ⊆ tsupport φ :=
  tsupport_comp_subset (g := componentTest i) (by simp [componentTest]) φ

/-- Compact scalar test support gives compact spinor test support. -/
theorem compact_coordinateTest (i : Fin 4) {φ : Covector → ℂ} (hc : HasCompactSupport φ) :
    HasCompactSupport (coordinateTest i φ) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordinateTest_subset i φ)

/-- The actual adjoint pairing against a coordinate field is the complex scalar test pairing. -/
theorem pair_coordinateTest (i : Fin 4) (φ : Covector → ℂ) (R : Covector → Spinor) (x : Covector) :
    pair (coordinateTest i φ x) (R x) = (conj (φ x) * R x i).re :=
  pair_componentTest i (φ x) (R x)

/-- Real scalar directions test the real component. -/
theorem pair_real_test (i : Fin 4) (φ : Covector → ℝ) (R : Covector → Spinor) (x : Covector) :
    pair (coordinateTest i (fun y => (φ y : ℂ)) x) (R x) = φ x * (R x i).re := by
  simp [pair_coordinateTest, Complex.mul_re]

/-- Purely imaginary scalar directions test the imaginary component with positive sign. -/
theorem pair_imaginary_test (i : Fin 4) (φ : Covector → ℝ) (R : Covector → Spinor) (x : Covector) :
    pair (coordinateTest i (fun y => Complex.I * (φ y : ℂ)) x) (R x) = φ x * (R x i).im := by
  simp [pair_coordinateTest, Complex.mul_re, Complex.mul_im]

variable {U : Set Covector} {R : Covector → Spinor}

/-- All compact interior pairings of locally continuous spinors are genuine integrable tests. -/
theorem integrableOn_pair (hR : ContinuousOn R U) {η : Covector → Spinor} (hη : ContinuousOn η U)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) : IntegrableOn (fun x => pair (η x) (R x)) U := by
  apply integrableOn_of_compact_support hc hs
  · intro x hx
    exact (pairCLM.continuous.continuousAt.comp_continuousWithinAt (hη x hx)).clm_apply (hR x hx)
  · intro x hx
    change pairCLM (η x) _ = 0
    simp [image_eq_zero_of_notMem_tsupport hx]

/-- The real Dirac-adjoint pairing with all smooth compact interior spinor tests
vanishes exactly when the continuous spinor residual vanishes pointwise on U. -/
theorem vanishing_pairings_iff (hU : IsOpen U) (hR : ContinuousOn R U) :
    (∀ η : Covector → Spinor, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      ∫ x in U, pair (η x) (R x) = 0) ↔ ∀ x ∈ U, R x = 0 := by
  constructor
  · intro h x hx
    funext i
    apply OpenFundamentalLemma.continuousOn_eq_zero_of_test_pairings hU (fun y => R y i)
      ((continuous_apply i).comp_continuousOn hR) _ x hx
    intro φ hφ hc hs
    have H := h (coordinateTest i φ) (contDiff_coordinateTest i hφ) (compact_coordinateTest i hc)
      ((tsupport_coordinateTest_subset i φ).trans hs)
    simpa only [pair_coordinateTest] using H
  · intro h η _ _ _
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    change pairCLM (η x) (R x) = 0
    simp [h x hx]

/-- Specialization to the actual flat-coordinate Dirac field on a locally C¹ background. -/
theorem diracField_vanishing_pairings_iff (hbar m c : ℝ) {ψ : Covector → Spinor} (hU : IsOpen U)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x) :
    (∀ η : Covector → Spinor, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      ∫ x in U, tested hbar m c ψ η x = 0) ↔ ∀ x ∈ U, diracField hbar m c ψ x = 0 :=
  vanishing_pairings_iff hU (fun x hx => (continuousAt_diracField hbar m c (hψ x hx)).continuousWithinAt)

end FoliationQM.DiracFundamentalLemma
