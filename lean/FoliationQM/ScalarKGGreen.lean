module

public import FoliationQM.TwistedScalarVariation
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Green identity for compact interior scalar tests

For the scalar limit of v13 `thm:dirac_lift`, both derivatives of the
flat massive Klein–Gordon operator can be moved to a compact interior
test. A local C² field admits a compact C² replacement equal to it near
the test support, so no boundary regularity is required.
-/

@[expose] public section
noncomputable section
open scoped ComplexConjugate ContDiff Topology
namespace FoliationQM.ScalarKGGreen
open Set Filter MeasureTheory DiracFieldDensity FlatIntegrationByParts PolarSecondDifferential
open OpenIntegrationByParts TwistedScalarVariation TwistedScalarDensity

/-- The massive differential operator vanishes off the closed support of its argument. -/
theorem kg_zero_of_notMem (p : MassiveParameters) (η : Covector → ℂ) {x : Covector} (hx : x ∉ tsupport η) :
    kgOperator p η coordinateDirections x = 0 := by
  have hs (v : Covector) : secondDirectionalDerivative η v x = 0 := by
    have he : x ∉ tsupport (directionalDerivative η v) := fun h => hx (tsupport_fderiv_apply_subset ℝ v h)
    change (fderiv ℝ (directionalDerivative η v) x) v = 0
    rw [fderiv_of_notMem_tsupport ℝ he]
    rfl
  simp [kgOperator, box, hs, image_eq_zero_of_notMem_tsupport hx]

/-- The topological support of the Klein–Gordon image lies inside the original test support. -/
theorem tsupport_kg_subset (p : MassiveParameters) (η : Covector → ℂ) :
    tsupport (kgOperator p η coordinateDirections) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro x hx
  by_contra hn
  exact hx (kg_zero_of_notMem p η hn)

/-- A smooth test has continuous massive Klein–Gordon image on the full ambient space. -/
theorem continuous_kg_test (p : MassiveParameters) {η : Covector → ℂ} (hη : ContDiff ℝ ∞ η) :
    Continuous (kgOperator p η coordinateDirections) :=
  continuous_kgOperator p (hη.of_le (by simp)) _

/-- Compact support of a test passes to its Klein–Gordon image. -/
theorem compact_kg_test (p : MassiveParameters) (η : Covector → ℂ) (hc : HasCompactSupport η) :
    HasCompactSupport (kgOperator p η coordinateDirections) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_kg_subset p η)

private theorem compact_replacement {U : Set Covector} {z η : Covector → ℂ} (hU : IsOpen U)
    (hz : ∀ x ∈ U, ContDiffAt ℝ 2 z x) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    ∃ w : Covector → ℂ, ContDiff ℝ 2 w ∧ HasCompactSupport w ∧ tsupport w ⊆ U ∧
      ∀ x ∈ tsupport η, w =ᶠ[𝓝 x] z := by
  obtain ⟨K, hK, hηK, hKU⟩ := exists_compact_between hc hU hs
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf, _, hsupport, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 2) isOpen_interior hK.isClosed hKL
  let w := fun y => (f y : ℂ) * z y
  have hzero (y : Covector) (hy : y ∉ L) : w y = 0 := by
    have hn : y ∉ Function.support f := fun h => hy (interior_subset (hsupport ▸ h))
    simp [w, Function.notMem_support.mp hn]
  have hsub : tsupport w ⊆ L := closure_minimal
    (fun y hy => by by_contra hn; exact hy (hzero y hn)) hL.isClosed
  refine ⟨w, contDiff_iff_contDiffAt.mpr ?_, hL.of_isClosed_subset (isClosed_tsupport w) hsub, hsub.trans hLU, ?_⟩
  · intro y
    by_cases hy : y ∈ U
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp y hf.contDiffAt).mul (hz y hy)
    · exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (hLU (hsub h))))
  · intro x hx
    filter_upwards [isOpen_interior.mem_nhds (hηK hx)] with y hy
    simp [w, (hone y).mp (interior_subset hy)]

private theorem re_conj_swap (z w : ℂ) : (conj z * w).re = (conj w * z).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

variable (p : MassiveParameters) {z η : Covector → ℂ} {U : Set Covector}

/-- The adjoint-tested integral is integrable on U for a locally continuous field and a compact interior test. -/
theorem integrableOn_adjoint (hz : ContinuousOn z U) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    IntegrableOn (fun x => conj (kgOperator p η coordinateDirections x) * z x) U :=
  (OpenFundamentalLemma.integrable_test_pairing hz (continuous_kg_test p hη)
    (compact_kg_test p η hc) ((tsupport_kg_subset p η).trans hs)).integrableOn

/-- The real Green identity moves both massive Klein–Gordon derivatives onto a compact interior test. -/
theorem green (hU : IsOpen U) (hz : ∀ x ∈ U, ContDiffAt ℝ 2 z x) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    (∫ x in U, (conj (η x) * kgOperator p z coordinateDirections x).re) =
      ∫ x in U, (conj (kgOperator p η coordinateDirections x) * z x).re := by
  obtain ⟨w, hw, hwc, hws, hnear⟩ := compact_replacement hU hz hc hs
  have hleft := integral_re_fieldPairing_eq p (hη.of_le (by norm_num)) hz hc hs coordinateDirections
  have hright := integral_re_fieldPairing_eq p (hw.of_le (by norm_num))
    (fun x (_ : x ∈ U) => (hη.of_le (by norm_num) : ContDiff ℝ 2 η).contDiffAt) hwc hws coordinateDirections
  have hpair : (∫ x in U, (ActionVariation.fieldPairing p η z coordinateDirections x).re) =
      ∫ x in U, (ActionVariation.fieldPairing p w η coordinateDirections x).re := by
    apply setIntegral_congr_fun hU.measurableSet
    intro x _
    dsimp only
    rw [ActionVariation.fieldPairing_re_symm p w η]
    by_cases hx : x ∈ tsupport η
    · have h := hnear x hx
      simp only [ActionVariation.fieldPairing, directionalDerivative, h.self_of_nhds, h.fderiv_eq]
    · rw [fieldPairing_zero_of_notMem_tsupport p η z _ hx, fieldPairing_zero_of_notMem_tsupport p η w _ hx]
  have htest : (∫ x in U, (conj (w x) * kgOperator p η coordinateDirections x).re) =
      ∫ x in U, (conj (kgOperator p η coordinateDirections x) * z x).re := by
    apply setIntegral_congr_fun hU.measurableSet
    intro x _
    dsimp only
    by_cases hx : x ∈ tsupport η
    · rw [(hnear x hx).self_of_nhds, re_conj_swap]
    · simp [kg_zero_of_notMem p η hx]
  linarith

/-- The compact test times the chiral potential and scalar field is integrable on the open region. -/
theorem integrableOn_testPotential {β : Covector → ℝ} (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : ContinuousOn z U)
    (hη : Continuous η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    IntegrableOn (fun x => conj (η x) * ((potential p β x : ℂ) * z x)) U := by
  apply (OpenFundamentalLemma.integrable_test_pairing _ hη hc hs).integrableOn
  intro x hx
  exact (Complex.continuous_ofReal.continuousAt.comp
    (TwistedScalarAction.continuousAt_potential p (hb x hx))).continuousWithinAt.mul (hz x hx)

/-- The tested force splits into the adjoint test term and the signed chiral potential term. -/
theorem tested_force (hU : IsOpen U) {β : Covector → ℝ} (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x)
    (hz : ∀ x ∈ U, ContDiffAt ℝ 2 z x) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    (∫ x in U, (conj (η x) * force p β z x).re) =
      (∫ x in U, (conj (kgOperator p η coordinateDirections x) * z x).re) +
        ∫ x in U, (conj (η x) * ((potential p β x : ℂ) * z x)).re := by
  have h1 := (OpenIntegrationByParts.integrable_test_kgOperator p (hη.of_le (by norm_num)) hz hc hs coordinateDirections).re
  have h2 := (integrableOn_testPotential p hb (fun x hx => (hz x hx).continuousAt.continuousWithinAt)
    hη.continuous hc hs).re
  simp only [RCLike.re_eq_complex_re] at h1 h2
  simp only [force, mul_add, Complex.add_re]
  rw [integral_add h1 h2, green p hU hz hη hc hs]

end FoliationQM.ScalarKGGreen
