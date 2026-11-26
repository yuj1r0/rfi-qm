module

public import FoliationQM.StationaryAction

/-!
# The fundamental lemma on an arbitrary open flat domain

Source: v13 `thm:kahler`. Tests are globally smooth, with compact topological
support contained in the open domain. The detected field is only required to
be continuous on that domain. Restricted Lebesgue integrals are genuine
integrals of integrable test products; no integrability or regularity outside
the domain is assumed.
-/
@[expose] public section

namespace FoliationQM.OpenFundamentalLemma

open MeasureTheory
open scoped ComplexConjugate ContDiff

/-- Multiplication by a compact interior test makes a locally continuous field
integrable, even when the field is unrestricted outside the domain. -/
theorem integrable_test_pairing {U : Set Covector} {F η : Covector → ℂ}
    (hF : ContinuousOn F U) (hη : Continuous η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U) : Integrable (fun x => conj (η x) * F x) := by
  have hp : ContinuousOn (fun x => conj (η x) * F x) (tsupport η) :=
    (Complex.continuous_conj.comp hη).continuousOn.mul (hF.mono hs)
  apply (hp.integrableOn_compact hc).integrable_of_forall_notMem_eq_zero
  intro x hx
  simp [image_eq_zero_of_notMem_tsupport hx]

/-- An interior-supported test pairing has the same restricted and whole-space
integrals. No boundary regularity is needed because the test vanishes off U. -/
theorem setIntegral_test_pairing_eq_integral {U : Set Covector}
    {F η : Covector → ℂ} (hs : tsupport η ⊆ U) :
    (∫ x in U, (conj (η x) * F x).re) = ∫ x, (conj (η x) * F x).re := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
  simp [hz]

/-- The local fundamental lemma for complex fields and real test pairings.
Only continuity on U is required, and the conclusion is pointwise on U. -/
theorem continuousOn_eq_zero_of_test_pairings {U : Set Covector} (hU : IsOpen U)
    (F : Covector → ℂ) (hF : ContinuousOn F U)
    (h : ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → ∫ x in U, (conj (η x) * F x).re = 0) :
    ∀ x ∈ U, F x = 0 := by
  apply MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) _ hU hF
    continuousOn_const
  change ∀ᵐ x ∂volume.restrict U, F x = 0
  rw [ae_restrict_iff' hU.measurableSet]
  apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hF.locallyIntegrableOn hU.measurableSet)
  intro g hg hgc hgs
  have hgd : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hgc' : HasCompactSupport (fun x => (g x : ℂ)) :=
    hgc.comp_left (g := fun t : ℝ => (t : ℂ)) rfl
  have hgs' : tsupport (fun x => (g x : ℂ)) ⊆ U :=
    (tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) rfl g).trans hgs
  have hgi : ContDiff ℝ ∞ (fun x => Complex.I * (g x : ℂ)) := contDiff_const.mul hgd
  have hgic : HasCompactSupport (fun x => Complex.I * (g x : ℂ)) := hgc'.mul_left
  have hgis : tsupport (fun x => Complex.I * (g x : ℂ)) ⊆ U :=
    tsupport_mul_subset_right.trans hgs'
  have hr := h _ hgd hgc' hgs'
  have hi := h _ hgi hgic hgis
  rw [setIntegral_test_pairing_eq_integral hgs'] at hr
  rw [setIntegral_test_pairing_eq_integral hgis] at hi
  have hp : Integrable (fun x => (g x : ℂ) * F x) := by
    simpa using integrable_test_pairing hF hgd.continuous hgc' hgs'
  have hpr : Integrable (fun x => g x • F x) := by
    simpa only [Complex.real_smul] using hp
  apply Complex.ext
  · have hre := integral_re hpr
    simp only [RCLike.re_eq_complex_re] at hre
    rw [← hre]
    simpa [Complex.real_smul] using hr
  · have him := integral_im hpr
    simp only [RCLike.im_eq_complex_im] at him
    rw [← him]
    simpa [Complex.real_smul, Complex.mul_re, Complex.mul_im] using hi

end FoliationQM.OpenFundamentalLemma
