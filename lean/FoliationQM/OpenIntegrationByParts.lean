module

public import FoliationQM.FlatIntegrationByParts
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Interior-test integration by parts

Sources: v13 `thm:kahler` and `eq:master_variational_equivalence`.
The background field has C² regularity only at points of the domain. A
compact test whose closed support lies inside the domain eliminates all
boundary terms, even when the domain has an irregular boundary. The
integrals use the restriction of flat Lebesgue volume to the domain.
-/
@[expose] public section

namespace FoliationQM.OpenIntegrationByParts

open MeasureTheory PolarSecondDifferential ActionVariation FlatIntegrationByParts
open scoped ComplexConjugate Topology

/-- Local C² regularity gives local C¹ regularity of each constant directional derivative. -/
theorem contDiffAt_directionalDerivative {f : Covector → ℂ} {x : Covector}
    (hf : ContDiffAt ℝ 2 f x) (v : Covector) :
    ContDiffAt ℝ 1 (directionalDerivative f v) x :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

/-- The actual flat wave operator is continuous at every C² point. -/
theorem continuousAt_box {f : Covector → ℂ} {x : Covector}
    (hf : ContDiffAt ℝ 2 f x) (e : Fin 4 → Covector) :
    ContinuousAt (box f e) x := by
  have h (μ : Fin 4) : ContinuousAt (secondDirectionalDerivative f (e μ)) x :=
    ((contDiffAt_directionalDerivative hf (e μ)).fderiv_right (m := 0)
      (by norm_num)).continuousAt.clm_apply continuousAt_const
  exact ((h 0).sub (h 1)).sub (h 2) |>.sub (h 3)

/-- The Klein--Gordon operator is continuous on a domain under local C² regularity. -/
theorem continuousOn_kgOperator (p : MassiveParameters) {U : Set Covector}
    {ψ : Covector → ℂ} (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (e : Fin 4 → Covector) : ContinuousOn (kgOperator p ψ e) U := by
  intro x hx
  exact (((continuousAt_box (hψ x hx) e).const_mul _).add
    ((hψ x hx).continuousAt.const_mul _)).continuousWithinAt

/-- A compact factor needs regularity of the other factor only on its closed support. -/
theorem integrable_conj_mul_local {f g : Covector → ℂ}
    (hf : Continuous f) (hg : ∀ x ∈ tsupport f, ContinuousAt g x)
    (hc : HasCompactSupport f) : Integrable (fun x => conj (f x) * g x) := by
  have hcontinuous : Continuous (fun x => conj (f x) * g x) := by
    apply continuous_iff_continuousAt.2
    intro x
    by_cases hx : x ∈ tsupport f
    · exact hf.continuousAt.star.mul (hg x hx)
    · apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hx)] with y hy
      simp [hy]
  exact hcontinuous.integrable_of_hasCompactSupport
    ((hc.comp_left (map_zero _)).mul_right)

/-- Local background regularity suffices for global integrability of the
compactly supported derivative product. -/
theorem integrable_derivative_pair_local {U : Set Covector} {f g : Covector → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ U) (v : Covector) :
    Integrable (fun x => conj (directionalDerivative f v x) *
      directionalDerivative g v x) := by
  apply integrable_conj_mul_local
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    _ (hc.fderiv_apply ℝ v)
  intro x hx
  exact (contDiffAt_directionalDerivative
    (hg x (hs (tsupport_fderiv_apply_subset ℝ v hx))) v).continuousAt

/-- A compact interior test has globally integrable pairing with the second
background derivative, without assumptions outside the domain. -/
theorem integrable_second_derivative_pair_local {U : Set Covector}
    {f g : Covector → ℂ} (hf : ContDiff ℝ 1 f)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ U) (v : Covector) :
    Integrable (fun x => conj (f x) * secondDirectionalDerivative g v x) := by
  apply integrable_conj_mul_local hf.continuous _ hc
  intro x hx
  exact ((contDiffAt_directionalDerivative (hg x (hs hx)) v).fderiv_right
    (m := 0) (by norm_num)).continuousAt.clm_apply continuousAt_const

/-- Actual directional integration by parts uses background differentiability
only on the compact test support. -/
theorem integral_derivative_pair_eq_local {U : Set Covector}
    {f g : Covector → ℂ} (hf : ContDiff ℝ 1 f)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ U) (v : Covector) :
    (∫ x, conj (directionalDerivative f v x) * directionalDerivative g v x) =
      -(∫ x, conj (f x) * secondDirectionalDerivative g v x) := by
  have hfc : ContDiff ℝ 1 (fun x => conj (f x)) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp hf
  have hder (x : Covector) :
      fderiv ℝ (fun y => conj (f y)) x v = conj (directionalDerivative f v x) :=
    ActionDensity.fderiv_conj_apply (hf.differentiable (by norm_num) x) v
  have hleft : Integrable (fun x =>
      fderiv ℝ (fun y => conj (f y)) x v * directionalDerivative g v x) := by
    simp_rw [hder]
    exact integrable_derivative_pair_local hf hg hc hs v
  have hright : Integrable (fun x =>
      conj (f x) * fderiv ℝ (directionalDerivative g v) x v) :=
    integrable_second_derivative_pair_local hf hg hc hs v
  have hproduct : Integrable (fun x => conj (f x) * directionalDerivative g v x) :=
    integrable_conj_mul_local hf.continuous
      (fun x hx => (contDiffAt_directionalDerivative (hg x (hs hx)) v).continuousAt) hc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hleft hright hproduct
    (fun x _ => hfc.differentiable (by norm_num) x)
    (fun x hx => (contDiffAt_directionalDerivative
      (hg x (hs ((tsupport_comp_subset (g := fun z : ℂ => conj z) (map_zero _) f) hx)))
      v).differentiableAt (by norm_num))
  simp_rw [hder] at h
  change (∫ x, conj (f x) * secondDirectionalDerivative g v x) =
    -(∫ x, conj (directionalDerivative f v x) * directionalDerivative g v x) at h
  exact (neg_neg _).symm.trans (congrArg Neg.neg h.symm)

/-- The interior-test action pairing is globally integrable despite arbitrary
behavior of the background outside the domain. -/
theorem integrable_fieldPairing_global (p : MassiveParameters) {U : Set Covector}
    {η ψ : Covector → ℂ} (hη : ContDiff ℝ 1 η)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (e : Fin 4 → Covector) :
    Integrable (fieldPairing p η ψ e) := by
  have hk (μ : Fin 4) := integrable_derivative_pair_local hη hψ hc hs (e μ)
  have hm := integrable_conj_mul_local hη.continuous
    (fun x hx => (hψ x (hs hx)).continuousAt) hc
  convert (((hk 0).sub (hk 1)).sub (hk 2) |>.sub (hk 3)).const_mul
      ((p.hbar : ℂ) ^ 2) |>.sub (hm.const_mul ((p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2)) using 1
  ext x
  simp only [fieldPairing, pairing, kineticPairing, Pi.sub_apply]
  ring

/-- The interior-test KG pairing is globally integrable under local C² regularity. -/
theorem integrable_test_kgOperator_global (p : MassiveParameters) {U : Set Covector}
    {η ψ : Covector → ℂ} (hη : ContDiff ℝ 1 η)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (e : Fin 4 → Covector) :
    Integrable (fun x => conj (η x) * kgOperator p ψ e x) := by
  apply integrable_conj_mul_local hη.continuous _ hc
  intro x hx
  exact ((continuousAt_box (hψ x (hs hx)) e).const_mul _).add
    ((hψ x (hs hx)).continuousAt.const_mul _)

/-- The interior-test action pairing is integrable for restricted flat volume. -/
theorem integrable_fieldPairing (p : MassiveParameters) {U : Set Covector}
    {η ψ : Covector → ℂ} (hη : ContDiff ℝ 1 η)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (e : Fin 4 → Covector) :
    IntegrableOn (fieldPairing p η ψ e) U :=
  (integrable_fieldPairing_global p hη hψ hc hs e).integrableOn

/-- The interior-test KG pairing is integrable for restricted flat volume. -/
theorem integrable_test_kgOperator (p : MassiveParameters) {U : Set Covector}
    {η ψ : Covector → ℂ} (hη : ContDiff ℝ 1 η)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (e : Fin 4 → Covector) :
    IntegrableOn (fun x => conj (η x) * kgOperator p ψ e x) U :=
  (integrable_test_kgOperator_global p hη hψ hc hs e).integrableOn

/-- All derivative terms of a test vanish outside its closed support. -/
theorem fieldPairing_zero_of_notMem_tsupport (p : MassiveParameters)
    (η ψ : Covector → ℂ) (e : Fin 4 → Covector) {x : Covector}
    (hx : x ∉ tsupport η) : fieldPairing p η ψ e x = 0 := by
  have hz : η x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hd : fderiv ℝ η x = 0 := fderiv_of_notMem_tsupport ℝ hx
  simp [fieldPairing, pairing, kineticPairing, directionalDerivative, hz, hd]

/-- Local background regularity suffices for the global integral identity
because every pairing is supported inside the compact interior test. -/
theorem integral_fieldPairing_eq_global (p : MassiveParameters) {U : Set Covector} {η ψ : Covector → ℂ}
    (hη : ContDiff ℝ 1 η) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (e : Fin 4 → Covector) :
    (∫ x, fieldPairing p η ψ e x) =
      -(∫ x, conj (η x) * kgOperator p ψ e x) := by
  let k (μ : Fin 4) (x : Covector) :=
    conj (directionalDerivative η (e μ) x) * directionalDerivative ψ (e μ) x
  let b (μ : Fin 4) (x : Covector) :=
    conj (η x) * secondDirectionalDerivative ψ (e μ) x
  let m (x : Covector) := conj (η x) * ψ x
  have hk (μ : Fin 4) : Integrable (k μ) := integrable_derivative_pair_local hη hψ hc hs (e μ)
  have hb (μ : Fin 4) : Integrable (b μ) := integrable_second_derivative_pair_local hη hψ hc hs (e μ)
  have hm : Integrable m := integrable_conj_mul_local hη.continuous
    (fun x hx => (hψ x (hs hx)).continuousAt) hc
  have hibp (μ : Fin 4) : (∫ x, k μ x) = -(∫ x, b μ x) :=
    integral_derivative_pair_eq_local hη hψ hc hs (e μ)
  have hp : fieldPairing p η ψ e = fun x =>
      (p.hbar : ℂ) ^ 2 * (k 0 x - k 1 x - k 2 x - k 3 x) -
        ((p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2) * m x := by
    funext x
    simp only [fieldPairing, pairing, kineticPairing, k, m]
    ring
  have ho : (fun x => conj (η x) * kgOperator p ψ e x) = fun x =>
      (p.hbar : ℂ) ^ 2 * (b 0 x - b 1 x - b 2 x - b 3 x) +
        ((p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2) * m x := by
    funext x
    simp only [kgOperator, box, b, m]
    ring
  have hks : Integrable (fun x => k 0 x - k 1 x - k 2 x - k 3 x) :=
    ((hk 0).sub (hk 1) |>.sub (hk 2) |>.sub (hk 3))
  have hbs : Integrable (fun x => b 0 x - b 1 x - b 2 x - b 3 x) :=
    ((hb 0).sub (hb 1) |>.sub (hb 2) |>.sub (hb 3))
  rw [hp, ho]
  dsimp only
  rw [integral_sub (hks.const_mul _) (hm.const_mul _),
    integral_add (hbs.const_mul _) (hm.const_mul _)]
  simp only [integral_const_mul]
  rw [integral_sub (f := fun x => k 0 x - k 1 x - k 2 x) (g := k 3)
      ((hk 0).sub (hk 1) |>.sub (hk 2)) (hk 3),
    integral_sub (f := fun x => k 0 x - k 1 x) (g := k 2) ((hk 0).sub (hk 1)) (hk 2),
    integral_sub (hk 0) (hk 1),
    integral_sub (f := fun x => b 0 x - b 1 x - b 2 x) (g := b 3)
      ((hb 0).sub (hb 1) |>.sub (hb 2)) (hb 3),
    integral_sub (f := fun x => b 0 x - b 1 x) (g := b 2) ((hb 0).sub (hb 1)) (hb 2),
    integral_sub (hb 0) (hb 1)]
  rw [hibp 0, hibp 1, hibp 2, hibp 3]
  ring


/-- Restricted-volume integration by parts for compact interior tests. No
regularity of the background outside the domain or of its boundary is assumed. -/
theorem integral_fieldPairing_eq (p : MassiveParameters) {U : Set Covector}
    {η ψ : Covector → ℂ} (hη : ContDiff ℝ 1 η)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (e : Fin 4 → Covector) :
    (∫ x in U, fieldPairing p η ψ e x) =
      -(∫ x in U, conj (η x) * kgOperator p ψ e x) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
    fieldPairing_zero_of_notMem_tsupport p η ψ e (fun hx' => hx (hs hx'))),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
  · exact integral_fieldPairing_eq_global p hη hψ hc hs e
  · simp [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hs hx'))]

/-- Real restricted-volume integration by parts identifies the actual action
pairing with the real weak KG pairing on the domain. -/
theorem integral_re_fieldPairing_eq (p : MassiveParameters) {U : Set Covector}
    {η ψ : Covector → ℂ} (hη : ContDiff ℝ 1 η)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (e : Fin 4 → Covector) :
    (∫ x in U, (fieldPairing p η ψ e x).re) =
      -(∫ x in U, (conj (η x) * kgOperator p ψ e x).re) := by
  have h := congrArg Complex.re (integral_fieldPairing_eq p hη hψ hc hs e)
  have hp := integral_re (integrable_fieldPairing p hη hψ hc hs e)
  have hq := integral_re (integrable_test_kgOperator p hη hψ hc hs e)
  simp only [RCLike.re_eq_complex_re] at hp hq
  rw [Complex.neg_re, ← hp, ← hq] at h
  exact h

end FoliationQM.OpenIntegrationByParts
