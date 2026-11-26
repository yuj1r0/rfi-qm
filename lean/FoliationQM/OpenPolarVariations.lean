module

public import FoliationQM.PolarSmoothCurve

/-!
# Compact polar tests on an open positive-density chart

Source: v13 `thm:kahler`. Background fields need only be smooth and positive
on the supplied open region. Tests have compact topological support inside
that region. Their zero germs outside the support give global smooth test
fields without any extension assumption on the background.
-/
@[expose] public section

namespace FoliationQM.OpenPolarVariations

open ActionDensity PolarTangentEquiv PolarTestVariations PolarSmoothCurve
open scoped Topology ContDiff ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local regularity on a set containing the topological support gives global
regularity, since the function is locally zero away from its support. -/
theorem contDiff_of_tsupport_subset {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {U : Set E} {n : WithTop ℕ∞}
    (hf : ∀ x ∈ U, ContDiffAt ℝ n f x) (hs : tsupport f ⊆ U) :
    ContDiff ℝ n f := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hf x hx
  · have hn : x ∉ tsupport f := fun h => hx (hs h)
    exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

/-- The polar field is locally smooth at every positive regular point. -/
theorem contDiffAt_actionField (p : MassiveParameters) {ρ S : E → ℝ}
    {n : WithTop ℕ∞} {x : E} (hρ : ContDiffAt ℝ n ρ x)
    (hS : ContDiffAt ℝ n S x) (hpos : 0 < ρ x) :
    ContDiffAt ℝ n (actionField p ρ S) x := by
  have hR := Complex.ofRealCLM.contDiff.contDiffAt.comp x (hρ.sqrt (ne_of_gt hpos))
  have hSc := Complex.ofRealCLM.contDiff.contDiffAt.comp x (hS.div_const p.hbar)
  exact hR.mul ((hSc.mul (contDiffAt_const (c := Complex.I))).cexp)

omit [NormedSpace ℝ E] in
/-- The forward polar tangent introduces no support outside its two tests. -/
theorem tsupport_testTangent_subset (p : MassiveParameters) (ρ S a b : E → ℝ) :
    tsupport (testTangent p ρ S a b) ⊆ tsupport a ∪ tsupport b := by
  apply closure_minimal _ ((isClosed_tsupport a).union (isClosed_tsupport b))
  intro x hx
  by_contra hn
  have ha := image_eq_zero_of_notMem_tsupport (show x ∉ tsupport a from fun h => hn (Or.inl h))
  have hb := image_eq_zero_of_notMem_tsupport (show x ∉ tsupport b from fun h => hn (Or.inr h))
  exact hx (by simp [testTangent, tangent, ha, hb])

/-- A polar-induced test is globally smooth when its real tests are supported
inside the region where the background is smooth and positive. -/
theorem contDiff_testTangent (p : MassiveParameters) {ρ S a b : E → ℝ}
    {U : Set E} {n : WithTop ℕ∞}
    (hρ : ∀ x ∈ U, ContDiffAt ℝ n ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ n S x)
    (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) :
    ContDiff ℝ n (testTangent p ρ S a b) := by
  apply contDiff_of_tsupport_subset (U := U) _
    ((tsupport_testTangent_subset p ρ S a b).trans (Set.union_subset hsa hsb))
  intro x hx
  have hden : (2 : ℝ) * ρ x ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt (hpos x hx))
  exact (contDiffAt_actionField p (hρ x hx) (hS x hx) (hpos x hx)).mul
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (ha.contDiffAt.div (contDiffAt_const.mul (hρ x hx)) hden)).add
      (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (hb.contDiffAt.div_const p.hbar))))

omit [NormedSpace ℝ E] in
/-- The inverse density test has support contained in the complex test. -/
theorem tsupport_densityVariation_subset (ψ η : E → ℂ) :
    tsupport (fun x => densityVariation (ψ x) (η x)) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro x hx
  by_contra hn
  exact hx (by simp [densityVariation, image_eq_zero_of_notMem_tsupport hn])

omit [NormedSpace ℝ E] in
/-- The inverse phase test has support contained in the complex test. -/
theorem tsupport_phaseVariation_subset (p : MassiveParameters) (ρ : E → ℝ) (ψ η : E → ℂ) :
    tsupport (fun x => phaseVariation p (ρ x) (ψ x) (η x)) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro x hx
  by_contra hn
  exact hx (by simp [phaseVariation, image_eq_zero_of_notMem_tsupport hn])

/-- Every compact complex test inside the chart has globally smooth compact
real inverse tests supported there, with exact tangent reconstruction on U. -/
theorem exists_testTangent (p : MassiveParameters) {ρ S : E → ℝ} {U : Set E}
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) {η : E → ℂ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    ∃ a b : E → ℝ, ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      HasCompactSupport a ∧ HasCompactSupport b ∧ tsupport a ⊆ U ∧ tsupport b ⊆ U ∧
        ∀ x ∈ U, testTangent p ρ S a b x = η x := by
  let ψ := actionField p ρ S
  have hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x :=
    fun x hx => contDiffAt_actionField p (hρ x hx) (hS x hx) (hpos x hx)
  have hsa := (tsupport_densityVariation_subset ψ η).trans hs
  have hsb := (tsupport_phaseVariation_subset p ρ ψ η).trans hs
  refine ⟨fun x => densityVariation (ψ x) (η x),
    fun x => phaseVariation p (ρ x) (ψ x) (η x), ?_, ?_,
    hasCompactSupport_densityVariation ψ hc, hasCompactSupport_phaseVariation p ρ ψ hc,
    hsa, hsb, ?_⟩
  · apply contDiff_of_tsupport_subset (U := U) _ hsa
    intro x hx
    exact contDiffAt_const.mul (Complex.reCLM.contDiff.contDiffAt.comp x
      ((Complex.conjCLE.contDiff.contDiffAt.comp x (hψ x hx)).mul hη.contDiffAt))
  · apply contDiff_of_tsupport_subset (U := U) _ hsb
    intro x hx
    exact (contDiffAt_const.mul (Complex.imCLM.contDiff.contDiffAt.comp x
      ((Complex.conjCLE.contDiff.contDiffAt.comp x (hψ x hx)).mul hη.contDiffAt))).div
        (hρ x hx) (ne_of_gt (hpos x hx))
  · intro x hx
    exact tangent_inverse p (hpos x hx)
      (actionField_conj_mul p ρ S x (hpos x hx).le) (η x)

/-- The polar image of affine real tests is jointly smooth whenever the
background is locally smooth and its varied density is positive. -/
theorem contDiffAt_curve (p : MassiveParameters) {ρ S a b : E → ℝ}
    {n : WithTop ℕ∞} (z : ℝ × E)
    (hρ : ContDiffAt ℝ n ρ z.2) (hS : ContDiffAt ℝ n S z.2)
    (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n b)
    (hpos : 0 < ρ z.2 + z.1 * a z.2) :
    ContDiffAt ℝ n (curve p ρ S a b) z := by
  have hr : ContDiffAt ℝ n (fun w : ℝ × E => ρ w.2 + w.1 * a w.2) z :=
    (hρ.comp z contDiffAt_snd).add (contDiffAt_fst.mul (ha.contDiffAt.comp z contDiffAt_snd))
  have hs : ContDiffAt ℝ n (fun w : ℝ × E => S w.2 + w.1 * b w.2) z :=
    (hS.comp z contDiffAt_snd).add (contDiffAt_fst.mul (hb.contDiffAt.comp z contDiffAt_snd))
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z (hr.sqrt (ne_of_gt hpos))).mul
    (((Complex.ofRealCLM.contDiff.contDiffAt.comp z (hs.div_const p.hbar)).mul
      (contDiffAt_const (c := Complex.I))).cexp)

/-- Compact tests supported inside a locally positive chart give one uniform
positive parameter interval, with joint smoothness throughout that chart. -/
theorem exists_pos_contDiffAt_curve (p : MassiveParameters) {ρ S a b : E → ℝ} {U : Set E}
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hca : HasCompactSupport a) (hsa : tsupport a ⊆ U) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x ∈ U,
      0 < ρ x + t * a x ∧ ContDiffAt ℝ ∞ (curve p ρ S a b) (t, x) := by
  have hsupp : tsupport (fun x => a x / ρ x) ⊆ tsupport a := by
    apply closure_minimal _ (isClosed_tsupport a)
    intro x hx
    by_contra hn
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hn])
  have hratio : ContDiff ℝ ∞ (fun x => a x / ρ x) := by
    apply contDiff_of_tsupport_subset (U := U) _ (hsupp.trans hsa)
    intro x hx
    exact ha.contDiffAt.div (hρ x hx) (ne_of_gt (hpos x hx))
  have hcompact : HasCompactSupport (fun x => a x / ρ x) :=
    hca.of_isClosed_subset (isClosed_tsupport _) hsupp
  obtain ⟨ε, hε, hbound⟩ := CompactPerturbation.exists_uniform_smul_norm_lt
    hratio.continuous hcompact (r := 1) zero_lt_one
  refine ⟨ε, hε, ?_⟩
  intro t ht x hx
  have hbnd := hbound t ht x
  simp only [smul_eq_mul, Real.norm_eq_abs] at hbnd
  have hp : 0 < ρ x * (1 + t * (a x / ρ x)) :=
    mul_pos (hpos x hx) (by linarith [(abs_lt.mp hbnd).1])
  have heq : ρ x * (1 + t * (a x / ρ x)) = ρ x + t * a x := by
    field_simp [ne_of_gt (hpos x hx)]
  rw [heq] at hp
  exact ⟨hp, contDiffAt_curve p (t, x) (hρ x hx) (hS x hx) ha hb hp⟩

/-- At an interior positive regular point the actual total parameter velocity
of the affine polar curve is its explicit tangent. -/
theorem fderiv_curve_time_zero (p : MassiveParameters) {ρ S a b : E → ℝ} {x : E}
    (hρ : ContDiffAt ℝ ∞ ρ x) (hS : ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : 0 < ρ x) :
    fderiv ℝ (curve p ρ S a b) (0, x) (1, 0) = testTangent p ρ S a b x := by
  have hcd := contDiffAt_curve p (0, x) hρ hS ha hb (by simpa using hpos)
  have hp := (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℝ) x).hasDerivAt
  have hd := (hcd.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hp
  exact hd.unique (hasDerivAt_curve_zero p ρ S a b x hpos)

end FoliationQM.OpenPolarVariations
