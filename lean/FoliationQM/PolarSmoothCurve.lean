module

public import FoliationQM.CompactPerturbation
public import FoliationQM.PolarTestVariations

/-!
# Jointly smooth affine density and phase variations

Source: v13 `thm:kahler`. These are the literal polar curves with density
`ρ + t * a` and real action phase `S + t * b`. Compact support supplies a
single parameter interval preserving positivity, even without a global
positive lower bound on the background. The actual joint Fréchet derivative
in the time direction realizes the previously proved polar tangent.
-/
@[expose] public section

namespace FoliationQM.PolarSmoothCurve

open ActionDensity PolarTangentEquiv PolarTestVariations
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual polar field under affine density and action-phase variations,
viewed jointly as a function of the real parameter and spatial point. -/
noncomputable def curve (p : MassiveParameters) (ρ S a b : E → ℝ)
    (z : ℝ × E) : ℂ :=
  actionField p (fun x => ρ x + z.1 * a x) (fun x => S x + z.1 * b x) z.2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- At parameter zero the nonlinear curve is exactly its background. -/
theorem curve_zero (p : MassiveParameters) (ρ S a b : E → ℝ) (x : E) :
    curve p ρ S a b (0, x) = actionField p ρ S x := by
  simp [curve, actionField]

/-- Joint smoothness holds wherever the varied density is positive. -/
theorem contDiffAt_curve (p : MassiveParameters) {ρ S a b : E → ℝ}
    {n : WithTop ℕ∞} (hρ : ContDiff ℝ n ρ) (hS : ContDiff ℝ n S)
    (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n b) (z : ℝ × E)
    (hpos : 0 < ρ z.2 + z.1 * a z.2) :
    ContDiffAt ℝ n (curve p ρ S a b) z := by
  have hr : ContDiff ℝ n (fun w : ℝ × E => ρ w.2 + w.1 * a w.2) :=
    (hρ.comp contDiff_snd).add (contDiff_fst.mul (ha.comp contDiff_snd))
  have hs : ContDiff ℝ n (fun w : ℝ × E => S w.2 + w.1 * b w.2) :=
    (hS.comp contDiff_snd).add (contDiff_fst.mul (hb.comp contDiff_snd))
  have hR := Complex.ofRealCLM.contDiff.contDiffAt.comp z
    (hr.contDiffAt.sqrt (ne_of_gt hpos))
  have hSc := Complex.ofRealCLM.contDiff.contDiffAt.comp z
    (hs.contDiffAt.div_const p.hbar)
  exact hR.mul ((hSc.mul (contDiffAt_const (c := Complex.I))).cexp)

/-- Compact density support gives a uniform positive interval with joint
smoothness at every parameter and spatial point in that interval. -/
theorem exists_pos_contDiffAt_curve (p : MassiveParameters) {ρ S a b : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpos : ∀ x, 0 < ρ x) (hca : HasCompactSupport a) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x,
      0 < ρ x + t * a x ∧ ContDiffAt ℝ ∞ (curve p ρ S a b) (t, x) := by
  obtain ⟨ε, hε, hp⟩ := CompactPerturbation.exists_pos_affine
    hρ.continuous hpos ha.continuous hca
  exact ⟨ε, hε, fun t ht x => ⟨hp t ht x,
    contDiffAt_curve p hρ hS ha hb (t, x) (hp t ht x)⟩⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The actual scalar-parameter derivative at zero is the polar tangent. -/
theorem hasDerivAt_curve_zero (p : MassiveParameters) (ρ S a b : E → ℝ)
    (x : E) (hpos : 0 < ρ x) :
    HasDerivAt (fun t : ℝ => curve p ρ S a b (t, x))
      (testTangent p ρ S a b x) 0 :=
  hasDerivAt_polarVariation p (ρ x) (S x) (a x) (b x) hpos

/-- The total Fréchet derivative on parameter-space-time realizes the same
polar tangent when applied to the parameter direction `(1, 0)`. -/
theorem fderiv_curve_time_zero (p : MassiveParameters) {ρ S a b : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (x : E) (hpos : 0 < ρ x) :
    fderiv ℝ (curve p ρ S a b) (0, x) (1, 0) = testTangent p ρ S a b x := by
  have hcd := contDiffAt_curve p hρ hS ha hb (0, x) (by simpa using hpos)
  have hp : HasDerivAt (fun t : ℝ => (t, x)) ((1 : ℝ), (0 : E)) 0 := by
    simpa using (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℝ) x).hasDerivAt
  have hd : HasFDerivAt (curve p ρ S a b)
      (fderiv ℝ (curve p ρ S a b) (0, x)) (0, x) :=
    (hcd.differentiableAt (by simp)).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => curve p ρ S a b (t, x))
      (fderiv ℝ (curve p ρ S a b) (0, x) (1, 0)) 0 :=
    HasFDerivAt.comp_hasDerivAt (l := curve p ρ S a b)
      (l' := fderiv ℝ (curve p ρ S a b) (0, x)) 0 hd hp
  exact hc.unique (hasDerivAt_curve_zero p ρ S a b x hpos)

omit [NormedSpace ℝ E] in
/-- The union of the two variation supports is a single compact spatial set. -/
theorem isCompact_variation_support {a b : E → ℝ}
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) :
    IsCompact (tsupport a ∪ tsupport b) := hca.union hcb

omit [NormedSpace ℝ E] in
/-- Outside the two variation supports the curve equals its background at
every parameter, independently of the positivity interval. -/
theorem curve_eq_base_of_not_mem (p : MassiveParameters) (ρ S a b : E → ℝ)
    {x : E} (hx : x ∉ tsupport a ∪ tsupport b) (t : ℝ) :
    curve p ρ S a b (t, x) = actionField p ρ S x := by
  have ha : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
  have hb : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
  simp [curve, actionField, PolarDifferential.polarField, ha, hb]

omit [NormedSpace ℝ E] in
/-- The background equality holds on a spatial neighborhood simultaneously
for every parameter outside the fixed union of topological supports. -/
theorem eventually_curve_eq_base_of_not_mem (p : MassiveParameters)
    (ρ S a b : E → ℝ) {x : E} (hx : x ∉ tsupport a ∪ tsupport b) :
    ∀ᶠ y in 𝓝 x, ∀ t : ℝ, curve p ρ S a b (t, y) = actionField p ρ S y := by
  have ha := notMem_tsupport_iff_eventuallyEq.mp (show x ∉ tsupport a from
    fun h => hx (Or.inl h))
  have hb := notMem_tsupport_iff_eventuallyEq.mp (show x ∉ tsupport b from
    fun h => hx (Or.inr h))
  filter_upwards [ha, hb] with y hay hby t
  simp only [Pi.zero_apply] at hay hby
  simp [curve, actionField, PolarDifferential.polarField, hay, hby]

omit [NormedSpace ℝ E] in
/-- The same equality is local in the joint parameter-space topology. -/
theorem eventually_curve_eq_base_prod_of_not_mem (p : MassiveParameters)
    (ρ S a b : E → ℝ) {x : E} (hx : x ∉ tsupport a ∪ tsupport b) (t : ℝ) :
    curve p ρ S a b =ᶠ[𝓝 (t, x)] (fun z => actionField p ρ S z.2) := by
  have h := (continuous_snd.tendsto (t, x)).eventually
    (eventually_curve_eq_base_of_not_mem p ρ S a b hx)
  filter_upwards [h] with z hz using hz z.1

/-- Every spatial derivative agrees with the background derivative away
from the fixed variation support. No regularity is hidden in this local
equality of the actual totalized Fréchet derivatives. -/
theorem fderiv_curve_space_of_not_mem (p : MassiveParameters) (ρ S a b : E → ℝ)
    {x : E} (hx : x ∉ tsupport a ∪ tsupport b) (t : ℝ) :
    fderiv ℝ (fun y => curve p ρ S a b (t, y)) x =
      fderiv ℝ (actionField p ρ S) x := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [eventually_curve_eq_base_of_not_mem p ρ S a b hx] with y hy
    using hy t

/-- The parameter-direction derivative vanishes outside the fixed spatial
support. This remains true for the totalized derivative without any smoothness
hypothesis, because the parameter slice there is exactly constant. -/
theorem fderiv_curve_time_of_not_mem (p : MassiveParameters) (ρ S a b : E → ℝ)
    {x : E} (hx : x ∉ tsupport a ∪ tsupport b) (t : ℝ) :
    fderiv ℝ (curve p ρ S a b) (t, x) (1, 0) = 0 := by
  by_cases hd : DifferentiableAt ℝ (curve p ρ S a b) (t, x)
  · have hp : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : E)) t := by
      simpa using (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x).hasDerivAt
    have hc : HasDerivAt (fun s : ℝ => curve p ρ S a b (s, x))
        (fderiv ℝ (curve p ρ S a b) (t, x) (1, 0)) t :=
      HasFDerivAt.comp_hasDerivAt (l := curve p ρ S a b)
        (l' := fderiv ℝ (curve p ρ S a b) (t, x)) t hd.hasFDerivAt hp
    have heq : (fun s : ℝ => curve p ρ S a b (s, x)) =
        (fun _ : ℝ => actionField p ρ S x) :=
      funext (curve_eq_base_of_not_mem p ρ S a b hx)
    rw [heq] at hc
    exact hc.unique (hasDerivAt_const t (actionField p ρ S x))
  · simp only [fderiv_zero_of_not_differentiableAt hd, zero_apply]

omit [NormedSpace ℝ E] in
/-- The support of every finite change lies in the same two test supports. -/
theorem tsupport_curve_sub_subset (p : MassiveParameters) (ρ S a b : E → ℝ) (t : ℝ) :
    tsupport (fun x => curve p ρ S a b (t, x) - actionField p ρ S x) ⊆
      tsupport a ∪ tsupport b := by
  apply closure_minimal _ ((isClosed_tsupport a).union (isClosed_tsupport b))
  intro x hx
  by_contra h
  exact hx (sub_eq_zero.mpr (curve_eq_base_of_not_mem p ρ S a b h t))

/-- The velocity field has support in the same compact spatial set,
uniformly in the parameter. -/
theorem tsupport_curve_time_subset (p : MassiveParameters) (ρ S a b : E → ℝ) (t : ℝ) :
    tsupport (fun x => fderiv ℝ (curve p ρ S a b) (t, x) (1, 0)) ⊆
      tsupport a ∪ tsupport b := by
  apply closure_minimal _ ((isClosed_tsupport a).union (isClosed_tsupport b))
  intro x hx
  by_contra h
  exact hx (fderiv_curve_time_of_not_mem p ρ S a b h t)

/-- Each parameter velocity has compact support whenever the two real
variations do. -/
theorem hasCompactSupport_curve_time (p : MassiveParameters) (ρ S : E → ℝ)
    {a b : E → ℝ} (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (t : ℝ) :
    HasCompactSupport (fun x => fderiv ℝ (curve p ρ S a b) (t, x) (1, 0)) :=
  (isCompact_variation_support hca hcb).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_curve_time_subset p ρ S a b t)

omit [NormedSpace ℝ E] in
/-- Each finite-parameter change has compact support in that same set. -/
theorem hasCompactSupport_curve_sub (p : MassiveParameters) (ρ S : E → ℝ)
    {a b : E → ℝ} (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (t : ℝ) :
    HasCompactSupport (fun x => curve p ρ S a b (t, x) - actionField p ρ S x) := by
  apply HasCompactSupport.intro (isCompact_variation_support hca hcb)
  intro x hx
  rw [curve_eq_base_of_not_mem p ρ S a b hx t, sub_self]

end FoliationQM.PolarSmoothCurve
