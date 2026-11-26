module
public import FoliationQM.ScaledChiralAction
public import FoliationQM.RelativeActionVariation

/-!
# Compact variations of a complex scalar in a fixed chiral field

For v13 `thm:dirac_lift`, the parameter velocity is the Fréchet derivative
of the actual joint family. Its change is supported in a common compact
set inside the spacetime domain. This gives finite density increments
and permits differentiation of the chiral correction under the integral.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff ComplexConjugate
namespace FoliationQM.TwistedScalarCurve
open Set MeasureTheory DiracFieldDensity SmoothActionDensity ScaledChiralAction TwistedScalarDensity

/-- An admissible jointly smooth compact interior variation through the given complex scalar. -/
structure Variation (U : Set Covector) (z : Covector → ℂ) where
  family : ℝ × Covector → ℂ
  params : Set ℝ
  params_open : IsOpen params
  zero_mem : 0 ∈ params
  carrier : Set Covector
  compact : IsCompact carrier
  interior : carrier ⊆ U
  initial : ∀ x, family (0, x) = z x
  smooth : ∀ t ∈ params, ∀ x ∈ U, ContDiffAt ℝ ∞ family (t, x)
  fixed : ∀ t ∈ params, ∀ x ∉ carrier, family (t, x) = z x

variable {U : Set Covector} {z : Covector → ℂ} (V : Variation U z)

/-- The original field is exactly the zero slice. -/
theorem slice_zero : slice V.family 0 = z := funext V.initial

/-- Outside the common carrier all parameter slices agree with the initial slice. -/
theorem fixed_initial (t : ℝ) (ht : t ∈ V.params) (x : Covector) (hx : x ∉ V.carrier) :
    V.family (t,x) = V.family (0,x) := (V.fixed t ht x hx).trans (V.initial x).symm

/-- Every allowed slice is locally smooth at each interior point. -/
theorem slice_smooth {t : ℝ} (ht : t ∈ V.params) {x : Covector} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (slice V.family t) x := contDiffAt_slice (V.smooth t ht x hx)

/-- The existence of an admissible variation ensures interior smoothness of its background. -/
theorem base_smooth (V : Variation U z) {x : Covector} (hx : x ∈ U) : ContDiffAt ℝ ∞ z x := by
  rw [← slice_zero V]
  exact slice_smooth V V.zero_mem hx

/-- The genuine parameter velocity vanishes outside the compact carrier at allowed parameters. -/
theorem velocity_zero {t : ℝ} (ht : t ∈ V.params) {x : Covector} (hx : x ∉ V.carrier) :
    velocity V.family t x = 0 :=
  OpenActionVariation.parameterDerivative_zero_of_eq_outside V.params_open ht hx (fixed_initial V)

/-- The closed support of the actual velocity lies inside the compact interior carrier. -/
theorem velocity_tsupport {t : ℝ} (ht : t ∈ V.params) : tsupport (velocity V.family t) ⊆ V.carrier :=
  closure_minimal (fun _ hx => Classical.byContradiction fun hn => hx (velocity_zero V ht hn)) V.compact.isClosed

/-- The actual parameter velocity is globally compactly supported. -/
theorem velocity_compact {t : ℝ} (ht : t ∈ V.params) : HasCompactSupport (velocity V.family t) :=
  V.compact.of_isClosed_subset (isClosed_tsupport _) (velocity_tsupport V ht)

/-- Smoothness inside the region and compact interior support make the velocity a smooth global test. -/
theorem velocity_smooth {t : ℝ} (ht : t ∈ V.params) : ContDiff ℝ ∞ (velocity V.family t) :=
  OpenPolarVariations.contDiff_of_tsupport_subset (fun x hx => contDiffAt_velocity (V.smooth t ht x hx))
    ((velocity_tsupport V ht).trans V.interior)

/-- Any compact smooth scalar test yields an admissible jointly smooth affine family. -/
def affineVariation (η : Covector → ℂ) (hz : ∀ x ∈ U, ContDiffAt ℝ ∞ z x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) : Variation U z where
  family q := z q.2 + (q.1 : ℂ)*η q.2
  params := univ
  params_open := isOpen_univ
  zero_mem := mem_univ _
  carrier := tsupport η
  compact := hc
  interior := hs
  initial x := by simp
  smooth t _ x hx := ((hz x hx).comp (t,x) contDiffAt_snd).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp (t,x) contDiffAt_fst).mul (hη.contDiffAt.comp (t,x) contDiffAt_snd))
  fixed t _ x hx := by simp [image_eq_zero_of_notMem_tsupport hx]

/-- Every compact scalar test is the actual parameter velocity of its affine variation throughout U. -/
theorem affine_velocity (η : Covector → ℂ) (hz : ∀ x ∈ U, ContDiffAt ℝ ∞ z x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (t : ℝ) {x : Covector} (hx : x ∈ U) :
    velocity (affineVariation η hz hη hc hs).family t x = η x := by
  let W := affineVariation η hz hη hc hs
  apply (hasDerivAt_slice_time ((W.smooth t (mem_univ t) x hx).differentiableAt (by simp))).unique
  change HasDerivAt (fun r : ℝ => z x + (r : ℂ) * η x) (η x) t
  simpa using ((Complex.ofRealCLM.hasFDerivAt (x := t)).hasDerivAt.mul_const (η x)).const_add (z x)

variable (p : MassiveParameters) {β : Covector → ℝ}

private theorem integrableOn_scalar_increment (hU : IsOpen U) {t : ℝ} (ht : t ∈ V.params) :
    IntegrableOn (RelativeAction.relativeDensity p z (slice V.family t) coordinateDirections) U := by
  simpa only [slice_zero V] using RelativeActionVariation.integrableOn_relativeDensity_curve p hU V.zero_mem V.smooth V.compact V.interior
    (fixed_initial V) coordinateDirections ht

private theorem integrableOn_correction_increment (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) {t : ℝ} (ht : t ∈ V.params) :
    IntegrableOn (correctionDiff p β z (slice V.family t)) U :=
  integrable_correctionDiff p V.compact V.interior hb (fun _ hx => (base_smooth V hx).continuousAt.continuousWithinAt)
    (fun _ hx => (slice_smooth V ht hx).continuousAt.continuousWithinAt) (V.fixed t ht)

/-- Each admissible spinor density increment is integrable without finiteness of the background action. -/
theorem integrableOn_increment (p : MassiveParameters) (V : Variation U z) (hU : IsOpen U)
    (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) {t : ℝ} (ht : t ∈ V.params) :
    IntegrableOn (fun x => density p β (slice V.family t) x - density p β z x) U := by
  apply ((integrableOn_scalar_increment V p hU ht).sub (integrableOn_correction_increment V p hb ht)).congr_fun _ hU.measurableSet
  intro x hx
  exact (increment_eq p (hb x hx).differentiableAt_one ((base_smooth V hx).differentiableAt (by simp))
    ((slice_smooth V ht hx).differentiableAt (by simp))).symm

/-- At each admissible parameter the relative action splits into a scalar action increment and the integrated correction increment. -/
theorem relative_eq_curve (p : MassiveParameters) (V : Variation U z) (hU : IsOpen U)
    (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) {t : ℝ} (ht : t ∈ V.params) :
    TwistedScalarAction.relativeAction p β z (slice V.family t) U =
      RelativeAction.relativeAction p z (slice V.family t) coordinateDirections U -
        ∫ x in U, correctionDiff p β z (slice V.family t) x :=
  relative_eq p hU.measurableSet (fun x hx => (hb x hx).differentiableAt_one)
    (fun _ hx => (base_smooth V hx).differentiableAt (by simp))
    (fun _ hx => (slice_smooth V ht hx).differentiableAt (by simp)) (integrableOn_scalar_increment V p hU ht)
    (integrableOn_correction_increment V p hb ht)

private theorem normSq_time {f : ℝ → ℂ} {w : ℂ} {t : ℝ} (hf : HasDerivAt f w t) :
    HasDerivAt (fun r => Complex.normSq (f r)) (2 * (conj w * f t).re) t := by
  have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf).mul hf
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  convert! hr using 1
  · funext r
    change Complex.normSq (f r) = (conj (f r) * f r).re
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  · simp [Complex.mul_re, Complex.add_re]
    ring

/-- Differentiation under the compactly supported correction integral uses the true scalar velocity. -/
theorem hasDerivAt_correction_curve (p : MassiveParameters) (V : Variation U z) (hU : IsOpen U)
    (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) :
    HasDerivAt (fun t => ∫ x in U, correctionDiff p β z (slice V.family t) x)
      (2 * ∫ x in U, (conj (velocity V.family 0 x) * ((potential p β x : ℂ) * z x)).re) 0 := by
  let D := fun t x => 2 * (conj (velocity V.family t x) * ((potential p β x : ℂ) * slice V.family t x)).re
  have hp (q : ℝ × Covector) (hx : q.2 ∈ U) :
      ContinuousAt (fun y : ℝ × Covector => potential p β y.2) q :=
    (TwistedScalarAction.continuousAt_potential p (hb q.2 hx)).comp continuousAt_snd
  have h := OpenCompactIntegralVariation.hasDerivAt_integral_of_compact_support hU
    (F := fun t x => correctionDiff p β z (slice V.family t) x) (F' := D)
    (V.params_open.mem_nhds V.zero_mem) (fun q hq =>
      ((hp q hq.2).mul ((Complex.continuous_normSq.continuousAt.comp (V.smooth q.1 hq.1 q.2 hq.2).continuousAt).sub
        ((Complex.continuous_normSq.continuousAt.comp (base_smooth V hq.2).continuousAt).comp continuousAt_snd))).continuousWithinAt)
    (fun q hq => ((Complex.continuous_re.continuousAt.comp
      ((contDiffAt_jointVelocity (V.smooth q.1 hq.1 q.2 hq.2)).continuousAt.star.mul
        ((Complex.continuous_ofReal.continuousAt.comp (hp q hq.2)).mul (V.smooth q.1 hq.1 q.2 hq.2).continuousAt))).const_mul 2).continuousWithinAt)
    V.compact V.interior (fun t ht x _ hx => by simp [D, velocity_zero V ht hx]) (fun t ht x hx => by
      have hd := (((normSq_time (hasDerivAt_slice_time ((V.smooth t ht x hx).differentiableAt (by simp)))).sub_const
        (Complex.normSq (z x))).const_mul (potential p β x))
      convert hd using 1
      · rfl
      · unfold D
        simp [Complex.mul_re, Complex.mul_im]
        ring)
    (by simp [correctionDiff, slice_zero])
  simpa only [D, slice_zero, integral_const_mul] using h.2

end FoliationQM.TwistedScalarCurve
