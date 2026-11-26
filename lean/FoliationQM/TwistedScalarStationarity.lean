module
public import FoliationQM.TwistedScalarVariation
public import FoliationQM.TwistedScalarCurve
public import FoliationQM.OpenFundamentalLemma

/-!
# The field equation of the chiral scalar action

For v13 `thm:dirac_lift`, stationarity of the mass-completed quadratic
action in the complex scalar variable at fixed angle gives the
Klein–Gordon operator plus the true signed chiral potential times the
field. Smooth compact nonlinear families and affine field tests detect
the same equation on the original open domain.
-/

@[expose] public section
noncomputable section
open scoped ContDiff Topology ComplexConjugate
namespace FoliationQM.TwistedScalarStationarity
open MeasureTheory TwistedScalarVariation DiracFieldDensity TwistedScalarCurve
open TwistedScalarAction TwistedScalarDensity

/-- Compact affine variations in the complex scalar field at fixed chiral background. -/
def AffineStationary (p : MassiveParameters) (β : Covector → ℝ) (z : Covector → ℂ) (U : Set Covector) : Prop :=
  ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
    HasDerivAt (fun t : ℝ => relativeAction p β z (fun x => z x + (t : ℂ) * η x) U) 0 0

/-- Relative stationarity along every admissible smooth compact complex scalar family. -/
def StationaryOn (p : MassiveParameters) (β : Covector → ℝ) (z : Covector → ℂ) (U : Set Covector) : Prop :=
  ∀ V : Variation U z, HasDerivAt (fun t => relativeAction p β z (SmoothActionDensity.slice V.family t) U) 0 0

/-- Ordinary stationarity, including finiteness of the actual massive background density. -/
def FiniteStationary (p : MassiveParameters) (β : Covector → ℝ) (z : Covector → ℂ) (U : Set Covector) : Prop :=
  IntegrableOn (density p β z) U ∧
    ∀ V : Variation U z, HasDerivAt (fun t => action p β (SmoothActionDensity.slice V.family t) U) 0 0

variable (p : MassiveParameters) {β : Covector → ℝ} {z : Covector → ℂ} {U : Set Covector}
variable (hU : IsOpen U) (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x)

include hU hb

/-- Affine stationarity is equivalent to vanishing of each true first-derivative test pairing. -/
theorem affine_iff_weak (hz : ∀ x ∈ U, ContDiffAt ℝ 2 z x) :
    AffineStationary p β z U ↔ ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      ∫ x in U, (ActionVariation.fieldPairing p η z coordinateDirections x).re -
        potential p β x * (conj (η x) * z x).re = 0 := by
  constructor
  · intro h η hη hc hs
    have e := (hasDerivAt_weak p hU hb hz hη hc hs).unique (h η hη hc hs)
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  · intro h η hη hc hs
    simpa only [h η hη hc hs, mul_zero] using hasDerivAt_weak p hU hb hz hη hc hs

/-- The compact scalar fundamental lemma recovers the pointwise equation on U. -/
theorem affine_iff_force (hz : ∀ x ∈ U, ContDiffAt ℝ 2 z x) :
    AffineStationary p β z U ↔ ∀ x ∈ U, force p β z x = 0 := by
  constructor
  · intro h
    apply OpenFundamentalLemma.continuousOn_eq_zero_of_test_pairings hU _ (continuousOn_force p hb hz)
    intro η hη hc hs
    have e := (hasDerivAt_residual p hU hb hz hη hc hs).unique (h η hη hc hs)
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  · intro he η hη hc hs
    have hi : (∫ x in U, (conj (η x) * force p β z x).re) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by simp [he x hx])
    simpa only [hi, mul_zero] using hasDerivAt_residual p hU hb hz hη hc hs

/-- Every solution is stationary along every admissible compact smooth scalar curve. -/
theorem stationary_of_force (he : ∀ x ∈ U, force p β z x = 0) : StationaryOn p β z U := by
  intro V
  have hi : (∫ x in U, (conj (SmoothActionDensity.velocity V.family 0 x) * force p β z x).re) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by simp [he x hx])
  simpa only [hi, mul_zero] using hasDerivAt_curve p V hU hb

/-- For a locally smooth background all compact affine tests occur among the smooth curves. -/
theorem stationary_iff_force (hz : ∀ x ∈ U, ContDiffAt ℝ ∞ z x) :
    StationaryOn p β z U ↔ ∀ x ∈ U, force p β z x = 0 := by
  constructor
  · intro h
    apply (affine_iff_force p hU hb (fun x hx => (hz x hx).of_le (by simp))).mp
    intro η hη hc hs
    exact h (affineVariation η hz hη hc hs)
  · exact stationary_of_force p hU hb

/-- On a genuinely finite background the ordinary and relative action criteria agree. -/
theorem finite_iff (hi : IntegrableOn (density p β z) U) :
    FiniteStationary p β z U ↔ StationaryOn p β z U := by
  constructor
  · rintro ⟨_, h⟩ V
    have e := (hasDerivAt_action p V hU hb hi).unique (h V)
    simpa only [e] using hasDerivAt_curve p V hU hb
  · intro h
    refine ⟨hi, fun V => ?_⟩
    have e := (hasDerivAt_curve p V hU hb).unique (h V)
    simpa only [e] using hasDerivAt_action p V hU hb hi

omit hU hb in
/-- The normalized equation displays the signed angle contribution to the mass coefficient. -/
theorem force_factor (p : MassiveParameters) (β : Covector → ℝ) (z : Covector → ℂ) (x : Covector) :
    force p β z x = (p.hbar : ℂ)^2 * (PolarSecondDifferential.box z coordinateDirections x +
      (((p.m^2 * p.c^2 + potential p β x) / p.hbar^2 : ℝ) : ℂ) * z x) := by
  unfold force FlatIntegrationByParts.kgOperator
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr p.hbar_pos.ne']
  ring

/-- Smooth compact stationarity is exactly the normalized massive wave equation with
coefficient (m²c²+V)/ℏ², for the original scalar field throughout U. -/
theorem stationary_iff_wave (hz : ∀ x ∈ U, ContDiffAt ℝ ∞ z x) :
    StationaryOn p β z U ↔ ∀ x ∈ U, PolarSecondDifferential.box z coordinateDirections x +
      (((p.m^2 * p.c^2 + potential p β x) / p.hbar^2 : ℝ) : ℂ) * z x = 0 := by
  rw [stationary_iff_force p hU hb hz]
  have hh : (p.hbar : ℂ)^2 ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr p.hbar_pos.ne')
  simp_rw [force_factor, mul_eq_zero, or_iff_right hh]

end FoliationQM.TwistedScalarStationarity
