module

public import FoliationQM.PolarTestVariations
public import FoliationQM.PolarAffineChart
public import FoliationQM.RestPlaneWave

/-!
# Integrated action in real polar coordinates

Source: v13 `thm:kahler`. The functional here is the actual integral of the
source's density/phase/log-density expression. All spacetime derivatives
are real Frechet derivatives, and all integrals use Lebesgue volume on R4.
-/
@[expose] public section

namespace FoliationQM.PolarChartAction

open MeasureTheory ActionDensity ActionVariation PolarTestVariations
open PolarAffineChart StationaryAction FlatIntegrationByParts
open scoped ContDiff Topology ComplexConjugate

/-- The real source integrand, including actual derivatives of log density. -/
noncomputable def hydroIntegrand (p : MassiveParameters) (ρ S : Covector → ℝ)
    (e : Fin 4 → Covector) (x : Covector) : ℝ :=
  hydroDensity p (ρ x) (fun i => fderiv ℝ S x (e i))
    (fun i => fderiv ℝ (fun y => Real.log (ρ y)) x (e i))

/-- The real density/phase action as an actual Lebesgue integral. -/
noncomputable def hydroAction (p : MassiveParameters) (ρ S : Covector → ℝ)
    (e : Fin 4 → Covector) : ℝ := ∫ x, hydroIntegrand p ρ S e x

/-- Pointwise equality gives the exact real source integrand on a positive
differentiable chart; no integral or variation identity is assumed. -/
theorem hydroIntegrand_eq (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x)
    (hpos : 0 < ρ x) (e : Fin 4 → Covector) :
    hydroIntegrand p ρ S e x =
      (fieldPairing p (actionField p ρ S) (actionField p ρ S) e x).re := by
  have hphase : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.const_mul p.hbar⁻¹
  have hd : DifferentiableAt ℝ (actionField p ρ S) x :=
    PolarDifferential.differentiableAt_polarField hρ hphase hpos
  rw [fieldPairing_self_eq_fieldDensity p hd,
    field_action_density_identity p hρ hS hpos]
  rfl

/-- Finiteness of the two actual density expressions is equivalent, so no
totalized nonintegrable integral is used to justify later stationary claims. -/
theorem integrable_hydroIntegrand_iff (p : MassiveParameters) {ρ S : Covector → ℝ}
    (hρ : Differentiable ℝ ρ) (hS : Differentiable ℝ S) (hpos : ∀ x, 0 < ρ x)
    (e : Fin 4 → Covector) :
    Integrable (hydroIntegrand p ρ S e) ↔
      Integrable (fun x => (fieldPairing p (actionField p ρ S) (actionField p ρ S) e x).re) := by
  have heq := funext (fun x => hydroIntegrand_eq p (hρ x) (hS x) (hpos x) e)
  rw [heq]

/-- Equality of the genuine integrated expressions on a differentiable
positive chart. Integrability is separately tracked by the preceding lemma. -/
theorem hydroAction_eq (p : MassiveParameters) {ρ S : Covector → ℝ}
    (hρ : Differentiable ℝ ρ) (hS : Differentiable ℝ S) (hpos : ∀ x, 0 < ρ x)
    (e : Fin 4 → Covector) :
    hydroAction p ρ S e = action p (actionField p ρ S) e volume := by
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun x => hydroIntegrand_eq p (hρ x) (hS x) (hpos x) e))

/-- Each actual inverse-chart variation has finite real action near zero,
equal to the affine complex action on the same whole-domain interval. -/
theorem eventually_integrable_curve_action_eq (p : MassiveParameters)
    {ρ S : Covector → ℝ} {η : Covector → ℂ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S) (hpos : ∀ x, 0 < ρ x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (e : Fin 4 → Covector)
    (hfinite : Integrable (hydroIntegrand p ρ S e)) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Integrable (hydroIntegrand p (curveDensity p ρ S η t) (curveAction p ρ S η t) e) ∧
      hydroAction p (curveDensity p ρ S η t) (curveAction p ρ S η t) e =
        action p (fun x => actionField p ρ S x + t * η x) e volume := by
  have hψ := contDiff_actionField p hρ hS hpos
  have hψ2 : ContDiff ℝ 2 (actionField p ρ S) := hψ.of_le (by norm_num)
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hη2 : ContDiff ℝ 2 η := hη.of_le (by norm_num)
  have hf := (integrable_hydroIntegrand_iff p (hρ.differentiable (by simp))
    (hS.differentiable (by simp)) hpos e).mp hfinite
  have hvar := integrable_variation p (actionField p ρ S) η e volume
    (Filter.Eventually.of_forall (hψ.differentiable (by simp)))
    (Filter.Eventually.of_forall (hη.differentiable (by simp))) hf
    (integrable_fieldPairing p hη1 hψ2 hc e).re
    (integrable_fieldPairing p hη1 hη2 hc e).re
  obtain ⟨ε, hε, hadm⟩ := exists_admissible_curve p hρ hS hpos hη hc
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  obtain ⟨hpost, hρt, hSt⟩ := hadm t ht'
  have heq : actionField p (curveDensity p ρ S η t) (curveAction p ρ S η t) =
      fun x => actionField p ρ S x + t * η x :=
    funext (fun x => curve_reconstruction p ρ S η t x (hpos x))
  have hi := integrable_hydroIntegrand_iff p (hρt.differentiable (by simp))
    (hSt.differentiable (by simp)) hpost e
  have ha := hydroAction_eq p (hρt.differentiable (by simp))
    (hSt.differentiable (by simp)) hpost e
  rw [heq] at hi ha
  exact ⟨hi.mpr (hvar t), ha⟩

/-- The source's actual real functional has the expected derivative along
the proved inverse-chart family, with its integrability justified near zero. -/
theorem hasDerivAt_hydroAction_curve (p : MassiveParameters)
    {ρ S : Covector → ℝ} {η : Covector → ℂ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S) (hpos : ∀ x, 0 < ρ x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (e : Fin 4 → Covector)
    (hfinite : Integrable (hydroIntegrand p ρ S e)) :
    HasDerivAt (fun t : ℝ =>
      hydroAction p (curveDensity p ρ S η t) (curveAction p ρ S η t) e)
      (-2 * ∫ x, (conj (η x) * kgOperator p (actionField p ρ S) e x).re) 0 := by
  have hf := (integrable_hydroIntegrand_iff p (hρ.differentiable (by simp))
    (hS.differentiable (by simp)) hpos e).mp hfinite
  have hd := hasDerivAt_action_eq_kg_pairing p e
    ((contDiff_actionField p hρ hS hpos).of_le (by norm_num)) hη hc hf
  exact hd.congr_of_eventuallyEq
    ((eventually_integrable_curve_action_eq p hρ hS hpos hη hc e hfinite).mono
      (fun _ ht => ht.2))

/-- Stationarity of the real density/phase functional on the explicitly
constructed inverse images of all smooth compact affine complex curves.
This specifies the tested curve class; it is not a definition asserting
stationarity along all affine real density/phase variations. -/
def ChartStationary (p : MassiveParameters) (ρ S : Covector → ℝ)
    (e : Fin 4 → Covector) : Prop :=
  Integrable (hydroIntegrand p ρ S e) ∧
    ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η →
      HasDerivAt (fun t : ℝ =>
        hydroAction p (curveDensity p ρ S η t) (curveAction p ρ S η t) e) 0 0

/-- Transporting all affine complex curves through the actual polar chart
preserves stationarity of the integrated functionals in both directions. -/
theorem chartStationary_iff_stationary (p : MassiveParameters) {ρ S : Covector → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S) (hpos : ∀ x, 0 < ρ x)
    (e : Fin 4 → Covector) :
    ChartStationary p ρ S e ↔ Stationary p (actionField p ρ S) e := by
  have hi := integrable_hydroIntegrand_iff p (hρ.differentiable (by simp))
    (hS.differentiable (by simp)) hpos e
  constructor
  · intro hs
    refine ⟨hi.mp hs.1, ?_⟩
    intro η hη hc
    exact (hs.2 η hη hc).congr_of_eventuallyEq
      ((eventually_integrable_curve_action_eq p hρ hS hpos hη hc e hs.1).mono
        (fun _ ht => ht.2.symm))
  · intro hs
    refine ⟨hi.mpr hs.1, ?_⟩
    intro η hη hc
    exact (hs.2 η hη hc).congr_of_eventuallyEq
      ((eventually_integrable_curve_action_eq p hρ hS hpos hη hc e (hi.mpr hs.1)).mono
        (fun _ ht => ht.2))

/-- The real action's chart-transported stationarity criterion is equivalent
to the normalized source KG equation for standard flat coordinates. -/
theorem chartStationary_iff_kleinGordon (p : MassiveParameters) {ρ S : Covector → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S) (hpos : ∀ x, 0 < ρ x)
    (hfinite : Integrable (hydroIntegrand p ρ S Madelung.coordinateVector)) :
    ChartStationary p ρ S Madelung.coordinateVector ↔ ∀ x,
      PolarSecondDifferential.box (actionField p ρ S) Madelung.coordinateVector x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * actionField p ρ S x) = 0 := by
  rw [chartStationary_iff_stationary p hρ hS hpos Madelung.coordinateVector]
  exact stationary_iff_kleinGordon p
    ((contDiff_actionField p hρ hS hpos).of_le (by norm_num))
    ((integrable_hydroIntegrand_iff p (hρ.differentiable (by simp))
      (hS.differentiable (by simp)) hpos Madelung.coordinateVector).mp hfinite)

/-- The explicit unit-density rest phase has zero real source density. -/
theorem hydroIntegrand_rest (p : MassiveParameters) (x : Covector) :
    hydroIntegrand p (fun _ => 1) (RestPlaneWave.restAction p)
      Madelung.coordinateVector x = 0 := by
  rw [hydroIntegrand_eq p (differentiableAt_const 1)
    ((RestPlaneWave.contDiff_restAction p 1).differentiable (by norm_num) x)
    (by norm_num)]
  exact congrArg Complex.re (RestPlaneWave.fieldPairing_restWave_self p x)

/-- A nonzero concrete instance of real chart-action stationarity: the rest
wave's supplied density/phase coordinates satisfy the new criterion. -/
theorem rest_chartStationary (p : MassiveParameters) :
    ChartStationary p (fun _ => 1) (RestPlaneWave.restAction p)
      Madelung.coordinateVector := by
  apply (chartStationary_iff_stationary p contDiff_const
    (RestPlaneWave.contDiff_restAction p ∞) (fun _ => by norm_num)
    Madelung.coordinateVector).mpr
  exact RestPlaneWave.restWave_stationary p

end FoliationQM.PolarChartAction
