module

public import FoliationQM.ActionVariation
public import FoliationQM.Madelung
public import FoliationQM.StationaryAction
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# A nonzero finite-action example

Source: v13 `thm:kahler`.

The unit-amplitude rest plane wave has action phase `-m c x⁰`, where `x⁰=ct`.
Its kinetic and mass densities cancel pointwise. Thus its full real action
density is integrable even on all spacetime, without requiring the field itself
to decay. This supplies a concrete instance for the flat variation results.
-/
@[expose] public section

namespace FoliationQM.RestPlaneWave

open MeasureTheory PolarSecondDifferential ActionVariation

/-- Rest action phase in the coordinate convention `x⁰=ct`. -/
noncomputable def restAction (p : MassiveParameters) (x : Covector) : ℝ :=
  -(p.m * p.c) * x 0

/-- The unit-amplitude rest plane wave. -/
noncomputable def restWave (p : MassiveParameters) : Covector → ℂ :=
  ActionDensity.actionField p (fun _ => 1) (restAction p)

/-- The rest action phase is smooth to every order. -/
theorem contDiff_restAction (p : MassiveParameters) (n : WithTop ℕ∞) :
    ContDiff ℝ n (restAction p) :=
  contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0)

/-- The actual rest-phase differential is the prescribed time covector. -/
theorem directionalDerivative_restAction (p : MassiveParameters) (x v : Covector) :
    directionalDerivative (restAction p) v x = -(p.m * p.c) * v 0 := by
  have hd : HasFDerivAt (restAction p)
      (-(p.m * p.c) • (ContinuousLinearMap.proj (0 : Fin 4) : Covector →L[ℝ] ℝ)) x :=
    (hasFDerivAt_apply 0 x).const_mul (-(p.m * p.c))
  rw [directionalDerivative, hd.fderiv]
  rfl

/-- The concrete nonzero complex rest wave is smooth to every order. -/
theorem contDiff_restWave (p : MassiveParameters) (n : WithTop ℕ∞) :
    ContDiff ℝ n (restWave p) := by
  have hreal : ContDiff ℝ n (fun x => restAction p x / p.hbar) :=
    (contDiff_restAction p n).div_const p.hbar
  have hc := Complex.ofRealCLM.contDiff.comp hreal
  have he := (hc.mul (contDiff_const (c := Complex.I))).cexp
  change ContDiff ℝ n (fun x => (Real.sqrt (1 : ℝ) : ℂ) * phase (restAction p x / p.hbar))
  simpa only [Real.sqrt_one, Complex.ofReal_one, one_mul, phase,
    Function.comp_def, Complex.ofRealCLM_apply] using he

/-- The rest wave has unit squared modulus, so it is a nontrivial example. -/
theorem restWave_normSq (p : MassiveParameters) (x : Covector) :
    Complex.normSq (restWave p x) = 1 :=
  ActionDensity.polarField_normSq (fun _ => 1) _ x (by norm_num)

/-- The rest-wave example is nowhere zero. -/
theorem restWave_ne_zero (p : MassiveParameters) (x : Covector) :
    restWave p x ≠ 0 := by
  intro h
  have hn := restWave_normSq p x
  rw [h] at hn
  norm_num at hn

/-- Kinetic and mass terms cancel in the actual rest-wave density. -/
theorem fieldPairing_restWave_self (p : MassiveParameters) (x : Covector) :
    fieldPairing p (restWave p) (restWave p) Madelung.coordinateVector x = 0 := by
  have hρ : DifferentiableAt ℝ (fun _ : Covector => (1 : ℝ)) x :=
    differentiableAt_const 1
  have hS := (contDiff_restAction p 1).differentiable (by norm_num) x
  rw [fieldPairing_self_eq_fieldDensity p
    ((contDiff_restWave p 1).differentiable (by norm_num) x)]
  rw [restWave, ActionDensity.field_action_density_identity p hρ hS (by norm_num)]
  have hs (i : Fin 4) : fderiv ℝ (restAction p) x (Madelung.coordinateVector i) =
      -(p.m * p.c) * (Madelung.coordinateVector i) 0 :=
    directionalDerivative_restAction p x _
  simp only [ActionDensity.hydroDensity, minkowski]
  rw [hs 0, hs 1, hs 2, hs 3]
  simp only [Madelung.coordinateVector]
  norm_num [fderiv_fun_const, Pi.single_apply]
  ring

/-- The genuine self-density is integrable for any supplied measure. -/
theorem integrable_restWave_self (p : MassiveParameters) (μ : Measure Covector) :
    Integrable (fun x =>
      (fieldPairing p (restWave p) (restWave p) Madelung.coordinateVector x).re) μ := by
  simp only [fieldPairing_restWave_self, Complex.zero_re]
  exact integrable_zero Covector ℝ μ

/-- The actual integral action of the rest wave is zero for any measure. -/
theorem action_restWave (p : MassiveParameters) (μ : Measure Covector) :
    action p (restWave p) Madelung.coordinateVector μ = 0 := by
  simp only [action, fieldPairing_restWave_self, Complex.zero_re, integral_zero]

/-- The unit-amplitude rest wave satisfies the actual coordinate KG equation. -/
theorem restWave_kg (p : MassiveParameters) (x : Covector) :
    box (restWave p) Madelung.coordinateVector x +
      (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * restWave p x) = 0 := by
  have hs (v : Covector) : directionalDerivative (restAction p) v =
      (fun _ => -(p.m * p.c) * v 0) :=
    funext (fun y => directionalDerivative_restAction p y v)
  have hR : ∀ᶠ y in nhds x, DifferentiableAt ℝ (fun _ : Covector => (1 : ℝ)) y :=
    Filter.Eventually.of_forall (fun _ => differentiableAt_const 1)
  have hS : ∀ᶠ y in nhds x, DifferentiableAt ℝ (restAction p) y :=
    Filter.Eventually.of_forall ((contDiff_restAction p 1).differentiable (by norm_num))
  have hRfirst (v : Covector) :
      directionalDerivative (fun _ : Covector => (1 : ℝ)) v = (fun _ => 0) := by
    funext y
    simp [directionalDerivative]
  have hR2 (i : Fin 4) : DifferentiableAt ℝ
      (directionalDerivative (fun _ : Covector => (1 : ℝ)) (Madelung.coordinateVector i)) x := by
    rw [hRfirst]
    exact differentiableAt_const 0
  have hS2 (i : Fin 4) : DifferentiableAt ℝ
      (directionalDerivative (restAction p) (Madelung.coordinateVector i)) x := by
    rw [hs]
    exact differentiableAt_const _
  have heq : restWave p = Madelung.actionField p (fun _ => 1) (restAction p) := by
    funext y
    simp only [restWave, ActionDensity.actionField, PolarDifferential.polarField,
      Madelung.actionField, amplitudeField, Real.sqrt_one]
  rw [heq, Madelung.kg_eq_zero_iff_madelung_coordinates p hR hS hR2 hS2 (by norm_num)]
  constructor
  · simp only [minkowski, directionalDerivative_restAction, box, secondDirectionalDerivative,
      hRfirst]
    simp only [directionalDerivative, fderiv_fun_const, Pi.zero_apply, zero_apply]
    norm_num [Madelung.coordinateVector, Pi.single_apply]
    ring
  · rw [Madelung.currentDivergence_eq_continuityResidual
      Madelung.coordinateVector (differentiableAt_const 1) hS2]
    simp only [PolarSecondJet.continuityResidual, minkowski, box,
      secondDirectionalDerivative, hs]
    simp only [directionalDerivative, fderiv_fun_const, Pi.zero_apply, zero_apply]
    ring

/-- The nonzero rest wave is stationary under every smooth compactly
supported complex variation of the actual spacetime action. -/
theorem restWave_stationary (p : MassiveParameters) :
    StationaryAction.Stationary p (restWave p) Madelung.coordinateVector :=
  (StationaryAction.stationary_iff_kleinGordon p (contDiff_restWave p 2)
    (integrable_restWave_self p volume)).2 (restWave_kg p)

end FoliationQM.RestPlaneWave
