module
public import FoliationQM.TwistedScalarAngles
public import FoliationQM.TwistedScalarAction
public import FoliationQM.RelativeStationaryAction
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The chiral action discrepancy on an open spacetime box

For the scalar limit in v13 `thm:dirac_lift`, integrate the true oscillatory
chiral correction over a time interval of length 2π and three unit spatial
intervals. The real angles converge uniformly to zero as their frequencies
increase. Each period contributes the same average squared derivative, giving
a strictly positive discrepancy in the integrated unit-scalar action.
-/

@[expose] public section
noncomputable section
open scoped Topology Matrix.Norms.Operator
namespace FoliationQM.TwistedOscillationIntegral
open Set MeasureTheory Filter TwistedScalarAngles TwistedScalarDensity DiracFieldDensity

/-- The upper endpoint in each physical coordinate. -/
def side (μ : Fin 4) : ℝ := if μ = 0 then 2 * Real.pi else 1

/-- The time interval (0,2π) times three open spatial intervals (0,1). -/
def box : Set Covector := univ.pi fun μ => Ioo 0 (side μ)

/-- The four-dimensional domain of integration is open. -/
theorem isOpen_box : IsOpen box := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

/-- The Lebesgue volume of the full spacetime box is 2π. -/
theorem volume_box : volume box = ENNReal.ofReal (2 * Real.pi) := by
  rw [box, volume_pi_pi]
  simp [side, Fin.prod_univ_four, Real.volume_Ioo]

/-- The small-angle amplitudes are indexed by the positive integer frequencies n+1. -/
def epsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Every member of the oscillatory sequence has positive amplitude. -/
theorem epsilon_pos (n : ℕ) : 0 < epsilon n := by unfold epsilon; positivity

/-- The chiral angles converge uniformly on all spacetime, hence on the integration domain. -/
theorem uniform_angles :
    TendstoUniformly (fun n : ℕ => timeAngle (epsilon n)) (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  have he : Tendsto epsilon atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [he.eventually (gt_mem_nhds hδ)] with n hn x
  simpa only [dist_zero_left, Real.norm_eq_abs] using (timeAngle_bound (epsilon_pos n).le x).trans_lt hn

/-- The actual twisted spinor fields converge uniformly to the constant rest spinor on all spacetime. -/
theorem uniform_fields :
    TendstoUniformly (fun n : ℕ => TwistedScalarField.field (timeAngle (epsilon n)) (fun _ => 1))
      (fun _ => DiracMatrices.restSpinor) atTop := by
  let φ : ℝ → DiracMatrices.Spinor := fun t => TwistedScalarJet.value t 1
  have hc : ContinuousAt φ 0 :=
    (MatrixDifferential.mulVecCLM (ScalarRestKinetic.embed 1)).continuous.continuousAt.comp
      (ChiralDifferential.differentiable_chiral 0).continuousAt
  have h0 : φ 0 = DiracMatrices.restSpinor := by simp [φ, TwistedScalarJet.value_zero, ScalarRestKinetic.embed]
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  obtain ⟨r, hr, h⟩ := Metric.continuousAt_iff.mp hc δ hδ
  filter_upwards [Metric.tendstoUniformly_iff.mp uniform_angles r hr] with n hn x
  change dist DiracMatrices.restSpinor (φ (timeAngle (epsilon n) x)) < δ
  rw [← h0, dist_comm]
  exact h (by simpa [dist_comm] using hn x)

/-- Integrating a time-coordinate function over this box leaves its time integral. -/
theorem integral_time (f : ℝ → ℝ) : (∫ x in box, f (x 0)) = ∫ t in Ioo 0 (2 * Real.pi), f t := by
  let μ : Fin 4 → Measure ℝ := fun i => volume.restrict (Ioo 0 (side i))
  let F : Fin 4 → ℝ → ℝ := fun i => if i = 0 then f else fun _ => 1
  have hproduct := integral_fin_nat_prod_eq_prod (μ := μ) F
  change (∫ x : Covector, f (x 0) ∂volume.restrict box) = _
  rw [box, volume_pi, Measure.restrict_pi_pi]
  change (∫ x : Covector, f (x 0) ∂Measure.pi μ) = _
  have hunit : (∫ _t in Ioo (0 : ℝ) 1, (1 : ℝ)) = 1 := by
    simp [measureReal_def, Real.volume_Ioo]
  simpa [F, μ, side, Fin.prod_univ_four, hunit] using hproduct

/-- The time integral of cos² at each integer frequency is exactly π over the fixed interval. -/
theorem integral_cos_sq_time (n : ℕ) :
    (∫ t in Ioo 0 (2 * Real.pi), Real.cos (t / epsilon n) ^ 2) = Real.pi := by
  have ht : 2 * Real.pi / epsilon n = ((2 * (n + 1) : ℕ) : ℝ) * Real.pi := by
    simp [epsilon]
    ring
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by positivity),
    intervalIntegral.integral_comp_div (fun u => Real.cos u ^ 2) (epsilon_pos n).ne',
    zero_div, integral_cos_sq, ht, Real.sin_nat_mul_pi]
  simp only [Real.cos_zero, Real.sin_zero, mul_zero, sub_zero, zero_add, smul_eq_mul]
  unfold epsilon
  push_cast
  field_simp

/-- The squared time derivative has a fixed positive integral, independently of frequency. -/
theorem potential_integral (p : MassiveParameters) (n : ℕ) :
    (∫ x in box, potential p (timeAngle (epsilon n)) x) = p.hbar^2 * Real.pi / 4 := by
  simp_rw [potential_timeAngle p (epsilon_pos n).ne']
  rw [integral_const_mul, integral_time (fun t => Real.cos (t / epsilon n)^2), integral_cos_sq_time]
  ring

private theorem integrableOn_box_of_continuous {f : Covector → ℝ} (hf : Continuous f) : IntegrableOn f box := by
  have hs : box ⊆ Icc (0 : Covector) side := by
    intro y hy
    exact ⟨fun i => (hy i (mem_univ i)).1.le, fun i => (hy i (mem_univ i)).2.le⟩
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc (a := (0 : Covector)) (b := side))).mono_set hs

/-- The oscillatory correction is genuinely integrable on the spacetime box. -/
theorem integrableOn_potential (p : MassiveParameters) (n : ℕ) :
    IntegrableOn (potential p (timeAngle (epsilon n))) box := by
  apply integrableOn_box_of_continuous
  have he : potential p (timeAngle (epsilon n)) =
      fun x : Covector => p.hbar ^ 2 / 4 * Real.cos (x 0 / epsilon n) ^ 2 :=
    funext (potential_timeAngle p (epsilon_pos n).ne')
  rw [he]
  fun_prop

/-- The ordinary massive scalar density on the unit field is integrable on the box. -/
theorem integrableOn_unit (p : MassiveParameters) :
    IntegrableOn (fun x => (ActionVariation.fieldPairing p (fun _ => 1) (fun _ => 1) coordinateDirections x).re) box := by
  simp_rw [RelativeStationaryAction.unitField_density]
  exact integrableOn_const (by rw [volume_box]; exact ENNReal.ofReal_ne_top)

private theorem unit_density (p : MassiveParameters) (n : ℕ) (x : Covector) :
    density p (timeAngle (epsilon n)) (fun _ => 1) x =
      (ActionVariation.fieldPairing p (fun _ => 1) (fun _ => 1) coordinateDirections x).re -
        potential p (timeAngle (epsilon n)) x := by
  simpa using density_eq_pairing p ((smooth_timeAngle (epsilon n) 1).differentiable (by norm_num) x)
    (differentiableAt_const (1 : ℂ))

/-- The twisted massive density is integrable at every integer frequency on the same box. -/
theorem integrableOn_density (p : MassiveParameters) (n : ℕ) :
    IntegrableOn (density p (timeAngle (epsilon n)) (fun _ => 1)) box := by
  have h := (integrableOn_unit p).sub (integrableOn_potential p n)
  exact h.congr_fun (fun x _ => (unit_density p n x).symm) isOpen_box.measurableSet

/-- The unit scalar field has the ordinary finite action −2πm²c² on the box. -/
theorem scalarAction_unit (p : MassiveParameters) :
    TwistedScalarAction.scalarAction p (fun _ => 1) box = -(2 * Real.pi * (p.m^2 * p.c^2)) := by
  unfold TwistedScalarAction.scalarAction TwistedScalarAction.scalarDensity
  simp_rw [RelativeStationaryAction.unitField_density]
  rw [setIntegral_const, measureReal_def, volume_box, ENNReal.toReal_ofReal (by positivity)]
  simp [smul_eq_mul]

/-- Each twisted action differs from the unit scalar action by the same positive number. -/
theorem action_eq_scalar_sub (p : MassiveParameters) (n : ℕ) :
    TwistedScalarAction.action p (timeAngle (epsilon n)) (fun _ => 1) box =
      TwistedScalarAction.scalarAction p (fun _ => 1) box - p.hbar^2 * Real.pi / 4 := by
  have hc : TwistedScalarAction.correction p (timeAngle (epsilon n)) (fun _ => 1) =
      potential p (timeAngle (epsilon n)) := by
    funext x
    simp [TwistedScalarAction.correction]
  rw [TwistedScalarAction.action_eq p isOpen_box.measurableSet
    (fun x _ => (smooth_timeAngle (epsilon n) 1).differentiable (by norm_num) x)
    (fun _ _ => differentiableAt_const 1) (integrableOn_unit p) (hc ▸ integrableOn_potential p n),
    hc, potential_integral]

/-- Despite uniform smallness of the angles, their finite twisted actions do not converge to the scalar action. -/
theorem not_tendsto_action (p : MassiveParameters) :
    ¬ Tendsto (fun n => TwistedScalarAction.action p (timeAngle (epsilon n)) (fun _ => 1) box) atTop
      (𝓝 (TwistedScalarAction.scalarAction p (fun _ => 1) box)) := by
  intro h
  simp_rw [action_eq_scalar_sub] at h
  have he := tendsto_nhds_unique h tendsto_const_nhds
  have hp : 0 < p.hbar^2 * Real.pi / 4 := div_pos (mul_pos (sq_pos_of_pos p.hbar_pos) Real.pi_pos) (by norm_num)
  linarith

end FoliationQM.TwistedOscillationIntegral
