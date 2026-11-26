module

public import FoliationQM.DressedClockWorldline
public import FoliationQM.HamiltonJacobiPullback
public import FoliationQM.SpinConnectionForms
public import FoliationQM.ActionDensity
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The closed clock form on the complement of the scalar nodes

In v13 the proper-time form needs timelike momentum while the phase clock
is defined wherever the complex wave is nonzero. Its logarithmic derivative
is intrinsic. Recentring the complex logarithm at each nonzero wave value
provides the local real potential used to prove closedness.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.NodalClockForm

open Filter Topology HamiltonJacobiPullback PolarDifferential MasterMetricAndCone

/-- The differential of phase angle computed from the wave alone. -/
def angleForm (ψ : Covector → ℂ) (x : Covector) : Covector [⋀^Fin 1]→L[ℝ] ℝ :=
  SpinConnectionForms.oneFormLift (Complex.imCLM.comp ((ψ x)⁻¹ • fderiv ℝ ψ x))

/-- The clock in the handoff's sign and normalization. -/
def waveClock (p : MassiveParameters) (ψ : Covector → ℂ) (x : Covector) :
    Covector [⋀^Fin 1]→L[ℝ] ℝ := (-p.hbar / (p.m * p.c^2)) • angleForm ψ x

/-- On a positive polar chart the intrinsic phase differential equals the
actual exterior differential of its dimensionless phase. -/
theorem angleForm_polar {ρ Φ : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hΦ : DifferentiableAt ℝ Φ x) (hp : 0 < ρ x) :
    angleForm (polarField ρ Φ) x = phaseDifferential Φ x := by
  ext v
  rw [phaseDifferential_apply]
  change ((polarField ρ Φ x)⁻¹ * (fderiv ℝ (polarField ρ Φ) x (v 0))).im = _
  rw [fderiv_polarField_apply hρ hΦ hp]
  let R : ℝ := Real.sqrt (ρ x)
  have hR : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hp).ne'
  have he : phase (Φ x) ≠ 0 := Complex.exp_ne_zero _
  let g := fderiv ℝ ρ x (v 0) / (2 * R)
  let b := fderiv ℝ Φ x (v 0)
  have h : ((R : ℂ) * phase (Φ x))⁻¹ * (phase (Φ x) * ((g : ℂ) + Complex.I * R * b)) =
      ((g/R : ℝ) : ℂ) + Complex.I * b := by
    push_cast
    field_simp
  change (((R : ℂ) * phase (Φ x))⁻¹ * (phase (Φ x) * ((g : ℂ) + Complex.I * R * b))).im = b
  rw [h]
  simp

/-- The intrinsic clock agrees with −dS/(mc²) for every regular polar
representative, so different real phase charts determine one form. -/
theorem waveClock_actionField (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) :
    waveClock p (ActionDensity.actionField p ρ S) x = clockForm S p.m p.c x := by
  unfold waveClock ActionDensity.actionField
  have hd : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv] using hS.mul_const p.hbar⁻¹
  rw [angleForm_polar hρ hd hp]
  ext v
  change (-p.hbar / (p.m * p.c^2)) * phaseDifferential (fun y => S y / p.hbar) x v = _
  rw [phaseDifferential_apply, ActionDensity.fderiv_action_phase_apply p hS, clockForm_apply]
  field_simp [p.m_pos.ne', p.c_pos.ne', p.hbar_pos.ne']

/-- Along the physical four-velocity the clock form measures the clock-time
rate M/m. The dimensionless phase has the angular rate −M c²/ℏ. -/
theorem waveClock_velocity (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x)
    (ht : 0 < minkowski (DressedMassDensityVariation.phaseDifferential S x)
      (DressedMassDensityVariation.phaseDifferential S x)) :
    waveClock p (ActionDensity.actionField p ρ S) x (fun _ => DressedClockWorldline.velocity p S x) =
      effectiveMass p.c (DressedMassDensityVariation.phaseDifferential S x) / p.m := by
  rw [waveClock_actionField p hρ hS hp, clockForm_apply, DressedClockWorldline.differential_velocity p ht]
  field_simp [p.m_pos.ne', p.c_pos.ne']

/-- A branch of phase relative to a nonzero reference value. -/
def localAngle (ψ : Covector → ℂ) (z : ℂ) (x : Covector) : ℝ :=
  (Complex.log (ψ x * z⁻¹)).im

private theorem localAngle_differential {ψ : Covector → ℂ} {z : ℂ} {y : Covector}
    (hz : z ≠ 0) (hy : ψ y * z⁻¹ ∈ Complex.slitPlane) (hd : DifferentiableAt ℝ ψ y) :
    phaseDifferential (localAngle ψ z) y = angleForm ψ y := by
  have hg := hd.hasFDerivAt.mul_const z⁻¹
  have hl := (Complex.hasStrictFDerivAt_log_real hy).hasFDerivAt.comp y hg
  have hi := Complex.imCLM.hasFDerivAt.comp y hl
  ext v
  rw [phaseDifferential_apply]
  change fderiv ℝ (Complex.imCLM ∘ Complex.log ∘ fun u => ψ u * z⁻¹) y (v 0) = _
  rw [hi.fderiv]
  change (((ψ y * z⁻¹)⁻¹ * (z⁻¹ * (fderiv ℝ ψ y (v 0))))).im =
    ((ψ y)⁻¹ * (fderiv ℝ ψ y (v 0))).im
  congr 1
  have hψ := left_ne_zero_of_mul (Complex.slitPlane_ne_zero hy)
  field_simp

/-- Every nonzero C² wave value has a local phase branch whose exterior
differential agrees on a neighborhood with the intrinsic form. -/
theorem exists_local_angle {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ x) (hn : ψ x ≠ 0) :
    ∃ Φ : Covector → ℝ, ContDiffAt ℝ 2 Φ x ∧ phaseDifferential Φ =ᶠ[𝓝 x] angleForm ψ := by
  have hg := hψ.mul (contDiffAt_const (c := (ψ x)⁻¹))
  have hx : ψ x * (ψ x)⁻¹ ∈ Complex.slitPlane := by simp [hn]
  have hlog := (Complex.contDiffAt_log (n := 2) hx).restrict_scalars ℝ
  refine ⟨localAngle ψ (ψ x), ?_, ?_⟩
  · change ContDiffAt ℝ 2 (Complex.imCLM ∘ Complex.log ∘ fun y => ψ y * (ψ x)⁻¹) x
    exact Complex.imCLM.contDiff.contDiffAt.comp x (hlog.comp x hg)
  filter_upwards [hg.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hx),
    hψ.eventually (by norm_num)] with y hy hsy
  exact localAngle_differential hn hy (hsy.differentiableAt (by norm_num))

/-- On the entire nonzero locus the physical clock is closed, including
those points where no timelike dressed velocity exists. -/
theorem waveClock_closed (p : MassiveParameters) {ψ : Covector → ℂ} {x : Covector}
    (hψ : ContDiffAt ℝ 2 ψ x) (hn : ψ x ≠ 0) : extDeriv (waveClock p ψ) x = 0 := by
  obtain ⟨Φ, hΦ, hg⟩ := exists_local_angle hψ hn
  change extDeriv ((-p.hbar / (p.m * p.c^2)) • angleForm ψ) x = 0
  rw [extDeriv_smul, ← hg.extDeriv_eq, extDeriv_phaseDifferential_zero hΦ, smul_zero]

end FoliationQM.NodalClockForm
