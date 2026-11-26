module
public import FoliationQM.DiracRestField
public import FoliationQM.DiracStationaryAction

/-!
# A physical rest solution and the degenerate zero-speed action

For v13 `thm:dirac_lift`, the everywhere regular rest solution is
stationary on each open domain. At c = 0 every actual Dirac density
vanishes, whereas the unscaled residual still contains iℏγ·∂. A smooth
linear spinor field distinguishes the two at the spacetime origin.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracStationaryExamples
open DiracMatrices DiracFieldDensity DiracEquation DiracStationaryAction
open DiracRelativeAction DiracActionSupport
open scoped ContDiff

/-- The rest plane spinor is stationary for the relative action on every open domain. -/
theorem rest_relative (hbar c m : ℝ) (hhbar : hbar ≠ 0) (hc : c ≠ 0)
    {U : Set Covector} (hU : IsOpen U) :
    RelativeStationary hbar c m U (DiracRestField.field hbar c m) :=
  (relative_iff hbar c m hU (fun _ _ => (DiracRestField.contDiff_field hbar c m ∞).contDiffAt) hc).mpr
    (fun x _ => DiracRestField.diracField_zero hbar c m hhbar x)

/-- The ordinary background action of the plane wave is finite, zero and stationary,
including on unbounded open domains. -/
theorem rest_absolute (hbar c m : ℝ) (hhbar : hbar ≠ 0) {U : Set Covector} (hU : IsOpen U) :
    MeasureTheory.IntegrableOn (dens hbar c m (DiracRestField.field hbar c m)) U ∧
      action hbar c m (DiracRestField.field hbar c m) U = 0 ∧
      AbsoluteStationary hbar c m U (DiracRestField.field hbar c m) := by
  have he (x : Covector) (_ : x ∈ U) := DiracRestField.diracField_zero hbar c m hhbar x
  exact ⟨DiracOnShellDensity.integrableOn_dens hbar c m hU.measurableSet he,
    DiracOnShellDensity.action_eq_zero hbar c m he, absolute_of_equation hbar c m hU he⟩

/-- At zero speed the ordinary real jet density vanishes even away from a solution. -/
theorem densityRe_zero_speed (hbar m : ℝ) (u : Spinor) (j : Fin 4 → Spinor) :
    DiracDensity.densityRe hbar 0 m u j = 0 := by
  simp [DiracDensity.densityRe, DiracDensity.density]

/-- The relative action vanishes at zero speed on every background and test field. -/
theorem relativeAction_zero_speed (hbar m : ℝ) (ψ φ : Covector → Spinor) (U : Set Covector) :
    relativeAction hbar 0 m ψ φ U = 0 := by
  have hd (u : Covector → Spinor) (x : Covector) : dens hbar 0 m u x = 0 :=
    densityRe_zero_speed hbar m _ _
  simp [relativeAction, hd]

/-- Every background is stationary along every admissible family at zero speed. -/
theorem relative_zero_speed (hbar m : ℝ) (U : Set Covector) (ψ : Covector → Spinor) :
    RelativeStationary hbar 0 m U ψ := by
  intro V
  simp_rw [relativeAction_zero_speed]
  exact hasDerivAt_const 0 0

/-- A smooth field whose time derivative is the nonzero rest spinor. -/
def timeRamp (x : Covector) : Spinor := x 0 • restSpinor

/-- The linear spinor field is smooth at every order. -/
theorem contDiff_timeRamp (n : WithTop ℕ∞) : ContDiff ℝ n timeRamp :=
  (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0).smul contDiff_const

/-- Its genuine directional derivative retains the time component of the direction. -/
theorem fderiv_timeRamp (x v : Covector) : fderiv ℝ timeRamp x v = v 0 • restSpinor := by
  let L := (ContinuousLinearMap.proj (0 : Fin 4) : Covector →L[ℝ] ℝ).smulRight restSpinor
  have h : HasFDerivAt timeRamp L x := L.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The unscaled Dirac residual at unit ℏ and zero c is the same nonzero spinor at every point. -/
theorem residual_timeRamp (m : ℝ) (x : Covector) :
    diracField 1 m 0 timeRamp x = Complex.I • restSpinor := by
  have hs : slashField timeRamp x = restSpinor := by
    unfold slashField slashJet
    simp_rw [fderiv_timeRamp]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp [coordinateDirections, gamma_zero_mulVec_restSpinor]
    · intro μ _ hμ
      simp [coordinateDirections, Ne.symm hμ]
    · simp
  change (Complex.I * (1 : ℂ)) • slashField timeRamp x -
    ((m * 0 : ℝ) : ℂ) • timeRamp x = _
  simp [hs]

/-- The invariant density of the linear time field is the square of its real time coordinate. -/
theorem invariantDensity_timeRamp (x : Covector) :
    SpinorRegularity.invariantDensity (timeRamp x) = (x 0) ^ 2 := by
  have he : timeRamp x = (x 0 : ℂ) • restSpinor := by
    rw [timeRamp, ← IsScalarTower.algebraMap_smul ℂ (x 0) restSpinor]
    rfl
  have hs : SpinorRegularity.scalar (timeRamp x) = (x 0) ^ 2 := by
    rw [SpinorRegularity.scalar, he, DiracAdjoint.bilinear_smul_left, DiracAdjoint.bilinear_smul_right,
      DiracAdjoint.rest_scalar, mul_one]
    simp [← Complex.ofReal_mul, pow_two]
  have hp : SpinorRegularity.pseudoscalar (timeRamp x) = 0 := by
    rw [SpinorRegularity.pseudoscalar, he, DiracAdjoint.bilinear_smul_left, DiracAdjoint.bilinear_smul_right,
      DiracAdjoint.rest_pseudoscalar]
    simp
  rw [SpinorRegularity.invariantDensity, hs, hp, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_sq (sq_nonneg _)]

/-- At zero speed, even on all spacetime, relative stationarity can hold
while the genuine Dirac field equation fails at the origin. -/
theorem stationary_without_equation (m : ℝ) :
    RelativeStationary 1 0 m Set.univ timeRamp ∧ diracField 1 m 0 timeRamp 0 ≠ 0 :=
  ⟨relative_zero_speed 1 m Set.univ timeRamp, by
    rw [residual_timeRamp]
    exact smul_ne_zero Complex.I_ne_zero restSpinor_ne_zero⟩

/-- On the positive-time open half-space the same stationary field is strictly
regular everywhere and its residual is nonzero at every point. -/
theorem regular_stationary_without_equation (m : ℝ) :
    let U := {x : Covector | 0 < x 0}
    IsOpen U ∧ RelativeStationary 1 0 m U timeRamp ∧
      ∀ x ∈ U, SpinorRegularity.Regular (timeRamp x) ∧ diracField 1 m 0 timeRamp x ≠ 0 := by
  refine ⟨isOpen_lt continuous_const (continuous_apply 0), relative_zero_speed 1 m _ timeRamp, ?_⟩
  intro x hx
  constructor
  · change 0 < SpinorRegularity.invariantDensity (timeRamp x)
    rw [invariantDensity_timeRamp]
    exact sq_pos_of_pos hx
  · rw [residual_timeRamp]
    exact smul_ne_zero Complex.I_ne_zero restSpinor_ne_zero

end FoliationQM.DiracStationaryExamples
