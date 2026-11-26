module

public import FoliationQM.RelativePolarStationaryAction

/-!
# Dressed mass of the scalar standing wave

The discussion after v13 `eq:noether_current` uses the mode cos(kx¹) exp(−iωt)
to distinguish mass dressing from an observer boost. In coordinates x⁰ = ct
the phase is −q x⁰ with q² = m²c² + ℏ²k². We use the open union of strips
where the amplitude is positive to avoid the nodes of its polar chart.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FoliationQM.DressedMassStandingWave
open PolarSecondDifferential

/-- Positive magnitude of the temporal phase covector in the coordinates (ct,x,y,z). -/
def momentum (p : MassiveParameters) (k : ℝ) : ℝ := Real.sqrt (p.m^2*p.c^2 + p.hbar^2*k^2)

/-- Physical angular frequency with respect to t. -/
def frequency (p : MassiveParameters) (k : ℝ) : ℝ := p.c * momentum p k / p.hbar

/-- Real spatial amplitude of the standing wave. -/
def amplitude (k : ℝ) (x : Covector) : ℝ := Real.cos (k*x 1)

/-- Scalar density of the mode, defined even at its nodes. -/
def density (k : ℝ) (x : Covector) : ℝ := amplitude k x ^ 2

/-- Real action phase on the positive-amplitude strips. -/
def actionPhase (p : MassiveParameters) (k : ℝ) (x : Covector) : ℝ := -momentum p k * x 0

/-- Open polar domain containing the spacetime origin. -/
def positiveRegion (k : ℝ) : Set Covector := {x | 0 < amplitude k x}

/-- The temporal momentum is positive even at zero spatial frequency. -/
theorem momentum_pos (p : MassiveParameters) (k : ℝ) : 0 < momentum p k :=
  Real.sqrt_pos_of_pos (add_pos_of_pos_of_nonneg
    (mul_pos (sq_pos_of_pos p.m_pos) (sq_pos_of_pos p.c_pos))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- The exact massive dispersion relation in the ct coordinate. -/
theorem momentum_sq (p : MassiveParameters) (k : ℝ) :
    momentum p k ^ 2 = p.m^2*p.c^2 + p.hbar^2*k^2 := Real.sq_sqrt (by positivity)

/-- Smoothness of the cosine amplitude on spacetime. -/
theorem smooth_amplitude (k : ℝ) : ContDiff ℝ ∞ (amplitude k) :=
  Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 1))

/-- Smoothness of the real density on spacetime. -/
theorem smooth_density (k : ℝ) : ContDiff ℝ ∞ (density k) := (smooth_amplitude k).pow 2

/-- Smoothness of the time-linear action phase on spacetime. -/
theorem smooth_phase (p : MassiveParameters) (k : ℝ) : ContDiff ℝ ∞ (actionPhase p k) :=
  contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0)

/-- Positivity of the amplitude defines an open domain. -/
theorem isOpen_positiveRegion (k : ℝ) : IsOpen (positiveRegion k) :=
  isOpen_lt continuous_const (smooth_amplitude k).continuous

/-- The example has a genuine regular point at the spacetime origin for every k. -/
theorem zero_mem (k : ℝ) : (0 : Covector) ∈ positiveRegion k := by
  simp [positiveRegion, amplitude]

/-- Strict positivity of the density on the chosen polar domain. -/
theorem density_pos {k : ℝ} {x : Covector} (hx : x ∈ positiveRegion k) : 0 < density k x :=
  sq_pos_of_pos hx

private theorem scaled_projection (k : ℝ) (i : Fin 4) (x : Covector) :
    HasFDerivAt (fun y : Covector => k*y i) (k • (ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ)) x :=
  (hasFDerivAt_apply i x).const_mul k

/-- Actual first directional derivative of the cosine amplitude. -/
theorem amplitude_derivative (k : ℝ) (x v : Covector) :
    directionalDerivative (amplitude k) v x = -Real.sin (k*x 1)*k*v 1 := by
  have h := (Real.hasDerivAt_cos (k*x 1)).comp_hasFDerivAt (f := fun y : Covector => k*y 1) x
    (scaled_projection k 1 x)
  change fderiv ℝ (Real.cos ∘ fun y : Covector => k*y 1) x v = _
  rw [h.fderiv]
  change -Real.sin (k*x 1) * (k*v 1) = _
  ring

/-- Actual second directional derivative of the amplitude along any constant vector. -/
theorem amplitude_second (k : ℝ) (x v : Covector) :
    secondDirectionalDerivative (amplitude k) v x = -(k^2) * (v 1)^2 * amplitude k x := by
  have h := (((Real.hasDerivAt_sin (k*x 1)).comp_hasFDerivAt (f := fun y : Covector => k*y 1) x
    (scaled_projection k 1 x)).neg.mul_const k).mul_const (v 1)
  unfold secondDirectionalDerivative
  rw [show directionalDerivative (amplitude k) v =
      (fun y : Covector => -Real.sin (k*y 1)*k*v 1) from funext (fun y => amplitude_derivative k y v)]
  unfold directionalDerivative
  simp only [Function.comp_def, Pi.neg_apply] at h
  rw [h.fderiv]
  change v 1 * (k * -(Real.cos (k*x 1) * (k*v 1))) = _
  unfold amplitude
  ring

/-- The flat spacetime wave operator on this stationary real amplitude is k²R. -/
theorem box_amplitude (k : ℝ) (x : Covector) :
    box (amplitude k) Madelung.coordinateVector x = k^2 * amplitude k x := by
  simp [box, amplitude_second, Madelung.coordinateVector]

/-- The actual quantum correction □√ρ/√ρ is k² at every point of the positive domain. -/
theorem quantum_correction {k : ℝ} {x : Covector} (hx : x ∈ positiveRegion k) :
    box (fun y => Real.sqrt (density k y)) Madelung.coordinateVector x /
      Real.sqrt (density k x) = k^2 := by
  have he : (fun y => Real.sqrt (density k y)) =ᶠ[𝓝 x] amplitude k := by
    filter_upwards [(isOpen_positiveRegion k).mem_nhds hx] with y hy
    exact Real.sqrt_sq (le_of_lt hy)
  have hsecond (v : Covector) :
      secondDirectionalDerivative (fun y => Real.sqrt (density k y)) v x =
        secondDirectionalDerivative (amplitude k) v x := by
    have hd : directionalDerivative (fun y => Real.sqrt (density k y)) v =ᶠ[𝓝 x]
        directionalDerivative (amplitude k) v :=
      (he.fderiv (𝕜 := ℝ)).mono (fun _ hy => congrArg (fun L => L v) hy)
    exact congrArg (fun L => L v) (hd.fderiv_eq (𝕜 := ℝ))
  have hb : box (fun y => Real.sqrt (density k y)) Madelung.coordinateVector x =
      box (amplitude k) Madelung.coordinateVector x := by
    unfold box
    rw [hsecond, hsecond, hsecond, hsecond]
  rw [hb, box_amplitude, show Real.sqrt (density k x) = amplitude k x from he.self_of_nhds]
  exact mul_div_cancel_right₀ _ (ne_of_gt hx)

/-- Actual phase derivative; spatial vectors annihilate the action phase. -/
theorem phase_derivative (p : MassiveParameters) (k : ℝ) (x v : Covector) :
    directionalDerivative (actionPhase p k) v x = -momentum p k * v 0 := by
  unfold directionalDerivative actionPhase
  rw [((hasFDerivAt_apply (0 : Fin 4) x).const_mul (-momentum p k)).fderiv]
  rfl

/-- Lowered covector formed from the actual coordinate derivatives of the phase. -/
def phaseGradient (p : MassiveParameters) (k : ℝ) (x : Covector) : Covector :=
  fun i => directionalDerivative (actionPhase p k) (Madelung.coordinateVector i) x

/-- The exact time component of the phase gradient, with all spatial components zero. -/
theorem gradient_eq (p : MassiveParameters) (k : ℝ) (x : Covector) :
    phaseGradient p k x = Pi.single 0 (-momentum p k) := by
  ext i
  fin_cases i <;> simp [phaseGradient, phase_derivative, Madelung.coordinateVector]

/-- Minkowski norm of the actual phase covector. -/
theorem minkowski_gradient (p : MassiveParameters) (k : ℝ) (x : Covector) :
    minkowski (phaseGradient p k x) (phaseGradient p k x) = momentum p k ^ 2 := by
  simp [gradient_eq, minkowski, pow_two]

private theorem phase_box (p : MassiveParameters) (k : ℝ) (x : Covector) :
    box (actionPhase p k) Madelung.coordinateVector x = 0 := by
  have hd (v : Covector) : directionalDerivative (actionPhase p k) v =
      fun _ => -momentum p k * v 0 := funext (fun y => phase_derivative p k y v)
  simp [box, secondDirectionalDerivative, hd, directionalDerivative]

/-- The actual density current has zero divergence, as its only nonzero component
is time directed and its scalar coefficient depends only on x¹. -/
theorem current_conserved (p : MassiveParameters) (k : ℝ) (x : Covector) :
    PolarRegularity.densityCurrentDivergence (density k) (actionPhase p k) Madelung.coordinateVector x = 0 := by
  change Madelung.currentDivergence (amplitude k) (actionPhase p k) Madelung.coordinateVector x = 0
  rw [Madelung.currentDivergence_eq_continuityResidual _ ((smooth_amplitude k).differentiable (by simp) x)
    (fun i => PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two
      ((smooth_phase p k).contDiffAt.of_le (by simp)) _)]
  simp [PolarSecondJet.continuityResidual, minkowski, phase_box, amplitude_derivative,
    phase_derivative, Madelung.coordinateVector]

/-- The standing wave is stationary for the relative polar action tested on the positive strips. -/
theorem stationary (p : MassiveParameters) (k : ℝ) :
    RelativePolarStationaryAction.RelativePolarStationaryOn p (density k) (actionPhase p k)
      Madelung.coordinateVector (positiveRegion k) := by
  apply (RelativePolarStationaryAction.relativePolarStationaryOn_iff_madelung p
    (isOpen_positiveRegion k) (fun _ _ => (smooth_density k).contDiffAt)
    (fun _ _ => (smooth_phase p k).contDiffAt) (fun _ hx => density_pos hx)).mpr
  intro x hx
  refine ⟨?_, current_conserved p k x⟩
  change minkowski (phaseGradient p k x) (phaseGradient p k x) = _
  rw [minkowski_gradient, momentum_sq, mul_div_assoc, quantum_correction hx]

/-- On the chosen strips the polar reconstruction is exactly cos(kx¹) exp(−iωt), with t = x⁰/c. -/
theorem wave_eq (p : MassiveParameters) (k : ℝ) {x : Covector} (hx : x ∈ positiveRegion k) :
    ActionDensity.actionField p (density k) (actionPhase p k) x =
      (Real.cos (k*x 1) : ℂ) * phase (-frequency p k * (x 0 / p.c)) := by
  change (Real.sqrt (amplitude k x ^ 2) : ℂ) * phase ((-momentum p k * x 0) / p.hbar) = _
  rw [Real.sqrt_sq (le_of_lt hx)]
  congr 2
  unfold frequency
  field_simp [p.c_pos.ne', p.hbar_pos.ne']

/-- The associated physical complex scalar field satisfies the massive KG equation at every
point of the positive-amplitude strips. -/
theorem kleinGordon (p : MassiveParameters) (k : ℝ) {x : Covector} (hx : x ∈ positiveRegion k) :
    box (ActionDensity.actionField p (density k) (actionPhase p k)) Madelung.coordinateVector x +
        (((p.m^2*p.c^2/p.hbar^2 : ℝ) : ℂ) * ActionDensity.actionField p (density k) (actionPhase p k) x) = 0 :=
  (RelativePolarStationaryAction.relativePolarStationaryOn_iff_kleinGordon p (isOpen_positiveRegion k)
    (fun _ _ => (smooth_density k).contDiffAt) (fun _ _ => (smooth_phase p k).contDiffAt)
    (fun _ h => density_pos h)).mp (stationary p k) x hx

/-- The invariant dressed mass determined from the phase is q/c. -/
theorem dressed_mass (p : MassiveParameters) (k : ℝ) (x : Covector) :
    effectiveMass p.c (phaseGradient p k x) = momentum p k / p.c := by
  rw [effectiveMass, minkowski_gradient, Real.sqrt_sq (momentum_pos p k).le]

/-- The future-directed normalized velocity has only its time component c. -/
theorem velocity_rest (p : MassiveParameters) (k : ℝ) (x : Covector) :
    velocityCovector p.c (phaseGradient p k x) = Pi.single 0 p.c := by
  ext i
  change -(phaseGradient p k x i) / effectiveMass p.c (phaseGradient p k x) = _
  rw [dressed_mass, gradient_eq]
  fin_cases i <;> simp [field, (momentum_pos p k).ne']

/-- The dressed mass is strictly larger than the positive bare mass at nonzero spatial frequency. -/
theorem mass_gt_bare (p : MassiveParameters) {k : ℝ} (hk : k ≠ 0) (x : Covector) :
    p.m < effectiveMass p.c (phaseGradient p k x) := by
  rw [dressed_mass, lt_div_iff₀ p.c_pos]
  have hs : (p.m*p.c)^2 < momentum p k ^ 2 := by
    rw [momentum_sq, mul_pow]
    exact lt_add_of_pos_right _ (mul_pos (sq_pos_of_pos p.hbar_pos) (sq_pos_of_ne_zero hk))
  nlinarith [momentum_pos p k, mul_pos p.m_pos p.c_pos]

/-- The observer at coordinate rest sees γ = 1, and the frequency ratio is entirely mass dressing. -/
theorem observer_ratio (p : MassiveParameters) (k : ℝ) (x : Covector) :
    velocityCovector p.c (phaseGradient p k x) 0 / p.c = 1 ∧
      effectiveMass p.c (phaseGradient p k x) / p.m = p.hbar * frequency p k / (p.m * p.c^2) := by
  constructor
  · simp [velocity_rest, p.c_pos.ne']
  · rw [dressed_mass]
    unfold frequency
    field_simp [p.hbar_pos.ne', p.c_pos.ne', p.m_pos.ne']

/-- The flux density seen by the coordinate observer is the dressed rest density.
On the positive strips of a nonconstant standing mode it exceeds the invariant density. -/
theorem observer_density (p : MassiveParameters) {k : ℝ} (hk : k ≠ 0)
    {x : Covector} (hx : x ∈ positiveRegion k) :
    -(density k x / p.m) * phaseGradient p k x 0 / p.c =
      density k x * (effectiveMass p.c (phaseGradient p k x) / p.m) ∧
      density k x < density k x * (effectiveMass p.c (phaseGradient p k x) / p.m) := by
  constructor
  · rw [dressed_mass, gradient_eq]
    simp only [Pi.single_eq_same]
    ring
  · have hr : 1 < effectiveMass p.c (phaseGradient p k x) / p.m :=
      (one_lt_div p.m_pos).mpr (mass_gt_bare p hk x)
    simpa using mul_lt_mul_of_pos_left hr (density_pos hx)

end FoliationQM.DressedMassStandingWave
