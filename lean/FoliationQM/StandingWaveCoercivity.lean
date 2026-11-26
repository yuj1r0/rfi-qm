module

public import FoliationQM.OsmoticSliceFields
public import FoliationQM.DressedMassStandingWave
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Strict spatial coercivity on a cell of a standing wave

For v13 `eq:spacelike_coercivity`, fix wave number one in the actual massive
standing wave and any coordinate slice x⁰=t. Between π/6 and π/3 in x¹,
the amplitude is positive and its spatial derivative is nonzero. The other
two directions each have length one. All integrals use spatial Lebesgue volume.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.StandingWaveCoercivity
open Set MeasureTheory DressedMassStandingWave OsmoticSliceFields LorentzCoordinates
open DressedMassDensityVariation LogDensityTransport ObserverFluxDensity PolarSecondDifferential

/-- The lower corner of the physical slice cell. -/
def lowerCorner (i : Fin 3) : ℝ := if i = 0 then Real.pi/6 else 0
/-- The upper corner of the physical slice cell. -/
def upperCorner (i : Fin 3) : ℝ := if i = 0 then Real.pi/3 else 1

/-- Closed laboratory box [π/6,π/3] × [0,1] × [0,1] in the three spatial coordinates. -/
def cell : Set Spatial := Icc lowerCorner upperCorner

/-- The bounded example cell is compact. -/
theorem compact_cell : IsCompact cell := isCompact_Icc

/-- The actual three-dimensional volume of the example is π/6. -/
theorem volume_cell : volume cell = ENNReal.ofReal (Real.pi/6) := by
  rw [cell, Real.volume_Icc_pi]
  simp [Fin.prod_univ_three, lowerCorner, upperCorner, show Real.pi/3 - Real.pi/6 = Real.pi/6 by ring]

/-- The cell has strictly positive finite Lebesgue volume. -/
theorem volume_cell_pos_finite : 0 < volume cell ∧ volume cell < ⊤ := by
  rw [volume_cell]
  exact ⟨ENNReal.ofReal_pos.mpr (div_pos Real.pi_pos (by norm_num)), ENNReal.ofReal_lt_top⟩

private theorem angles {y : Spatial} (hy : y ∈ cell) :
    0 < Real.cos (y 0) ∧ 0 < Real.sin (y 0) := by
  have hlo : Real.pi/6 ≤ y 0 := by simpa [lowerCorner] using hy.1 0
  have hhi : y 0 ≤ Real.pi/3 := by simpa [upperCorner] using hy.2 0
  exact ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])⟩

/-- The full spatial cell stays in the positive polar chart at every slice time. -/
theorem slice_regular (t : ℝ) {y : Spatial} (hy : y ∈ cell) : slicePoint t y ∈ positiveRegion 1 := by
  simpa [positiveRegion, amplitude, slicePoint, assemble] using (angles hy).1

/-- This same complex standing wave satisfies the massive Klein–Gordon equation on the cell. -/
theorem slice_kg (p : MassiveParameters) (t : ℝ) {y : Spatial} (hy : y ∈ cell) :
    let ψ := ActionDensity.actionField p (density 1) (actionPhase p 1)
    box ψ Madelung.coordinateVector (slicePoint t y) +
      (((p.m^2*p.c^2/p.hbar^2 : ℝ) : ℂ) * ψ (slicePoint t y)) = 0 :=
  kleinGordon p 1 (slice_regular t hy)

private theorem log_derivative {x : Covector} (hx : x ∈ positiveRegion 1) (v : Covector) :
    fderiv ℝ (fun z => Real.log (density 1 z)) x v =
      (-2 * Real.sin (x 1) / Real.cos (x 1)) * v 1 := by
  have hR := ((smooth_amplitude 1).differentiable (by simp) x).hasFDerivAt
  have hρ := hR.pow 2
  rw [PolarDifferential.fderiv_log_density_apply ((smooth_density 1).differentiable (by simp) x) (density_pos hx)]
  change fderiv ℝ (fun z => amplitude 1 z ^ 2) x v / density 1 x = _
  rw [hρ.fderiv]
  have hd := amplitude_derivative 1 x v
  unfold directionalDerivative at hd
  simp only [smul_apply, smul_eq_mul, hd, density, amplitude, one_mul, mul_one]
  have hp : 0 < Real.cos (x 1) := by simpa [positiveRegion, amplitude] using hx
  field_simp [hp.ne']
  ring

/-- The true logarithmic density derivative in the normal coordinate vanishes on the cell. -/
theorem normal_zero (t : ℝ) {y : Spatial} (hy : y ∈ cell) :
    normalScore (density 1) (slicePoint t y) = 0 := by
  change fderiv ℝ _ _ (Madelung.coordinateVector 0) = _
  rw [log_derivative (slice_regular t hy)]
  simp [Madelung.coordinateVector]

/-- Only the first spatial logarithmic derivative survives, with the true tangent factor of the cosine. -/
theorem spatial_score (t : ℝ) {y : Spatial} (hy : y ∈ cell) :
    spatialScore (density 1) (slicePoint t y) = Pi.single 0 (-2 * Real.sin (y 0) / Real.cos (y 0)) := by
  ext i
  change fderiv ℝ _ _ (Madelung.coordinateVector i.succ) = _
  rw [log_derivative (slice_regular t hy)]
  fin_cases i <;> simp [Madelung.coordinateVector, slicePoint, assemble]

/-- The actual spatial score is nonzero throughout the cell. -/
theorem spatial_ne_zero (t : ℝ) {y : Spatial} (hy : y ∈ cell) :
    spatialScore (density 1) (slicePoint t y) ≠ 0 := by
  rw [spatial_score t hy]
  intro h
  have he := congrFun h 0
  simp [ne_of_gt (angles hy).1, ne_of_gt (angles hy).2] at he

/-- Spatial drift and dilatation of the original massive phase both vanish, at every spacetime point. -/
theorem drift_dilatation_zero (p : MassiveParameters) :
    phaseDrift p.c (actionPhase p 1) = 0 ∧ dilatation p.c (actionPhase p 1) = 0 := by
  have ha : normalMomentum (actionPhase p 1) = fun _ => momentum p 1 := by
    ext x
    change -phaseGradient p 1 x 0 = _
    simp [gradient_eq]
  have hv : phaseDrift p.c (actionPhase p 1) = 0 := by
    funext x i
    change p.c * phaseGradient p 1 x i.succ / _ = 0
    simp [gradient_eq]
  refine ⟨hv, ?_⟩
  funext x
  simp [dilatation, hv, ha, spatialDivergence, material, spatialDot, phaseDifferential,
    directionalDerivative]

/-- The standing phase has future-timelike gradient throughout spacetime, with exact drift speed zero. -/
theorem future_timelike (p : MassiveParameters) (x : Covector) :
    0 < normalMomentum (actionPhase p 1) x ∧
    0 < minkowski (phaseDifferential (actionPhase p 1) x) (phaseDifferential (actionPhase p 1) x) ∧
    euclideanSpeed (phaseDrift p.c (actionPhase p 1) x) = 0 := by
  constructor
  · change 0 < -phaseGradient p 1 x 0
    simp [gradient_eq, momentum_pos]
  · exact ⟨(minkowski_gradient p 1 x).symm ▸ sq_pos_of_pos (momentum_pos p 1),
      by simp [(drift_dilatation_zero p).1, euclideanSpeed, speedSq, spatialDot]⟩

/-- Multiplication by the physical density cancels the cosine denominator of the score. -/
theorem weighted_spatial (t : ℝ) {y : Spatial} (hy : y ∈ cell) :
    density 1 (slicePoint t y) * speedSq (spatialScore (density 1) (slicePoint t y)) =
      4 * Real.sin (y 0)^2 := by
  rw [spatial_score t hy, speedSq_eq_sum]
  simp [density, amplitude, slicePoint, assemble]
  field_simp [(angles hy).1.ne']
  ring

private theorem integral_first (f : ℝ → ℝ) :
    (∫ y in cell, f (y 0)) = ∫ z in Icc (Real.pi/6) (Real.pi/3), f z := by
  let μ : Fin 3 → Measure ℝ := fun i => volume.restrict (Icc (lowerCorner i) (upperCorner i))
  let F : Fin 3 → ℝ → ℝ := fun i => if i = 0 then f else fun _ => 1
  have he := integral_fin_nat_prod_eq_prod (μ := μ) F
  change (∫ y : Spatial, f (y 0) ∂volume.restrict cell) = _
  rw [cell, ← pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  change (∫ y : Spatial, f (y 0) ∂Measure.pi μ) = _
  have hu : (∫ _z in Icc (0 : ℝ) 1, (1 : ℝ)) = 1 := by simp [measureReal_def]
  simpa [F, μ, Fin.prod_univ_three, lowerCorner, upperCorner, hu] using he

/-- The finite density-weighted spatial Fisher square on each slice equals π/3. -/
theorem spatial_integral (t : ℝ) :
    (∫ y in cell, density 1 (slicePoint t y) * speedSq (spatialScore (density 1) (slicePoint t y))) =
      Real.pi / 3 := by
  rw [setIntegral_congr_fun compact_cell.measurableSet (fun y hy => weighted_spatial t hy),
    integral_const_mul, integral_first (fun z => Real.sin z ^ 2), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show Real.pi/6 ≤ Real.pi/3 by linarith [Real.pi_pos]),
    integral_sin_sq, Real.sin_pi_div_six, Real.cos_pi_div_six,
    Real.sin_pi_div_three, Real.cos_pi_div_three]
  ring

/-- All three actual density-weighted square integrals in the source estimate are finite. -/
theorem integrable_squares (p : MassiveParameters) (t : ℝ) :
    IntegrableOn (fun y => density 1 (slicePoint t y) * (normalScore (density 1) (slicePoint t y))^2) cell ∧
    IntegrableOn (fun y => density 1 (slicePoint t y) * speedSq (spatialScore (density 1) (slicePoint t y))) cell ∧
    IntegrableOn (fun y => density 1 (slicePoint t y) * (dilatation p.c (actionPhase p 1) (slicePoint t y))^2) cell := by
  refine ⟨integrableOn_zero.congr_fun (fun y hy => ?_) compact_cell.measurableSet, ?_, ?_⟩
  · simp [normal_zero t hy]
  · have h : Continuous (fun y : Spatial => 4 * Real.sin (y 0)^2) :=
      continuous_const.mul ((Real.continuous_sin.comp (continuous_apply 0)).pow 2)
    exact (h.continuousOn.integrableOn_compact compact_cell).congr_fun
      (fun y hy => (weighted_spatial t hy).symm) compact_cell.measurableSet
  · simp [(drift_dilatation_zero p).2]

/-- The manuscript's strict dilatation hypothesis actually holds with the uniform speed bound v_max=0. -/
theorem dilatation_bound (p : MassiveParameters) (t : ℝ) :
    Real.sqrt (∫ y in cell, density 1 (slicePoint t y) * (dilatation p.c (actionPhase p 1) (slicePoint t y))^2) <
      (p.c - 0) * Real.sqrt (∫ y in cell, density 1 (slicePoint t y) *
        speedSq (spatialScore (density 1) (slicePoint t y))) := by
  rw [spatial_integral]
  simp only [(drift_dilatation_zero p).2, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    mul_zero, integral_zero, Real.sqrt_zero, sub_zero]
  exact mul_pos p.c_pos (Real.sqrt_pos.2 (div_pos Real.pi_pos (by norm_num)))

private theorem contracted (p : MassiveParameters) (t : ℝ) (y : Spatial) (hy : y ∈ cell) :
    density 1 (slicePoint t y) * minkowski (infoMomentum p (density 1) (slicePoint t y))
      (infoMomentum p (density 1) (slicePoint t y)) =
      (-p.hbar^2/4) * (density 1 (slicePoint t y) * speedSq (spatialScore (density 1) (slicePoint t y))) := by
  rw [info_square, normal_zero t hy]
  ring

/-- The weighted physical signed contraction itself is integrable on the spatial cell. -/
theorem integrable_signed (p : MassiveParameters) (t : ℝ) :
    IntegrableOn (fun y => density 1 (slicePoint t y) *
      minkowski (infoMomentum p (density 1) (slicePoint t y)) (infoMomentum p (density 1) (slicePoint t y))) cell :=
  IntegrableOn.congr_fun ((integrable_squares p t).2.1.const_mul (-p.hbar^2/4))
    (fun y hy => (contracted p t y hy).symm) compact_cell.measurableSet

/-- The integral of the actual lowered osmotic momentum contraction on the cell is −ℏ²π/12. -/
theorem signed_integral (p : MassiveParameters) (t : ℝ) :
    (∫ y in cell, density 1 (slicePoint t y) *
      minkowski (infoMomentum p (density 1) (slicePoint t y)) (infoMomentum p (density 1) (slicePoint t y))) =
      -p.hbar^2 * Real.pi / 12 := by
  rw [setIntegral_congr_fun compact_cell.measurableSet (contracted p t), integral_const_mul, spatial_integral]
  ring

/-- Strict spatial coercivity of this massive KG solution for every t and positive ℏ. -/
theorem signed_integral_neg (p : MassiveParameters) (t : ℝ) :
    (∫ y in cell, density 1 (slicePoint t y) *
      minkowski (infoMomentum p (density 1) (slicePoint t y)) (infoMomentum p (density 1) (slicePoint t y))) < 0 := by
  rw [signed_integral]
  have hh := sq_pos_of_pos p.hbar_pos
  nlinarith [mul_pos hh Real.pi_pos]

end FoliationQM.StandingWaveCoercivity
