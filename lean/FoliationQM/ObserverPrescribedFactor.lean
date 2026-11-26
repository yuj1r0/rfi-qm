module

public import FoliationQM.ObserverSliceFisher
public import FoliationQM.GaussianKGInitialJet
public import FoliationQM.PolarTestVariations

/-!
# Realization of a prescribed laboratory density on the initial slice

With intrinsic density one, the phase −mc x⁰ g(y) prescribes the normal
phase derivative independently at each spatial point. On x⁰ = 0 its
spatial differential vanishes and the current divided by c has density g.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverPrescribedFactor

open LorentzCoordinates OsmoticSliceFields DressedMassDensityVariation Madelung
open scoped ContDiff

/-- The spacetime action with normal phase slope −mc g on the initial slice. -/
def action (p : MassiveParameters) (g : Spatial → ℝ) (x : Covector) : ℝ :=
  x 0 * (-(p.m * p.c) * g (GaussianKGInitialJet.space x))

/-- The spacetime action preserves the differentiability order of the spatial profile. -/
theorem action_smooth (p : MassiveParameters) (g : Spatial → ℝ) {n : WithTop ℕ∞}
    (hg : ContDiff ℝ n g) : ContDiff ℝ n (action p g) :=
  (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0).mul
    (contDiff_const.mul (hg.comp GaussianKGInitialJet.space.contDiff))

/-- The complex wave of unit intrinsic density has the same regularity as the profile. -/
theorem wave_smooth (p : MassiveParameters) (g : Spatial → ℝ) {n : WithTop ℕ∞}
    (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (ActionDensity.actionField p (fun _ => 1) (action p g)) :=
  PolarTestVariations.contDiff_actionField p contDiff_const (action_smooth p g hg) (fun _ => one_pos)

private theorem space_slice (y : Spatial) : GaussianKGInitialJet.space (slicePoint 0 y) = y := by
  ext i
  fin_cases i <;> rfl

private theorem action_derivative (p : MassiveParameters) (g : Spatial → ℝ) (y : Spatial)
    (hg : DifferentiableAt ℝ g y) :
    HasFDerivAt (action p g) ((-(p.m*p.c) * g y) • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 4 => ℝ) 0) (slicePoint 0 y) := by
  let x := slicePoint 0 y
  have hd : DifferentiableAt ℝ g (GaussianKGInitialJet.space x) := space_slice y ▸ hg
  have h := (hasFDerivAt_apply (0 : Fin 4) x).fun_mul
    ((hd.hasFDerivAt.comp x GaussianKGInitialJet.space.hasFDerivAt).const_mul (-(p.m*p.c)))
  change HasFDerivAt (action p g) _ x at h
  simpa only [show x 0 = 0 by rfl, zero_smul, zero_add, Function.comp_apply,
    show GaussianKGInitialJet.space x = y from space_slice y] using h

/-- Only the normal component of the phase differential survives on x⁰ = 0. -/
theorem initial_differential (p : MassiveParameters) (g : Spatial → ℝ) (y : Spatial)
    (hg : DifferentiableAt ℝ g y) :
    phaseDifferential (action p g) (slicePoint 0 y) = (-(p.m*p.c)*g y) • coordinateVector 0 := by
  funext i
  change fderiv ℝ (action p g) (slicePoint 0 y) (coordinateVector i) = _
  rw [(action_derivative p g y hg).fderiv]
  fin_cases i <;> simp [coordinateVector]

/-- The normal phase factor in the laboratory frame is the prescribed profile. -/
theorem factor_eq (p : MassiveParameters) (g : Spatial → ℝ) (y : Spatial)
    (hg : DifferentiableAt ℝ g y) : ObserverSliceFisher.sliceFactor p (action p g) 0 y = g y := by
  unfold ObserverSliceFisher.sliceFactor ObserverCurrentFactor.factor
  rw [(action_derivative p g y hg).fderiv]
  simp [coordinateVector, p.m_pos.ne', p.c_pos.ne']

/-- Dividing the actual temporal current by c gives g at each point of the slice. -/
theorem measured_eq (p : MassiveParameters) (g : Spatial → ℝ) (y : Spatial)
    (hg : DifferentiableAt ℝ g y) :
    ObserverSliceFisher.measured p (fun _ => 1) (action p g) 0 y = g y := by
  rw [ObserverSliceFisher.measured_eq (differentiableAt_const _) (action_derivative p g y hg).differentiableAt
    one_pos, factor_eq p g y hg]
  simp

/-- The full current on the initial slice is cg times the future coordinate normal. -/
theorem current_eq (p : MassiveParameters) (g : Spatial → ℝ) (y : Spatial)
    (hg : DifferentiableAt ℝ g y) :
    ScalarPhaseCurrent.current p (ActionDensity.actionField p (fun _ => 1) (action p g)) (slicePoint 0 y) =
      (p.c * g y) • coordinateVector 0 := by
  funext i
  rw [ScalarDressedCurrent.current_actionField p (differentiableAt_const _)
    (action_derivative p g y hg).differentiableAt one_pos i, initial_differential p g y hg]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [p.m_pos.ne']

/-- A positive prescribed profile puts the phase in the future-timelike polar chart. -/
theorem future_timelike (p : MassiveParameters) (g : Spatial → ℝ) (y : Spatial)
    (hg : DifferentiableAt ℝ g y) (hpos : 0 < g y) :
    let dS := phaseDifferential (action p g) (slicePoint 0 y)
    0 < minkowski dS dS ∧ dS 0 < 0 := by
  dsimp only
  rw [initial_differential p g y hg]
  simp [minkowski, coordinateVector, mul_pos (mul_pos p.m_pos p.c_pos) hpos]

/-- The measured four-current has positive time component and positive Lorentz square. -/
theorem current_future_timelike (p : MassiveParameters) (g : Spatial → ℝ) (y : Spatial)
    (hg : DifferentiableAt ℝ g y) (hpos : 0 < g y) :
    let j := ScalarPhaseCurrent.current p (ActionDensity.actionField p (fun _ => 1) (action p g)) (slicePoint 0 y)
    0 < minkowski j j ∧ 0 < j 0 := by
  dsimp only
  rw [current_eq p g y hg]
  simp [minkowski, coordinateVector, mul_pos p.c_pos hpos]

/-- All three components of the phase drift vanish on the laboratory slice. -/
theorem drift_zero (p : MassiveParameters) (g : Spatial → ℝ) (y : Spatial)
    (hg : DifferentiableAt ℝ g y) :
    ObserverFluxDensity.phaseDrift p.c (action p g) (slicePoint 0 y) = 0 := by
  funext i
  simp [ObserverFluxDensity.phaseDrift, initial_differential p g y hg, coordinateVector]

end FoliationQM.ObserverPrescribedFactor
