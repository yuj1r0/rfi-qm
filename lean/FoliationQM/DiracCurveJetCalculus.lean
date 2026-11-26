module
public import FoliationQM.DiracJetFirstVariation
public import FoliationQM.DiracAffineFieldVariation
public import FoliationQM.SmoothActionDensity
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# First variation along a jointly smooth Dirac field curve

For v13 `thm:dirac_lift` and `eq:dirac_lagrangian_sym`, the parameter
velocity and all four spacetime derivatives are computed from the field.
Symmetry of the joint second Fréchet derivative identifies the velocity
of each spatial jet with the corresponding derivative of the velocity field.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracCurveJetCalculus
open DiracMatrices DiracFieldDensity DiracPolarizedDensity DiracJetFirstVariation
open Set Filter
open scoped Topology ContDiff

/-- A spinor field obtained by fixing the real parameter. -/
def slice (Ψ : ℝ × Covector → Spinor) (t : ℝ) (x : Covector) : Spinor := Ψ (t, x)

/-- The actual parameter velocity of a spinor field curve. -/
def velocity (Ψ : ℝ × Covector → Spinor) (t : ℝ) (x : Covector) : Spinor :=
  fderiv ℝ Ψ (t, x) (1, 0)

/-- The field value and its actual four coordinate derivatives, regarded as one jet. -/
def fieldJet (u : Covector → Spinor) (x : Covector) : Jet :=
  (u x, fun μ => fderiv ℝ u x (coordinateDirections μ))

/-- The original coordinate Dirac density of the parameter slice. -/
def density (hbar c m : ℝ) (Ψ : ℝ × Covector → Spinor) (t : ℝ) (x : Covector) : ℝ :=
  value hbar c m (fieldJet (slice Ψ t) x)

/-- The polarized first density with the actual velocity and its spacetime derivatives. -/
def firstDensity (hbar c m : ℝ) (Ψ : ℝ × Covector → Spinor) (t : ℝ) (x : Covector) : ℝ :=
  let u := fieldJet (slice Ψ t) x
  let v := fieldJet (velocity Ψ t) x
  2 * (mixed hbar c m v.1 v.2 u.1 u.2).re

/-- The jet expression evaluates the actual real field density at the four spacetime directions. -/
theorem density_eq_fieldDensityRe (hbar c m : ℝ) (Ψ : ℝ × Covector → Spinor) (t : ℝ) (x : Covector) :
    density hbar c m Ψ t x = fieldDensityRe hbar c m (slice Ψ t) x coordinateDirections := rfl

/-- The derivative coefficient is the polarized variation density with the actual velocity as test field. -/
theorem firstDensity_eq (hbar c m : ℝ) (Ψ : ℝ × Covector → Spinor) (t : ℝ) (x : Covector) :
    firstDensity hbar c m Ψ t x =
      DiracAffineFieldVariation.firstDensity hbar c m (slice Ψ t) (velocity Ψ t) x coordinateDirections := rfl

variable {Ψ : ℝ × Covector → Spinor} {t : ℝ} {x : Covector} {z : ℝ × Covector}

/-- Differentiation of a slice in a spatial direction agrees with the joint spatial differential. -/
theorem fderiv_slice_apply (hΨ : DifferentiableAt ℝ Ψ (t, x)) (v : Covector) :
    fderiv ℝ (slice Ψ t) x v = fderiv ℝ Ψ (t, x) (0, v) := by
  have h := hΨ.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  change fderiv ℝ (Ψ ∘ fun y => (t, y)) x v = _
  rw [h.fderiv]
  rfl

/-- The parameter derivative of the field value is its actual velocity. -/
theorem hasDerivAt_slice_time (hΨ : DifferentiableAt ℝ Ψ (t, x)) :
    HasDerivAt (fun r => slice Ψ r x) (velocity Ψ t x) t := by
  have h := (hΨ.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)).hasDerivAt
  exact h

/-- A smooth joint field restricts to a smooth spatial slice. -/
theorem contDiffAt_slice (hΨ : ContDiffAt ℝ ∞ Ψ (t, x)) : ContDiffAt ℝ ∞ (slice Ψ t) x :=
  hΨ.comp x (contDiffAt_const.prodMk contDiffAt_id)

private theorem smooth_directional (hΨ : ContDiffAt ℝ ∞ Ψ z) (v : ℝ × Covector) :
    ContDiffAt ℝ ∞ (fun w => fderiv ℝ Ψ w v) z :=
  (hΨ.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

/-- The total velocity field remains jointly smooth near a point of joint smoothness. -/
theorem contDiffAt_jointVelocity (hΨ : ContDiffAt ℝ ∞ Ψ z) :
    ContDiffAt ℝ ∞ (fun w => velocity Ψ w.1 w.2) z := smooth_directional hΨ (1, 0)

/-- The velocity is locally smooth in spacetime at the given parameter. -/
theorem contDiffAt_velocity (hΨ : ContDiffAt ℝ ∞ Ψ (t, x)) :
    ContDiffAt ℝ ∞ (velocity Ψ t) x :=
  (contDiffAt_jointVelocity hΨ).comp x (contDiffAt_const.prodMk contDiffAt_id)

private theorem fderiv_directional (hΨ : ContDiffAt ℝ ∞ Ψ z) (v w : ℝ × Covector) :
    fderiv ℝ (fun y => fderiv ℝ Ψ y v) z w = fderiv ℝ (fderiv ℝ Ψ) z w v := by
  have h := ((hΨ.fderiv_right (m := ∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const v z)
  rw [h.fderiv]
  simp

private theorem spatial_eventually (hΨ : ContDiffAt ℝ ∞ Ψ z) (v : Covector) :
    (fun w : ℝ × Covector => fderiv ℝ (slice Ψ w.1) w.2 v) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ Ψ w (0, v)) := by
  have hdiff := ((hΨ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
    (fun _ h => h.differentiableAt (by norm_num))
  filter_upwards [hdiff] with w hw
  exact fderiv_slice_apply hw v

/-- Joint smoothness of each spatial derivative across the given parameter and base point. -/
theorem contDiffAt_spatial (hΨ : ContDiffAt ℝ ∞ Ψ z) (v : Covector) :
    ContDiffAt ℝ ∞ (fun w : ℝ × Covector => fderiv ℝ (slice Ψ w.1) w.2 v) z :=
  (smooth_directional hΨ (0, v)).congr_of_eventuallyEq (spatial_eventually hΨ v)

/-- The parameter derivative of a genuine spacetime derivative is the spacetime
derivative of the genuine parameter velocity. -/
theorem hasDerivAt_spatial (hΨ : ContDiffAt ℝ ∞ Ψ (t, x)) (v : Covector) :
    HasDerivAt (fun r => fderiv ℝ (slice Ψ r) x v) (fderiv ℝ (velocity Ψ t) x v) t := by
  have hraw := (((smooth_directional hΨ (0, v)).differentiableAt
    (by simp)).hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)).hasDerivAt
  have hv : fderiv ℝ (velocity Ψ t) x v = fderiv ℝ (fderiv ℝ Ψ) (t, x) (0, v) (1, 0) := by
    change fderiv ℝ (slice (fun w => velocity Ψ w.1 w.2) t) x v = _
    rw [fderiv_slice_apply ((contDiffAt_jointVelocity hΨ).differentiableAt (by simp))]
    exact fderiv_directional hΨ (1, 0) (0, v)
  have heq := ((continuousAt_id.prodMk continuousAt_const).tendsto.eventually (spatial_eventually hΨ v))
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq heq
  change fderiv ℝ (fun w => fderiv ℝ Ψ w (0, v)) (t, x) (1, 0) = _
  rw [fderiv_directional hΨ, hv]
  exact hΨ.isSymmSndFDerivAt (by simp) _ _

/-- The derivative of the full jet is the full spatial jet of the actual velocity. -/
theorem hasDerivAt_fieldJet (hΨ : ContDiffAt ℝ ∞ Ψ (t, x)) :
    HasDerivAt (fun r => fieldJet (slice Ψ r) x) (fieldJet (velocity Ψ t) x) t := by
  have hj : HasDerivAt (fun r μ => fderiv ℝ (slice Ψ r) x (coordinateDirections μ))
      (fun μ => fderiv ℝ (velocity Ψ t) x (coordinateDirections μ)) t :=
    hasDerivAt_pi.2 (fun μ => hasDerivAt_spatial hΨ (coordinateDirections μ))
  exact (hasDerivAt_slice_time (hΨ.differentiableAt (by simp))).prodMk hj

/-- The full jet of a jointly smooth curve is continuous in parameter and spacetime. -/
theorem continuousAt_fieldJet (hΨ : ContDiffAt ℝ ∞ Ψ z) :
    ContinuousAt (fun w : ℝ × Covector => fieldJet (slice Ψ w.1) w.2) z :=
  hΨ.continuousAt.prodMk (continuousAt_pi.mpr (fun μ => (contDiffAt_spatial hΨ (coordinateDirections μ)).continuousAt))

variable (hbar c m : ℝ)

/-- The pointwise parameter derivative of the unchanged Dirac density along the smooth curve. -/
theorem hasDerivAt_density (hΨ : ContDiffAt ℝ ∞ Ψ (t, x)) :
    HasDerivAt (fun r => density hbar c m Ψ r x) (firstDensity hbar c m Ψ t x) t :=
  hasDerivAt_curve hbar c m (fun r => fieldJet (slice Ψ r) x) (hasDerivAt_fieldJet hΨ)

/-- Joint continuity of the density follows from continuity on the full jet space. -/
theorem continuousAt_density (hΨ : ContDiffAt ℝ ∞ Ψ z) :
    ContinuousAt (fun w : ℝ × Covector => density hbar c m Ψ w.1 w.2) z :=
  (differentiable_value hbar c m _).continuousAt.comp (continuousAt_fieldJet hΨ)

private theorem polarization_difference (u v : Jet) :
    2 * (mixed hbar c m v.1 v.2 u.1 u.2).re =
      value hbar c m (u + v) - value hbar c m u - value hbar c m v := by
  have h := densityRe_affine hbar c m 1 u.1 u.2 v.1 v.2
  simp only [one_smul, one_mul, one_pow] at h
  change _ = DiracDensity.densityRe hbar c m (u.1 + v.1) (u.2 + v.2) -
    DiracDensity.densityRe hbar c m u.1 u.2 - DiracDensity.densityRe hbar c m v.1 v.2
  rw [h]
  ring

/-- The first density is continuous jointly, since both the curve and its velocity
have jointly continuous full jets. -/
theorem continuousAt_first (hΨ : ContDiffAt ℝ ∞ Ψ z) :
    ContinuousAt (fun w : ℝ × Covector => firstDensity hbar c m Ψ w.1 w.2) z := by
  let u := fun w : ℝ × Covector => fieldJet (slice Ψ w.1) w.2
  let v := fun w : ℝ × Covector => fieldJet (velocity Ψ w.1) w.2
  have hu : ContinuousAt u z := continuousAt_fieldJet hΨ
  have hv : ContinuousAt v z := continuousAt_fieldJet (contDiffAt_jointVelocity hΨ)
  have hd := (differentiable_value hbar c m).continuous
  change ContinuousAt (fun w => 2 * (mixed hbar c m (v w).1 (v w).2 (u w).1 (u w).2).re) z
  simp_rw [polarization_difference hbar c m]
  exact ((hd.continuousAt.comp (hu.add hv)).sub (hd.continuousAt.comp hu)).sub (hd.continuousAt.comp hv)

variable {s : Set ℝ} {U : Set Covector}

/-- Joint continuity of the actual density on the parameter-spacetime product. -/
theorem continuousOn_density (hΨ : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ Ψ (t, x)) :
    ContinuousOn (fun w : ℝ × Covector => density hbar c m Ψ w.1 w.2) (s ×ˢ U) :=
  fun z hz => (continuousAt_density hbar c m (hΨ z.1 hz.1 z.2 hz.2)).continuousWithinAt

/-- Joint continuity of the actual derivative density on the same product. -/
theorem continuousOn_first (hΨ : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ Ψ (t, x)) :
    ContinuousOn (fun w : ℝ × Covector => firstDensity hbar c m Ψ w.1 w.2) (s ×ˢ U) :=
  fun z hz => (continuousAt_first hbar c m (hΨ z.1 hz.1 z.2 hz.2)).continuousWithinAt

end FoliationQM.DiracCurveJetCalculus
