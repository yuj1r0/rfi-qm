module

public import FoliationQM.ConeMetricExtension
public import FoliationQM.CanonicalConeGeometry

/-!
# Actual speeds for the positive-coupling cone tensor

Sources: v13 `eq:lambda_metric` and `lem:uniqueness`. Speeds are the square
roots of the already constructed tensor evaluated on actual tangent vectors.
Uniform comparison with Euclidean speed is proved from the radial projection,
not stipulated as a distance formula. The physical Born coordinate and phase
remain fixed. Statements about nonzero curves concern the punctured plane;
no regular extension of a noncanonical tensor to its origin is inferred.
-/

@[expose] public section

namespace FoliationQM.ConeSpeed

open ConeMetricExtension PolarDifferential
open Set MeasureTheory
open scoped ComplexConjugate Topology ENNReal

/-- Squared radial stretching relative to the fixed physical Born coordinate. -/
noncomputable def radialFactorSq (hbar coupling : ℝ) : ℝ := 4 * coupling / hbar ^ 2

/-- The lower uniform comparison factor for actual lengths. -/
noncomputable def lowerFactor (hbar coupling : ℝ) : ℝ :=
  Real.sqrt (min 1 (radialFactorSq hbar coupling))

/-- The upper uniform comparison factor for actual lengths. -/
noncomputable def upperFactor (hbar coupling : ℝ) : ℝ :=
  Real.sqrt (max 1 (radialFactorSq hbar coupling))

/-- Actual tangent speed from the source cone tensor in the physical coordinate. -/
noncomputable def speed (hbar coupling : ℝ) (z v : ℂ) : ℝ :=
  Real.sqrt (tensor hbar coupling z v v)

/-- The source metric speed on a supplied positive-density real phase curve. -/
noncomputable def sourceSpeed (hbar coupling : ℝ) (ρ Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (coupling / (hbar ^ 2 * ρ t) * (deriv ρ t) ^ 2 +
    ρ t * (deriv Φ t) ^ 2)

/-- The radial projection satisfies the Euclidean squared Cauchy bound. -/
theorem radial_sq_le (z v : ℂ) :
    radial z v ^ 2 ≤ Complex.normSq z * Complex.normSq v := by
  have h : Complex.normSq (conj z * v) = Complex.normSq z * Complex.normSq v := by
    simp
  rw [Complex.normSq_apply] at h
  change (conj z * v).re ^ 2 ≤ Complex.normSq z * Complex.normSq v
  nlinarith [sq_nonneg (conj z * v).im]

/-- The normalized squared radial component is nonnegative. -/
theorem radial_quotient_nonneg (z v : ℂ) :
    0 ≤ radial z v ^ 2 / Complex.normSq z :=
  div_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)

/-- The normalized radial component never exceeds the full squared speed,
including the harmless totalized value at zero position. -/
theorem radial_quotient_le (z v : ℂ) :
    radial z v ^ 2 / Complex.normSq z ≤ Complex.normSq v := by
  by_cases hz : z = 0
  · simp [hz, Complex.normSq_nonneg]
  · apply (div_le_iff₀ (Complex.normSq_pos.mpr hz)).mpr
    simpa only [mul_comm] using radial_sq_le z v

/-- The diagonal tensor is Euclidean energy plus its explicit radial correction. -/
theorem tensor_self_eq (hbar coupling : ℝ) (z v : ℂ) :
    tensor hbar coupling z v v = Complex.normSq v +
      (radialFactorSq hbar coupling - 1) * (radial z v ^ 2 / Complex.normSq z) := by
  have he : euclidean v v = Complex.normSq v := by
    unfold euclidean
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [tensor, he]
  unfold radialFactorSq
  ring

/-- The minimum radial/tangential eigenvalue bounds the actual tensor below. -/
theorem tensor_min_le (hbar coupling : ℝ) (z v : ℂ) :
    min 1 (radialFactorSq hbar coupling) * ‖v‖ ^ 2 ≤ tensor hbar coupling z v v := by
  rw [← Complex.normSq_eq_norm_sq, tensor_self_eq]
  have h0 := radial_quotient_nonneg z v
  have h1 := radial_quotient_le z v
  by_cases ha : radialFactorSq hbar coupling ≤ 1
  · rw [min_eq_right ha]
    nlinarith
  · rw [min_eq_left (le_of_not_ge ha)]
    nlinarith

/-- The maximum radial/tangential eigenvalue bounds the actual tensor above. -/
theorem tensor_le_max (hbar coupling : ℝ) (z v : ℂ) :
    tensor hbar coupling z v v ≤ max 1 (radialFactorSq hbar coupling) * ‖v‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, tensor_self_eq]
  have h0 := radial_quotient_nonneg z v
  have h1 := radial_quotient_le z v
  by_cases ha : radialFactorSq hbar coupling ≤ 1
  · rw [max_eq_left ha]
    nlinarith
  · rw [max_eq_right (le_of_not_ge ha)]
    nlinarith

/-- Positive physical hbar and coupling give a positive radial eigenvalue. -/
theorem radialFactorSq_pos (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling) :
    0 < radialFactorSq hbar coupling := by
  unfold radialFactorSq
  positivity

/-- Positive coupling gives a strictly positive lower speed-comparison constant. -/
theorem lowerFactor_pos (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling) :
    0 < lowerFactor hbar coupling := by
  apply Real.sqrt_pos.mpr
  exact lt_min (by norm_num) (radialFactorSq_pos hbar coupling hh hc)

/-- The upper speed-comparison constant is positive for all parameter values. -/
theorem upperFactor_pos (hbar coupling : ℝ) : 0 < upperFactor hbar coupling := by
  apply Real.sqrt_pos.mpr
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- The positive-coupling cone tensor is nonnegative on every tangent vector. -/
theorem tensor_nonneg (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling)
    (z v : ℂ) : 0 ≤ tensor hbar coupling z v v := by
  exact le_trans (mul_nonneg (le_min (by norm_num)
    (radialFactorSq_pos hbar coupling hh hc).le) (sq_nonneg _))
    (tensor_min_le hbar coupling z v)

/-- The tensor is strictly positive on nonzero tangent vectors. -/
theorem tensor_pos (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling)
    (z : ℂ) {v : ℂ} (hv : v ≠ 0) : 0 < tensor hbar coupling z v v := by
  exact lt_of_lt_of_le (mul_pos (lt_min (by norm_num)
    (radialFactorSq_pos hbar coupling hh hc)) (sq_pos_of_pos (norm_pos_iff.mpr hv)))
    (tensor_min_le hbar coupling z v)

/-- The actual speed is nonnegative. -/
theorem speed_nonneg (hbar coupling : ℝ) (z v : ℂ) : 0 ≤ speed hbar coupling z v :=
  Real.sqrt_nonneg _

/-- The actual speed has the uniform positive Euclidean lower bound. -/
theorem speed_lower_bound (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling)
    (z v : ℂ) : lowerFactor hbar coupling * ‖v‖ ≤ speed hbar coupling z v := by
  have h := Real.sqrt_le_sqrt (tensor_min_le hbar coupling z v)
  rw [Real.sqrt_mul (le_min (by norm_num) (radialFactorSq_pos hbar coupling hh hc).le),
    Real.sqrt_sq (norm_nonneg _)] at h
  exact h

/-- The actual speed has the uniform Euclidean upper bound. -/
theorem speed_upper_bound (hbar coupling : ℝ) (z v : ℂ) :
    speed hbar coupling z v ≤ upperFactor hbar coupling * ‖v‖ := by
  have h := Real.sqrt_le_sqrt (tensor_le_max hbar coupling z v)
  rw [Real.sqrt_mul (le_trans (by norm_num) (le_max_left 1 _)),
    Real.sqrt_sq (norm_nonneg _)] at h
  exact h

/-- At canonical coupling the actual speed is ordinary Euclidean speed. -/
theorem speed_canonical (hbar : ℝ) (hh : 0 < hbar) (z v : ℂ) :
    speed hbar (hbar ^ 2 / 4) z v = ‖v‖ := by
  rw [speed, tensor_canonical hbar hh]
  change Real.sqrt (conj v * v).re = ‖v‖
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  exact Real.sqrt_sq (norm_nonneg _)

/-- Scaling a real tangent scales the quadratic tensor by the scalar square. -/
theorem tensor_smul (hbar coupling a : ℝ) (z v : ℂ) :
    tensor hbar coupling z (a • v) (a • v) = a ^ 2 * tensor hbar coupling z v v := by
  simp [tensor, euclidean, radial, Complex.mul_re, Complex.mul_im]
  ring

/-- Real tangent scaling gives absolute homogeneity of actual cone speed. -/
theorem speed_smul (hbar coupling a : ℝ) (z v : ℂ) :
    speed hbar coupling z (a • v) = |a| * speed hbar coupling z v := by
  rw [speed, tensor_smul, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]
  rfl

/-- A zero tangent has zero actual cone speed. -/
theorem speed_zero (hbar coupling : ℝ) (z : ℂ) : speed hbar coupling z 0 = 0 := by
  simp [speed, tensor, euclidean, radial]

/-- Positive coupling makes zero speed equivalent to a zero tangent. -/
theorem speed_eq_zero_iff (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling)
    (z v : ℂ) : speed hbar coupling z v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hle := speed_lower_bound hbar coupling hh hc z v
    rw [h] at hle
    have hn : ‖v‖ = 0 := le_antisymm
      (nonpos_of_mul_nonpos_right hle (lowerFactor_pos hbar coupling hh hc))
      (norm_nonneg v)
    exact norm_eq_zero.mp hn
  · rintro rfl
    exact speed_zero hbar coupling z

/-- Evaluation on the actual derivative of a positive-density polar curve
gives the arbitrary-coupling source metric energy. -/
theorem tensor_deriv_polarField (hbar coupling : ℝ) {ρ Φ : ℝ → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ t) (hΦ : DifferentiableAt ℝ Φ t) (hpos : 0 < ρ t) :
    tensor hbar coupling (polarField ρ Φ t)
      (deriv (polarField ρ Φ) t) (deriv (polarField ρ Φ) t) =
      coupling / (hbar ^ 2 * ρ t) * (deriv ρ t) ^ 2 + ρ t * (deriv Φ t) ^ 2 := by
  have hd : deriv (polarField ρ Φ) t =
      MasterMetricAndCone.polarTangent (ρ t) (Φ t) (deriv ρ t) (deriv Φ t) := by
    simpa only [fderiv_apply_one_eq_deriv] using fderiv_polarField_apply hρ hΦ hpos (1 : ℝ)
  have he : Complex.normSq (deriv (polarField ρ Φ) t) =
      (deriv ρ t) ^ 2 / (4 * ρ t) + ρ t * (deriv Φ t) ^ 2 := by
    simpa only [fderiv_apply_one_eq_deriv] using fderiv_polarField_normSq hρ hΦ hpos (1 : ℝ)
  have hr : radial (polarField ρ Φ t) (deriv (polarField ρ Φ) t) = deriv ρ t / 2 := by
    rw [hd]
    exact radial_polarTangent (ρ t) (Φ t) (deriv ρ t) (deriv Φ t) hpos
  have hn := ActionDensity.polarField_normSq ρ Φ t hpos.le
  rw [tensor_self_eq, he, hr, hn, radialFactorSq]
  ring

/-- Actual cone speed of a differentiable positive-density polar curve is
the square root of the literal source metric expression. -/
theorem speed_deriv_polarField (hbar coupling : ℝ) {ρ Φ : ℝ → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ t) (hΦ : DifferentiableAt ℝ Φ t) (hpos : 0 < ρ t) :
    speed hbar coupling (polarField ρ Φ t) (deriv (polarField ρ Φ) t) =
      sourceSpeed hbar coupling ρ Φ t := by
  rw [speed, tensor_deriv_polarField hbar coupling hρ hΦ hpos]
  rfl

/-- Actual cone speed is continuous along continuous nonzero positions and
continuous tangent vectors, without imposing a smooth extension at zero. -/
theorem continuousOn_speed (hbar coupling : ℝ) {X : Type*} [TopologicalSpace X]
    {z v : X → ℂ} {U : Set X} (hz : ContinuousOn z U) (hv : ContinuousOn v U)
    (hne : ∀ x ∈ U, z x ≠ 0) :
    ContinuousOn (fun x => speed hbar coupling (z x) (v x)) U := by
  have he : ContinuousOn (fun x => euclidean (v x) (v x)) U :=
    Complex.continuous_re.comp_continuousOn
      ((Complex.continuous_conj.comp_continuousOn hv).mul hv)
  have hr : ContinuousOn (fun x => radial (z x) (v x)) U :=
    Complex.continuous_re.comp_continuousOn
      ((Complex.continuous_conj.comp_continuousOn hz).mul hv)
  have hn : ContinuousOn (fun x => Complex.normSq (z x)) U :=
    Complex.continuous_normSq.comp_continuousOn hz
  exact (he.add (((continuousOn_const.mul hr).mul hr).div hn
    (fun x hx => ne_of_gt (Complex.normSq_pos.mpr (hne x hx))))).sqrt

/-- Local C1 regularity of an actual nonvanishing curve proves integrability
of its cone speed on the closed parameter interval. -/
theorem integrableOn_curveSpeed (hbar coupling : ℝ) {γ : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 γ t)
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) :
    IntegrableOn (fun t => speed hbar coupling (γ t) (deriv γ t)) (Icc 0 1) := by
  apply ContinuousOn.integrableOn_Icc
  apply continuousOn_speed hbar coupling
    (fun t ht => (hγ t ht).continuousAt.continuousWithinAt) _ hne
  exact fun t ht => ((hγ t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

/-- Local C1 density and phase on the positive chart give genuinely
integrable arbitrary-coupling source speed. -/
theorem integrableOn_sourceSpeed (hbar coupling : ℝ) (hh : 0 < hbar) {ρ Φ : ℝ → ℝ}
    (hρ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 ρ t)
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 Φ t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ρ t) :
    IntegrableOn (sourceSpeed hbar coupling ρ Φ) (Icc 0 1) := by
  have hcρ : ContinuousOn ρ (Icc 0 1) :=
    fun t ht => (hρ t ht).continuousAt.continuousWithinAt
  have hcdρ : ContinuousOn (deriv ρ) (Icc 0 1) :=
    fun t ht => ((hρ t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hcdΦ : ContinuousOn (deriv Φ) (Icc 0 1) :=
    fun t ht => ((hΦ t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  exact (((continuousOn_const.div (continuousOn_const.mul hcρ)
    (fun t ht => mul_ne_zero (pow_ne_zero _ hh.ne') (ne_of_gt (hpos t ht)))).mul
    (hcdρ.pow 2)).add (hcρ.mul (hcdΦ.pow 2))).sqrt.integrableOn_Icc

/-- Extended length integrates the actual cone-tensor speed of the curve. -/
noncomputable def curveELength (hbar coupling : ℝ) (γ : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (speed hbar coupling (γ t) (deriv γ t))

/-- The actual cone length dominates the Euclidean length by the positive
uniform lower speed factor; no curve regularity is needed for this comparison. -/
theorem curveELength_lower_bound (hbar coupling : ℝ) (hh : 0 < hbar)
    (hc : 0 < coupling) (γ : ℝ → ℂ) :
    ENNReal.ofReal (lowerFactor hbar coupling) * PuncturedPlaneDetour.curveELength γ ≤
      curveELength hbar coupling γ := by
  unfold curveELength PuncturedPlaneDetour.curveELength
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro t
  dsimp only
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (lowerFactor_pos hbar coupling hh hc).le]
  exact ENNReal.ofReal_le_ofReal (speed_lower_bound hbar coupling hh hc (γ t) (deriv γ t))

/-- The actual cone length is bounded above by the Euclidean length times
the uniform upper speed factor. -/
theorem curveELength_upper_bound (hbar coupling : ℝ) (γ : ℝ → ℂ) :
    curveELength hbar coupling γ ≤
      ENNReal.ofReal (upperFactor hbar coupling) * PuncturedPlaneDetour.curveELength γ := by
  unfold curveELength PuncturedPlaneDetour.curveELength
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro t
  dsimp only
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (upperFactor_pos hbar coupling).le]
  exact ENNReal.ofReal_le_ofReal (speed_upper_bound hbar coupling (γ t) (deriv γ t))

/-- Canonical coupling recovers the original actual Euclidean curve length. -/
theorem curveELength_canonical (hbar : ℝ) (hh : 0 < hbar) (γ : ℝ → ℂ) :
    curveELength hbar (hbar ^ 2 / 4) γ = PuncturedPlaneDetour.curveELength γ := by
  unfold curveELength PuncturedPlaneDetour.curveELength
  simp only [speed_canonical hbar hh, ofReal_norm]

/-- A local C1 nonvanishing curve has the ordinary integral representation
of actual cone length, with integrability proved from those hypotheses. -/
theorem curveELength_eq_integral (hbar coupling : ℝ) {γ : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 γ t)
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) :
    curveELength hbar coupling γ =
      ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, speed hbar coupling (γ t) (deriv γ t)) := by
  exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_curveSpeed hbar coupling hγ hne)
    (Filter.Eventually.of_forall fun t => speed_nonneg hbar coupling (γ t) (deriv γ t))).symm

/-- Actual cone length of a differentiable positive-density real phase curve
is the extended integral of the literal source metric speed. -/
theorem curveELength_polarField (hbar coupling : ℝ) {ρ Φ : ℝ → ℝ}
    (hρ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ ρ t)
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ Φ t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ρ t) :
    curveELength hbar coupling (polarField ρ Φ) =
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (sourceSpeed hbar coupling ρ Φ t) := by
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [speed_deriv_polarField hbar coupling (hρ t ht) (hΦ t ht) (hpos t ht)]

/-- Local C1 positive-density real phase curves have a genuinely integrable
source-speed formula for the ordinary cone length. -/
theorem curveELength_polarField_eq_integral (hbar coupling : ℝ) (hh : 0 < hbar)
    {ρ Φ : ℝ → ℝ}
    (hρ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 ρ t)
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 Φ t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ρ t) :
    curveELength hbar coupling (polarField ρ Φ) =
      ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, sourceSpeed hbar coupling ρ Φ t) := by
  rw [curveELength_polarField hbar coupling
    (fun t ht => (hρ t ht).differentiableAt (by norm_num))
    (fun t ht => (hΦ t ht).differentiableAt (by norm_num)) hpos]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrableOn_sourceSpeed hbar coupling hh hρ hΦ hpos)
    (Filter.Eventually.of_forall fun t => Real.sqrt_nonneg _)).symm

end FoliationQM.ConeSpeed
