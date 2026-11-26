module

public import FoliationQM.ConeIntrinsicMetric
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Exact radial distances in the genuine cone metric

Sources: v13 `lem:uniqueness`, `eq:lambda_metric`. The radial lower bound is
derived from the actual derivative of modulus, the source tensor speed, and
the fundamental theorem of calculus along genuine paths. Positive straight
radial segments attain it. No distance to a completed tip is assumed here.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ConeRadial

open ConeMetricExtension ConeSpeed ConeManifold ConeIntrinsicMetric
open Set MeasureTheory Topology
open scoped ENNReal Manifold ComplexConjugate

/-- The radial stretching factor of the actual source metric. -/
def radialScale (hbar coupling : ℝ) : ℝ := Real.sqrt (radialFactorSq hbar coupling)

/-- Positive physical parameters give a strictly positive radial scale. -/
theorem radialScale_pos (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling) :
    0 < radialScale hbar coupling :=
  Real.sqrt_pos.mpr (radialFactorSq_pos hbar coupling hh hc)

/-- The radial scale agrees with the source radial coordinate coefficient. -/
theorem radialScale_eq (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling) :
    radialScale hbar coupling = 2 * Real.sqrt coupling / hbar := by
  rw [radialScale, radialFactorSq, Real.sqrt_div (by positivity),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq hh.le]
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Squaring the source radial scale gives its radial tensor coefficient. -/
theorem radialScale_sq (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling) :
    radialScale hbar coupling ^ 2 = 4 * coupling / hbar ^ 2 :=
  Real.sq_sqrt (radialFactorSq_pos hbar coupling hh hc).le

/-- The radial scale is one exactly at canonical coupling. -/
theorem radialScale_eq_one_iff (hbar coupling : ℝ) (hh : 0 < hbar) :
    radialScale hbar coupling = 1 ↔ coupling = hbar ^ 2 / 4 := by
  rw [radialScale, Real.sqrt_eq_one, radialFactorSq,
    div_eq_iff (pow_ne_zero 2 hh.ne'), one_mul]
  constructor <;> intro h <;> linarith

/-- The actual derivative of modulus is the normalized radial projection. -/
theorem hasDerivAt_norm {γ : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hne : γ t ≠ 0) :
    HasDerivAt (fun u => ‖γ u‖) (radial (γ t) v / ‖γ t‖) t := by
  have hn : ‖γ t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have h := hγ.norm_sq.sqrt (pow_ne_zero 2 hn)
  convert h using 1
  · funext u
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · rw [Real.sqrt_sq (norm_nonneg _), Complex.inner]
    unfold radial
    rw [mul_comm v (conj (γ t))]
    field_simp

/-- The ordinary derivative of modulus uses the actual coordinate derivative. -/
theorem deriv_norm_eq {γ : ℝ → ℂ} {t : ℝ}
    (hγ : DifferentiableAt ℝ γ t) (hne : γ t ≠ 0) :
    deriv (fun u => ‖γ u‖) t = radial (γ t) (deriv γ t) / ‖γ t‖ :=
  (hasDerivAt_norm hγ.hasDerivAt hne).deriv

/-- Source energy dominates its full radial contribution. -/
theorem radial_energy_le (hbar coupling : ℝ) (z v : ℂ) :
    radialFactorSq hbar coupling * (radial z v / ‖z‖) ^ 2 ≤
      tensor hbar coupling z v v := by
  rw [div_pow, ← Complex.normSq_eq_norm_sq, tensor_self_eq]
  nlinarith [radial_quotient_le z v]

/-- Actual source speed dominates radial scale times absolute radial speed. -/
theorem radial_speed_le (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling)
    (z v : ℂ) :
    radialScale hbar coupling * |radial z v / ‖z‖| ≤ speed hbar coupling z v := by
  have h := Real.sqrt_le_sqrt (radial_energy_le hbar coupling z v)
  rw [Real.sqrt_mul (radialFactorSq_pos hbar coupling hh hc).le,
    Real.sqrt_sq_eq_abs] at h
  exact h

/-- The modulus derivative of a genuine nonzero curve obeys the exact radial bound. -/
theorem radial_deriv_le_speed (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling)
    {γ : ℝ → ℂ} {t : ℝ} (hγ : DifferentiableAt ℝ γ t) (hne : γ t ≠ 0) :
    radialScale hbar coupling * |deriv (fun u => ‖γ u‖) t| ≤
      speed hbar coupling (γ t) (deriv γ t) := by
  rw [deriv_norm_eq hγ hne]
  exact radial_speed_le hbar coupling hh hc _ _

/-- Every genuine nonvanishing C1 curve pays at least its radial endpoint
variation, by the fundamental theorem of calculus and the actual speed bound. -/
theorem radial_edist_le_curveELength (hbar coupling : ℝ) (hh : 0 < hbar)
    (hc : 0 < coupling) {z w : ℂ} {γ : ℝ → ℂ}
    (hγ : PuncturedPlaneDetour.Admissible z w γ) :
    ENNReal.ofReal (radialScale hbar coupling * |‖z‖ - ‖w‖|) ≤
      ConeSpeed.curveELength hbar coupling γ := by
  have hnorm : ContDiffOn ℝ 1 (fun t => ‖γ t‖) (Icc 0 1) := hγ.1.norm ℂ hγ.2.2.2
  have hfund := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hnorm zero_le_one
  rw [hγ.2.1, hγ.2.2.1, Real.enorm_eq_ofReal_abs, abs_sub_comm] at hfund
  rw [ENNReal.ofReal_mul (radialScale_pos hbar coupling hh hc).le]
  apply (mul_le_mul' (le_refl _) hfund).trans
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold ConeSpeed.curveELength
  simp only [← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_mono' measurableSet_Ioo
  intro t ht
  have hd : DifferentiableAt ℝ γ t :=
    (hγ.1 t ⟨ht.1.le, ht.2.le⟩).differentiableWithinAt (by norm_num) |>.differentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (radialScale_pos hbar coupling hh hc).le]
  exact ENNReal.ofReal_le_ofReal
    (radial_deriv_le_speed hbar coupling hh hc hd (hγ.2.2.2 t ⟨ht.1.le, ht.2.le⟩))

/-- Taking the actual path infimum preserves the exact radial endpoint bound. -/
theorem radial_intrinsicEDist_lower_bound (hbar coupling : ℝ) (hh : 0 < hbar)
    (hc : 0 < coupling) (p q : Point hbar coupling) :
    ENNReal.ofReal (radialScale hbar coupling * |‖p.value‖ - ‖q.value‖|) ≤
      intrinsicEDist hbar coupling p q := by
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, hzero, hone, hsmooth, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr
  have ha : PuncturedPlaneDetour.Admissible p.value q.value (fun t => (γ t).value) :=
    ⟨contDiffOn_value_curve hsmooth, congrArg Point.value hzero,
      congrArg Point.value hone, fun t _ => (γ t).value_ne_zero⟩
  have h := radial_edist_le_curveELength hbar coupling hh hc ha
  have hlenEq : ConeSpeed.curveELength hbar coupling (fun t => (γ t).value) =
      Manifold.pathELength 𝓘(ℝ, ℂ) γ 0 1 := (pathELength_eq_integral γ 0 1).symm
  exact (h.trans_eq hlenEq).trans_lt hlen

/-- Moving the base point along a nonzero real radial factor leaves the
same tensor on a fixed coordinate tangent. -/
theorem tensor_smul_position (hbar coupling a : ℝ) (ha : a ≠ 0) (z v : ℂ) :
    tensor hbar coupling (a • z) v v = tensor hbar coupling z v v := by
  have hr : radial (a • z) v = a * radial z v := by
    simp [radial, Complex.mul_re]
    ring
  have hn : Complex.normSq (a • z) = a ^ 2 * Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, ← Complex.normSq_eq_norm_sq]
  rw [tensor_self_eq, tensor_self_eq, hr, hn, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero 2 ha)]

/-- Nonzero radial movement of the base point preserves coordinate speed. -/
theorem speed_smul_position (hbar coupling a : ℝ) (ha : a ≠ 0) (z v : ℂ) :
    speed hbar coupling (a • z) v = speed hbar coupling z v := by
  rw [speed, speed, tensor_smul_position hbar coupling a ha]

/-- A tangent equal to its position vector is purely radial. -/
theorem tensor_self_position (hbar coupling : ℝ) (z : ℂ) :
    tensor hbar coupling z z z = radialFactorSq hbar coupling * ‖z‖ ^ 2 := by
  have hr : radial z z = Complex.normSq z := by
    unfold radial
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [tensor_self_eq, hr, ← Complex.normSq_eq_norm_sq]
  by_cases hz : Complex.normSq z = 0
  · simp [hz]
  · field_simp
    ring

/-- Pure radial coordinate velocity has exactly the stretched Euclidean speed. -/
theorem speed_self_position (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling)
    (z : ℂ) : speed hbar coupling z z = radialScale hbar coupling * ‖z‖ := by
  rw [speed, tensor_self_position, Real.sqrt_mul (radialFactorSq_pos hbar coupling hh hc).le,
    Real.sqrt_sq (norm_nonneg _)]
  rfl

/-- The straight positive radial interpolation in physical complex coordinates. -/
def rayCurve (z : ℂ) (s t : ℝ) : ℂ := (1 + t * (s - 1)) • z

/-- The straight radial curve has the actual constant radial derivative. -/
theorem hasDerivAt_rayCurve (z : ℂ) (s t : ℝ) :
    HasDerivAt (rayCurve z s) ((s - 1) • z) t := by
  simpa only [zero_add, one_mul] using!
    (((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).mul_const (s - 1))).smul_const z)

/-- The ordinary derivative of a radial interpolation is its constant velocity. -/
theorem deriv_rayCurve (z : ℂ) (s t : ℝ) :
    deriv (rayCurve z s) t = (s - 1) • z := (hasDerivAt_rayCurve z s t).deriv

/-- Positive endpoint scaling keeps the full radial segment strictly away from zero. -/
theorem rayCurve_factor_pos {s t : ℝ} (hs : 0 < s) (ht : t ∈ Icc 0 1) :
    0 < 1 + t * (s - 1) := by
  by_cases ht1 : t = 1
  · simp [ht1, hs]
  · have hleft : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)
    have hright : 0 ≤ t * s := mul_nonneg ht.1 hs.le
    nlinarith

/-- Every positive straight radial interpolation is an admissible actual curve. -/
theorem admissible_rayCurve {z : ℂ} (hz : z ≠ 0) {s : ℝ} (hs : 0 < s) :
    PuncturedPlaneDetour.Admissible z ((s : ℂ) * z) (rayCurve z s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : ContDiff ℝ 1 (rayCurve z s) := by
      unfold rayCurve
      fun_prop
    exact h.contDiffOn
  · simp [rayCurve]
  · simp [rayCurve, Complex.real_smul]
  · intro t ht
    exact smul_ne_zero (rayCurve_factor_pos hs ht).ne' hz

/-- A positive radial segment has constant speed with the exact source radial scale. -/
theorem speed_rayCurve (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling)
    (z : ℂ) {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : t ∈ Icc 0 1) :
    speed hbar coupling (rayCurve z s t) (deriv (rayCurve z s) t) =
      radialScale hbar coupling * |1 - s| * ‖z‖ := by
  rw [deriv_rayCurve, rayCurve,
    speed_smul_position hbar coupling _ (rayCurve_factor_pos hs ht).ne',
    speed_smul, speed_self_position hbar coupling hh hc, abs_sub_comm]
  ring

/-- Integrating the actual radial speed gives the exact segment length. -/
theorem curveELength_rayCurve (hbar coupling : ℝ) (hh : 0 < hbar) (hc : 0 < coupling)
    (z : ℂ) {s : ℝ} (hs : 0 < s) :
    ConeSpeed.curveELength hbar coupling (rayCurve z s) =
      ENNReal.ofReal (radialScale hbar coupling * |1 - s| * ‖z‖) := by
  unfold ConeSpeed.curveELength
  have he : (∫⁻ t in Icc (0 : ℝ) 1,
      ENNReal.ofReal (speed hbar coupling (rayCurve z s t) (deriv (rayCurve z s) t))) =
      ∫⁻ _t in Icc (0 : ℝ) 1,
        ENNReal.ofReal (radialScale hbar coupling * |1 - s| * ‖z‖) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [speed_rayCurve hbar coupling hh hc z hs ht]
  rw [he]
  simp

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]

/-- The genuine intrinsic distance bounds the exact scaled radial variation. -/
theorem radial_dist_lower_bound (p q : Point hbar coupling) :
    radialScale hbar coupling * |‖p.value‖ - ‖q.value‖| ≤ dist p q := by
  have h := ENNReal.toReal_mono (intrinsicEDist_ne_top hbar coupling p q)
    (radial_intrinsicEDist_lower_bound hbar coupling Fact.out Fact.out p q)
  simpa only [← edist_eq_intrinsicEDist, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
    ENNReal.toReal_ofReal (mul_nonneg (radialScale_pos hbar coupling Fact.out Fact.out).le
      (abs_nonneg _))] using h

/-- Same-ray points attain the radial lower bound by the actual positive
straight radial segment. -/
theorem dist_smul (p q : Point hbar coupling) (s : ℝ) (hs : 0 < s)
    (hq : q.value = (s : ℂ) * p.value) :
    dist p q = radialScale hbar coupling * |1 - s| * ‖p.value‖ := by
  apply le_antisymm
  · have ha := admissible_rayCurve p.value_ne_zero hs
    rw [← hq] at ha
    have h := ConeManifold.intrinsicEDist_le_curveELength p q ha
    rw [curveELength_rayCurve hbar coupling Fact.out Fact.out p.value hs,
      ← edist_eq_intrinsicEDist] at h
    have hp : 0 ≤ radialScale hbar coupling * |1 - s| * ‖p.value‖ := by
      exact mul_nonneg (mul_nonneg (radialScale_pos hbar coupling Fact.out Fact.out).le
        (abs_nonneg _)) (norm_nonneg _)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.toReal_ofReal hp] using hreal
  · have h := radial_dist_lower_bound hbar coupling p q
    rw [hq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] at h
    have he : |‖p.value‖ - s * ‖p.value‖| = |1 - s| * ‖p.value‖ := by
      rw [show ‖p.value‖ - s * ‖p.value‖ = (1 - s) * ‖p.value‖ by ring,
        abs_mul, abs_of_nonneg (norm_nonneg _)]
    rw [he] at h
    simpa only [mul_assoc] using h

end FoliationQM.ConeRadial
