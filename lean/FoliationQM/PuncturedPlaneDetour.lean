module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Arbitrarily short smooth detours in the punctured complex plane

Source: v13 `lem:uniqueness`, canonical metric-completion bridge.
These actual polynomial curves avoid the origin and have Euclidean lengths
arbitrarily close to the chord distance. The resulting infimum is over actual
smooth curves, not an assumed distance formula. Transport to the source polar
Riemannian metric is a separate obligation.
-/

@[expose] public section

namespace FoliationQM.PuncturedPlaneDetour

open Set MeasureTheory
open scoped ENNReal ContDiff

/-- A polynomial perpendicular detour from `z` to `w`, with signed height `η`. -/
noncomputable def detour (z w : ℂ) (η t : ℝ) : ℂ :=
  z + (t : ℂ) * (w - z) + (η * t * (1 - t) : ℝ) * Complex.I * (w - z)

/-- Every detour is smooth on the whole parameter line. -/
theorem contDiff_detour (z w : ℂ) (η : ℝ) : ContDiff ℝ ∞ (detour z w η) := by
  have hof : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := by
    simpa using! Complex.ofRealCLM.contDiff
  have hr : ContDiff ℝ ∞ (fun t : ℝ => η * t * (1 - t)) := by fun_prop
  exact (contDiff_const.add (hof.mul contDiff_const)).add
    (((hof.comp hr).mul contDiff_const).mul contDiff_const)

/-- The detour starts at its prescribed first endpoint. -/
theorem detour_zero (z w : ℂ) (η : ℝ) : detour z w η 0 = z := by
  simp [detour]

/-- The detour ends at its prescribed second endpoint. -/
theorem detour_one (z w : ℂ) (η : ℝ) : detour z w η 1 = w := by
  simp [detour]

/-- The derivative is the chord vector plus its varying perpendicular component. -/
theorem hasDerivAt_detour (z w : ℂ) (η t : ℝ) :
    HasDerivAt (detour z w η)
      ((w - z) * (1 + (η * (1 - 2 * t) : ℝ) * Complex.I)) t := by
  have hreal : HasDerivAt (fun u : ℝ => η * u * (1 - u))
      (η * (1 - 2 * t)) t := by
    convert! (((hasDerivAt_id t).const_mul η).mul
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))) using 1
    simp
    ring
  have hof : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
    simpa using! (Complex.ofRealCLM.hasFDerivAt (x := t)).hasDerivAt
  convert! ((hasDerivAt_const t z).add (hof.mul_const (w - z))).add
    ((hreal.ofReal_comp.mul_const Complex.I).mul_const (w - z)) using 1
  simp
  ring

/-- The ordinary derivative agrees with the explicit polynomial derivative. -/
theorem deriv_detour (z w : ℂ) (η t : ℝ) :
    deriv (detour z w η) t =
      (w - z) * (1 + (η * (1 - 2 * t) : ℝ) * Complex.I) :=
  (hasDerivAt_detour z w η t).deriv

/-- In chord coordinates, the imaginary part separates the detour from zero. -/
theorem detour_div_im (z w : ℂ) (η t : ℝ) (hzw : z ≠ w) :
    (detour z w η t / (w - z)).im = (z / (w - z)).im + η * t * (1 - t) := by
  have hd : w - z ≠ 0 := sub_ne_zero.mpr hzw.symm
  have heq : detour z w η t / (w - z) =
      z / (w - z) + (t : ℂ) + (η * t * (1 - t) : ℝ) * Complex.I := by
    unfold detour
    field_simp
  rw [heq]
  simp

/-- Choosing the detour on the same side as the chord prevents every zero,
including when the original straight segment passes through the origin. -/
theorem detour_ne_zero (z w : ℂ) (η : ℝ) (hz : z ≠ 0) (hw : w ≠ 0)
    (hzw : z ≠ w) (hη : η ≠ 0) (hside : 0 ≤ η * (z / (w - z)).im)
    {t : ℝ} (ht : t ∈ Icc 0 1) : detour z w η t ≠ 0 := by
  rcases ht.1.eq_or_lt with ht0 | ht0
  · simpa [← ht0, detour_zero] using hz
  rcases ht.2.eq_or_lt with ht1 | ht1
  · simpa [ht1, detour_one] using hw
  have hp : 0 < η ^ 2 * (t * (1 - t)) :=
    mul_pos (sq_pos_of_ne_zero hη) (mul_pos ht0 (sub_pos.mpr ht1))
  intro heq
  have hi := detour_div_im z w η t hzw
  rw [heq] at hi
  simp only [zero_div, Complex.zero_im] at hi
  have hm := congrArg (fun r : ℝ => η * r) hi
  nlinarith

/-- The speed is bounded by the chord length times one plus the height. -/
theorem norm_deriv_detour_le (z w : ℂ) (η : ℝ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖deriv (detour z w η) t‖ ≤ ‖w - z‖ * (1 + |η|) := by
  rw [deriv_detour, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖(1 : ℂ) + (η * (1 - 2 * t) : ℝ) * Complex.I‖ ≤
        ‖(1 : ℂ)‖ + ‖(η * (1 - 2 * t) : ℝ) * Complex.I‖ := norm_add_le _ _
    _ = 1 + |η| * |1 - 2 * t| := by
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        mul_one, abs_mul]
    _ ≤ 1 + |η| := by
      have ht' : |1 - 2 * t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
      nlinarith [abs_nonneg η]

/-- The length used below integrates the norm of the actual derivative. -/
noncomputable def curveELength (γ : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv γ t‖ₑ

/-- Every detour has a genuinely integrable speed on the parameter interval. -/
theorem integrableOn_speed_detour (z w : ℂ) (η : ℝ) :
    IntegrableOn (fun t => ‖deriv (detour z w η) t‖) (Icc 0 1) := by
  have hc : Continuous (fun t => ‖deriv (detour z w η) t‖) := by
    simp_rw [deriv_detour]
    fun_prop
  exact hc.continuousOn.integrableOn_Icc

/-- The explicit uniform speed bound controls the actual length integral. -/
theorem curveELength_detour_le (z w : ℂ) (η : ℝ) :
    curveELength (detour z w η) ≤ ENNReal.ofReal (‖w - z‖ * (1 + |η|)) := by
  calc
    curveELength (detour z w η) ≤
        ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal (‖w - z‖ * (1 + |η|)) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_deriv_detour_le z w η ht)
    _ = ENNReal.ofReal (‖w - z‖ * (1 + |η|)) := by simp

/-- Nonzero endpoints have smooth nonvanishing connecting curves with length as close
to their ordinary Euclidean distance as desired. -/
theorem exists_short_detour {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → ℂ, ContDiff ℝ ∞ γ ∧ γ 0 = z ∧ γ 1 = w ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) ∧
      curveELength γ < edist z w + ENNReal.ofReal ε := by
  by_cases hzw : z = w
  · subst w
    refine ⟨fun _ => z, contDiff_const, rfl, rfl, fun _ _ => hz, ?_⟩
    simp [curveELength, hε]
  let δ := ε / (‖w - z‖ + 1)
  have hden : 0 < ‖w - z‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  let η := if 0 ≤ (z / (w - z)).im then δ else -δ
  have habs : |η| = δ := by
    dsimp [η]
    split <;> simp [abs_of_pos hδ, abs_of_neg (neg_neg_of_pos hδ)]
  have hη : η ≠ 0 := by
    intro h
    simp [h] at habs
    linarith
  have hside : 0 ≤ η * (z / (w - z)).im := by
    dsimp [η]
    split
    · positivity
    · exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hδ.le) (by linarith)
  refine ⟨detour z w η, contDiff_detour z w η, detour_zero z w η,
    detour_one z w η, fun t ht => detour_ne_zero z w η hz hw hzw hη hside ht, ?_⟩
  apply (curveELength_detour_le z w η).trans_lt
  rw [habs, edist_dist, ← ENNReal.ofReal_add dist_nonneg hε.le]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
  have hprod : δ * (‖w - z‖ + 1) = ε := div_mul_cancel₀ ε hden.ne'
  have hdist : ‖w - z‖ = dist z w := by rw [dist_comm, dist_eq_norm]
  rw [← hdist]
  nlinarith

/-- Admissible curves are `C¹` on the closed parameter interval, have the
specified endpoints, and avoid zero throughout that interval. -/
def Admissible (z w : ℂ) (γ : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0 = z ∧ γ 1 = w ∧
    ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0

/-- The intrinsic extended distance defined by actual nonvanishing `C¹`
complex curves and the integral of their Euclidean speed. -/
noncomputable def intrinsicEDist (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → ℂ) (_ : Admissible z w γ), curveELength γ

/-- The endpoint distance is a lower bound for the actual length of every
admissible curve, by the fundamental theorem of calculus. -/
theorem edist_le_curveELength {z w : ℂ} {γ : ℝ → ℂ} (hγ : Admissible z w γ) :
    edist z w ≤ curveELength γ := by
  have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hγ.1 zero_le_one
  rw [hγ.2.1, hγ.2.2.1] at h
  simpa only [edist_eq_enorm_sub, enorm_sub_rev, curveELength] using h

/-- Removing the origin does not change the Euclidean intrinsic distance:
the infimum of lengths of actual nonvanishing `C¹` curves is the chord distance. -/
theorem intrinsicEDist_eq_edist {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    intrinsicEDist z w = edist z w := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨γ, hsmooth, hzero, hone, hnonzero, hlen⟩ :=
      exists_short_detour hz hw (ε := (ε : ℝ)) (by exact_mod_cast hε)
    have ha : Admissible z w γ :=
      ⟨hsmooth.contDiffOn.of_le (by simp), hzero, hone, hnonzero⟩
    have hle : intrinsicEDist z w ≤ curveELength γ :=
      iInf_le_of_le γ (iInf_le_of_le ha le_rfl)
    exact hle.trans
      (by simpa only [ENNReal.ofReal_coe_nnreal] using hlen.le)
  · exact le_iInf fun γ => le_iInf fun hγ => edist_le_curveELength hγ

end FoliationQM.PuncturedPlaneDetour
