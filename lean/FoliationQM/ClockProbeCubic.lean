module

public import FoliationQM.ClockProbeLimit
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Actual antipodal probe symmetry and cubic cancellation

Sources: the fourth-order refinement following v13 `eq:kl_fisher_expansion`
in the proof of `thm:clock_sideband`, and the corresponding supplement
paragraph. Each of the actual normalized phase integrals is invariant under
a phase-origin shift. Shifting every phase by pi reverses the displacement,
so every continuous odd displacement function has zero genuine average.
In particular the actual third differential's cubic Taylor term cancels.
The finite-product norm below bounds the probes; it is not substituted for
the positive Euclidean Fisher trace.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ClockProbeCubic

open ClockCircleAverage ClockProbeCovariance ClockProbeLimit
open scoped BigOperators

/-- Shifting the origins of all three actual phase integrals leaves every
function of the physical displacement with the same iterated average. -/
theorem average3_shift_displacement (ell : ℝ) (F : Space → ℝ) (φ : Space) :
    average3 (fun θ => F (displacement ell (φ + θ))) =
      average3 (fun θ => F (displacement ell θ)) := by
  have hvec (t0 t1 t2 : ℝ) :
      φ + ![t0, t1, t2] = ![φ 0 + t0, φ 1 + t1, φ 2 + t2] := by
    ext i
    fin_cases i <;> rfl
  have h2 (a b : ℝ) :
      average (fun t => F (displacement ell ![a, b, φ 2 + t])) =
        average (fun t => F (displacement ell ![a, b, t])) := by
    refine average_shift (f := fun t => F (displacement ell ![a, b, t])) ?_ (φ 2)
    intro t
    apply congrArg F
    ext i
    fin_cases i <;> simp [displacement, Real.cos_add_two_pi]
  have h1 (a : ℝ) :
      average (fun t1 => average (fun t2 => F (displacement ell ![a, φ 1 + t1, t2]))) =
        average (fun t1 => average (fun t2 => F (displacement ell ![a, t1, t2]))) := by
    refine average_shift (f := fun t1 => average (fun t2 => F (displacement ell ![a, t1, t2]))) ?_ (φ 1)
    intro t
    apply congrArg average
    funext t2
    apply congrArg F
    ext i
    fin_cases i <;> simp [displacement, Real.cos_add_two_pi]
  unfold average3
  simp_rw [hvec, h2, h1]
  refine average_shift (f := fun t0 => average (fun t1 => average (fun t2 =>
    F (displacement ell ![t0, t1, t2])))) ?_ (φ 0)
  intro t
  apply congrArg average
  funext t1
  apply congrArg average
  funext t2
  apply congrArg F
  ext i
  fin_cases i <;> simp [displacement, Real.cos_add_two_pi]

/-- A half-turn of every physical clock phase reverses the entire probe. -/
theorem displacement_half_turn (ell : ℝ) (θ : Space) :
    displacement ell ((fun _ => Real.pi) + θ) = -displacement ell θ := by
  ext i
  simp [displacement, Real.cos_add, mul_neg]

/-- The actual three-circle probe average is invariant under antipodal reversal. -/
theorem average3_neg_displacement (ell : ℝ) (F : Space → ℝ) :
    average3 (fun θ => F (-displacement ell θ)) =
      average3 (fun θ => F (displacement ell θ)) := by
  simpa only [displacement_half_turn] using
    average3_shift_displacement ell F (fun _ => Real.pi)

/-- Every odd function of the physical displacement has zero actual average;
continuous examples have genuine integrability as established separately below. -/
theorem average3_odd_displacement (ell : ℝ) {F : Space → ℝ}
    (hodd : ∀ a, F (-a) = -F a) :
    average3 (fun θ => F (displacement ell θ)) = 0 := by
  have h := average3_neg_displacement ell F
  simp_rw [hodd] at h
  have hn : average3 (fun θ => -F (displacement ell θ)) =
      -average3 (fun θ => F (displacement ell θ)) := by
    simpa only [neg_one_mul] using average3_const_mul (-1) (fun θ => F (displacement ell θ))
  rw [hn] at h
  linarith

/-- Every continuous function of the probe is integrable at all three stages
of the actual phase average. -/
theorem iteratedIntegrable_probe (ell : ℝ) {F : Space → ℝ} (hF : Continuous F) :
    IteratedIntegrable (fun θ => F (displacement ell θ)) :=
  iteratedIntegrable_of_continuous (hF.comp (continuous_displacement ell))

/-- The cubic Taylor term of a genuine continuous third differential. -/
def cubic (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Space) ℝ) (a : Space) : ℝ :=
  (1 / 6 : ℝ) * T (fun _ => a)

/-- A continuous trilinear map gives a continuous diagonal cubic term. -/
theorem continuous_cubic (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Space) ℝ) :
    Continuous (cubic T) := by
  unfold cubic
  exact continuous_const.mul (T.cont.comp (continuous_pi (fun _ => continuous_id)))

/-- The actual cubic term is homogeneous of degree three. -/
theorem cubic_smul (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Space) ℝ)
    (ε : ℝ) (a : Space) : cubic T (ε • a) = ε ^ 3 * cubic T a := by
  unfold cubic
  rw [T.map_smul_univ (fun _ => ε) (fun _ => a)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- Every continuous diagonal trilinear term is odd under reversal. -/
theorem cubic_neg (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Space) ℝ)
    (a : Space) : cubic T (-a) = -cubic T a := by
  have h := cubic_smul T (-1) a
  norm_num at h
  exact h

/-- The source cubic Taylor term has zero actual three-circle average. -/
theorem average3_cubic (ell : ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Space) ℝ) :
    average3 (fun θ => cubic T (displacement ell θ)) = 0 :=
  average3_odd_displacement ell (cubic_neg T)

/-- Cubic cancellation persists for every real probe scale, including zero. -/
theorem average3_scaled_cubic (ell ε : ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Space) ℝ) :
    average3 (fun θ => cubic T (ε • displacement ell θ)) = 0 := by
  simp_rw [cubic_smul]
  rw [average3_const_mul, average3_cubic, mul_zero]

/-- The scaled cubic integrand is genuinely integrable at every stage. -/
theorem iteratedIntegrable_scaled_cubic (ell ε : ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Space) ℝ) :
    IteratedIntegrable (fun θ => cubic T (ε • displacement ell θ)) := by
  apply iteratedIntegrable_of_continuous
  exact (continuous_cubic T).comp ((continuous_displacement ell).const_smul ε)

/-- A fourth power of the actual scaled probe norm is uniformly bounded by
the fourth powers of scale and radius. -/
theorem norm_scaled_displacement_pow_four_le (ell ε : ℝ) (θ : Space) :
    ‖ε • displacement ell θ‖ ^ 4 ≤ ε ^ 4 * ell ^ 4 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow]
  have h := norm_displacement_le ell θ
  calc
    |ε| ^ 4 * ‖displacement ell θ‖ ^ 4 ≤ |ε| ^ 4 * |ell| ^ 4 := by
      gcongr
    _ = ε ^ 4 * ell ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl]
      simp only [pow_mul, sq_abs]

/-- The actual averaged fourth norm moment obeys the same uniform bound. -/
theorem norm_average3_scaled_norm_pow_four_le (ell ε : ℝ) :
    ‖average3 (fun θ => ‖ε • displacement ell θ‖ ^ 4)‖ ≤ ε ^ 4 * ell ^ 4 := by
  apply norm_average3_le (by positivity)
  intro θ
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_scaled_displacement_pow_four_le ell ε θ

/-- The scaled fourth norm moment has genuine stagewise phase integrability. -/
theorem iteratedIntegrable_scaled_norm_pow_four (ell ε : ℝ) :
    IteratedIntegrable (fun θ => ‖ε • displacement ell θ‖ ^ 4) := by
  apply iteratedIntegrable_of_continuous
  exact (((continuous_displacement ell).const_smul ε).norm).pow 4

end FoliationQM.ClockProbeCubic
