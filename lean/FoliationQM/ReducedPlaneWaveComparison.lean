module

public import FoliationQM.ReducedPlaneWave
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantitative comparison of the actual reduced plane waves

Source: v13 `cor:schrodinger`, component kinds C and D. The same spatial
wave vector and the actual physical-time derivatives are compared at the
reduced and Schrödinger frequencies. All estimates use the explicit sum of
three spatial squares and retain their physical constants. Time is bounded
only when these pointwise estimates are used on a common region.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ReducedPlaneWaveComparison

open LorentzCoordinates ReducedMassShellFrequency ReducedPlaneWave
open PolarSecondDifferential
open Madelung (coordinateVector)

private theorem phase_gap (w v : ℝ) (k : Spatial) (x : Covector) :
    ‖mode w k x - mode v k x‖ ≤ |x 0| * |w - v| := by
  have he : mode w k x - mode v k x =
      (Complex.exp (Complex.I * (((v - w) * x 0 : ℝ) : ℂ)) - 1) * mode v k x := by
    rw [sub_mul, one_mul]
    congr 1
    unfold mode
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, norm_mul, norm_mode, mul_one]
  calc
    _ ≤ ‖(v - w) * x 0‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |x 0| * |w - v| := by
      rw [Real.norm_eq_abs, abs_mul, abs_sub_comm]
      ring

private theorem frequency_gap_norm (p : MassiveParameters) (k : Spatial) :
    ‖(reducedFrequency p k : ℂ) - (schrodingerFrequency p k : ℂ)‖ ≤
      (p.hbar ^ 3 / (8 * p.m ^ 3)) * speedSq k ^ 2 / p.c ^ 2 := by
  have h := frequency_comparison p k
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr h.2.1)]
  calc
    _ = schrodingerFrequency p k - reducedFrequency p k := by ring
    _ ≤ _ := h.2.2
    _ = _ := by ring

private theorem time_derivative (w : ℝ) (k : Spatial) (x : Covector) :
    directionalDerivative (mode w k) (coordinateVector 0) x =
      -Complex.I * (w : ℂ) * mode w k x := by
  rw [directional_mode]
  simp [coordinateVector, spatialDot]

private theorem spatial_second (w : ℝ) (k : Spatial) (x : Covector) (i : Fin 3) :
    secondDirectionalDerivative (mode w k) (coordinateVector i.succ) x =
      -(k i : ℂ) ^ 2 * mode w k x := by
  fin_cases i <;> simp [second_directional_mode, coordinateVector, spatialDot]

/-- The actual reduced mode approaches its Schrödinger mode with a quartic spatial error and the explicit inverse-square speed factor. -/
theorem field_gap (p : MassiveParameters) (k : Spatial) (x : Covector) :
    ‖mode (reducedFrequency p k) k x - mode (schrodingerFrequency p k) k x‖ ≤
      |x 0| * (p.hbar ^ 3 / (8 * p.m ^ 3)) * speedSq k ^ 2 / p.c ^ 2 := by
  have h := phase_gap (reducedFrequency p k) (schrodingerFrequency p k) k x
  have hg := frequency_gap_norm p k
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hg
  calc
    _ ≤ |x 0| * |reducedFrequency p k - schrodingerFrequency p k| := h
    _ ≤ |x 0| * ((p.hbar ^ 3 / (8 * p.m ^ 3)) * speedSq k ^ 2 / p.c ^ 2) :=
      mul_le_mul_of_nonneg_left hg (abs_nonneg _)
    _ = _ := by ring

/-- The true time-derivative error includes both the frequency gap and the accumulated phase error, including at time zero. -/
theorem time_first_gap (p : MassiveParameters) (k : Spatial) (x : Covector) :
    ‖directionalDerivative (mode (reducedFrequency p k) k) (coordinateVector 0) x -
      directionalDerivative (mode (schrodingerFrequency p k) k) (coordinateVector 0) x‖ ≤
      (p.hbar ^ 3 / (8 * p.m ^ 3)) *
        (speedSq k ^ 2 + |x 0| * (p.hbar / (2 * p.m)) * speedSq k ^ 3) / p.c ^ 2 := by
  have hc := frequency_comparison p k
  have hn : 0 ≤ schrodingerFrequency p k := hc.1.trans hc.2.1
  have he : directionalDerivative (mode (reducedFrequency p k) k) (coordinateVector 0) x -
      directionalDerivative (mode (schrodingerFrequency p k) k) (coordinateVector 0) x =
      -Complex.I *
        (((reducedFrequency p k : ℂ) - (schrodingerFrequency p k : ℂ)) *
            mode (reducedFrequency p k) k x +
          (schrodingerFrequency p k : ℂ) *
            (mode (reducedFrequency p k) k x - mode (schrodingerFrequency p k) k x)) := by
    rw [time_derivative, time_derivative]
    ring
  rw [he, norm_mul, norm_neg, Complex.norm_I, one_mul]
  calc
    _ ≤ ‖((reducedFrequency p k : ℂ) - (schrodingerFrequency p k : ℂ)) *
          mode (reducedFrequency p k) k x‖ +
        ‖(schrodingerFrequency p k : ℂ) *
          (mode (reducedFrequency p k) k x - mode (schrodingerFrequency p k) k x)‖ :=
      norm_add_le _ _
    _ = ‖(reducedFrequency p k : ℂ) - (schrodingerFrequency p k : ℂ)‖ +
        schrodingerFrequency p k *
          ‖mode (reducedFrequency p k) k x - mode (schrodingerFrequency p k) k x‖ := by
      rw [norm_mul, norm_mode, mul_one, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hn]
    _ ≤ (p.hbar ^ 3 / (8 * p.m ^ 3)) * speedSq k ^ 2 / p.c ^ 2 +
        schrodingerFrequency p k *
          (|x 0| * (p.hbar ^ 3 / (8 * p.m ^ 3)) * speedSq k ^ 2 / p.c ^ 2) :=
      add_le_add (frequency_gap_norm p k)
        (mul_le_mul_of_nonneg_left (field_gap p k x) hn)
    _ = _ := by unfold schrodingerFrequency; ring

/-- Each actual spatial second derivative has a sixth-order spatial error bound, with no Laplacian multiplicity factor. -/
theorem spatial_second_gap (p : MassiveParameters) (k : Spatial) (x : Covector) (i : Fin 3) :
    ‖secondDirectionalDerivative (mode (reducedFrequency p k) k) (coordinateVector i.succ) x -
      secondDirectionalDerivative (mode (schrodingerFrequency p k) k) (coordinateVector i.succ) x‖ ≤
      |x 0| * (p.hbar ^ 3 / (8 * p.m ^ 3)) * speedSq k ^ 3 / p.c ^ 2 := by
  have hk : k i ^ 2 ≤ speedSq k := by
    rw [speedSq_eq_sum]
    fin_cases i <;> dsimp <;> nlinarith [sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2)]
  have hb : 0 ≤ |x 0| * (p.hbar ^ 3 / (8 * p.m ^ 3)) * speedSq k ^ 2 / p.c ^ 2 := by
    have hm := p.m_pos
    have hh := p.hbar_pos
    positivity
  rw [spatial_second, spatial_second, ← mul_sub]
  simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ k i ^ 2 *
        (|x 0| * (p.hbar ^ 3 / (8 * p.m ^ 3)) * speedSq k ^ 2 / p.c ^ 2) :=
      mul_le_mul_of_nonneg_left (field_gap p k x) (sq_nonneg _)
    _ ≤ speedSq k *
        (|x 0| * (p.hbar ^ 3 / (8 * p.m ^ 3)) * speedSq k ^ 2 / p.c ^ 2) :=
      mul_le_mul_of_nonneg_right hk hb
    _ = _ := by ring

/-- The actual second time derivative is bounded by a quartic spatial polynomial independent of the speed parameter. -/
theorem time_second_bound (p : MassiveParameters) (k : Spatial) (x : Covector) :
    ‖secondDirectionalDerivative (mode (reducedFrequency p k) k) (coordinateVector 0) x‖ ≤
      (p.hbar / (2 * p.m)) ^ 2 * speedSq k ^ 2 := by
  have he : secondDirectionalDerivative (mode (reducedFrequency p k) k)
      (coordinateVector 0) x =
      -(reducedFrequency p k : ℂ) ^ 2 * mode (reducedFrequency p k) k x := by
    simpa [coordinateVector, spatialDot] using
      second_directional_mode (reducedFrequency p k) k x (coordinateVector 0)
  rw [he]
  simp only [norm_mul, norm_neg, norm_pow, norm_mode, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  have h := frequency_comparison p k
  calc
    _ ≤ schrodingerFrequency p k ^ 2 := pow_le_pow_left₀ h.1 h.2.1 2
    _ = _ := by unfold schrodingerFrequency; ring

end FoliationQM.ReducedPlaneWaveComparison
