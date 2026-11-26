module

public import FoliationQM.ConeRadialCompletion

/-!
# Actual one-turn clock-curve length in the positive cone

Sources: v13 `lem:uniqueness`, `eq:lambda_metric`, and `eq:cone_angle`.
The fixed physical clock traces the actual curve `R * exp(2*pi*t*i)` on
`[0,1]`. Its cone-tensor speed and its genuine weighted integral length
are computed from its derivative. These are one-turn curve-length results;
no identification with metric variation or Hausdorff circumference is assumed.
-/

@[expose] public section

noncomputable section

namespace FoliationQM.ConeCircleLength

open MasterMetricAndCone PolarDifferential Set MeasureTheory
open scoped ENNReal ContDiff Manifold

/-- One complete physical clock turn at fixed positive amplitude. -/
def orbit (R : ℝ) (t : ℝ) : ℂ :=
  (R : ℂ) * phase (2 * Real.pi * t)

/-- The actual orbit is smooth to every order on its real parameter line. -/
theorem contDiff_orbit (R : ℝ) (n : ℕ∞ω) : ContDiff ℝ n (orbit R) := by
  unfold orbit phase
  exact contDiff_const.mul
    (((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
      contDiff_const).cexp)

/-- The orbit has its prescribed physical amplitude at every parameter. -/
theorem norm_orbit (R : ℝ) (hR : 0 ≤ R) (t : ℝ) : ‖orbit R t‖ = R := by
  change ‖(R : ℂ) * (Circle.exp (2 * Real.pi * t) : ℂ)‖ = R
  rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hR]

/-- Positive amplitude makes the entire actual orbit avoid the missing origin. -/
theorem orbit_ne_zero (R : ℝ) (hR : 0 < R) (t : ℝ) : orbit R t ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [norm_orbit R hR.le t]; exact hR.ne')

/-- The physical clock starts on the positive real ray. -/
theorem orbit_zero (R : ℝ) : orbit R 0 = (R : ℂ) := by
  simp [orbit, phase]

/-- One unit of the curve parameter is exactly one physical clock period. -/
theorem orbit_one (R : ℝ) : orbit R 1 = (R : ℂ) := by
  change (R : ℂ) * (Circle.exp (2 * Real.pi * 1) : ℂ) = (R : ℂ)
  simp

/-- The complete clock turn is a genuine admissible closed nonvanishing C1 curve. -/
theorem admissible_orbit (R : ℝ) (hR : 0 < R) :
    PuncturedPlaneDetour.Admissible (R : ℂ) (R : ℂ) (orbit R) := by
  exact ⟨(contDiff_orbit R 1).contDiffOn, orbit_zero R, orbit_one R,
    fun t _ => orbit_ne_zero R hR t⟩

/-- The orbit is the actual polar field with constant density and linear phase. -/
theorem orbit_eq_polarField (R : ℝ) (hR : 0 ≤ R) :
    orbit R = polarField (fun _ : ℝ => R ^ 2) (fun t => 2 * Real.pi * t) := by
  funext t
  simp only [orbit, polarField, Real.sqrt_sq hR]

/-- The literal source polar-speed expression is constant on this clock orbit. -/
theorem sourceSpeed_orbit (hbar coupling R : ℝ) (hR : 0 ≤ R) (t : ℝ) :
    ConeSpeed.sourceSpeed hbar coupling (fun _ : ℝ => R ^ 2)
      (fun u => 2 * Real.pi * u) t = 2 * Real.pi * R := by
  simp only [ConeSpeed.sourceSpeed, deriv_const, deriv_const_mul_id,
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
  rw [show R ^ 2 * (2 * Real.pi) ^ 2 = (2 * Real.pi * R) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-- The actual derivative's weighted cone speed is independent of the coupling
on a fixed-radius clock turn. -/
theorem speed_orbit (hbar coupling R : ℝ) (hR : 0 < R) (t : ℝ) :
    ConeSpeed.speed hbar coupling (orbit R t) (deriv (orbit R) t) =
      2 * Real.pi * R := by
  rw [orbit_eq_polarField R hR.le]
  have hΦ : DifferentiableAt ℝ (fun u : ℝ => 2 * Real.pi * u) t := by fun_prop
  exact (ConeSpeed.speed_deriv_polarField hbar coupling
    (differentiableAt_const (R ^ 2)) hΦ (sq_pos_of_pos hR)).trans
      (sourceSpeed_orbit hbar coupling R hR.le t)

/-- The actual cone speed is integrable on the entire closed parameter interval. -/
theorem integrableOn_speed_orbit (hbar coupling R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun t => ConeSpeed.speed hbar coupling (orbit R t)
      (deriv (orbit R) t)) (Icc (0 : ℝ) 1) :=
  ConeSpeed.integrableOn_curveSpeed hbar coupling
    (fun _ _ => (contDiff_orbit R 1).contDiffAt)
    (fun t _ => orbit_ne_zero R hR t)

/-- The ordinary integral of actual cone speed is the one-turn length `2*pi*R`. -/
theorem integral_speed_orbit (hbar coupling R : ℝ) (hR : 0 < R) :
    (∫ t in Icc (0 : ℝ) 1, ConeSpeed.speed hbar coupling (orbit R t)
      (deriv (orbit R) t)) = 2 * Real.pi * R := by
  simp only [speed_orbit hbar coupling R hR]
  simp

/-- The extended length of the actual one-turn curve is precisely `2*pi*R`. -/
theorem curveELength_orbit (hbar coupling R : ℝ) (hR : 0 < R) :
    ConeSpeed.curveELength hbar coupling (orbit R) =
      ENNReal.ofReal (2 * Real.pi * R) := by
  rw [ConeSpeed.curveELength_eq_integral hbar coupling
    (fun _ _ => (contDiff_orbit R 1).contDiffAt)
    (fun t _ => orbit_ne_zero R hR t)]
  rw [integral_speed_orbit hbar coupling R hR]

/-- The finite real length also equals the ordinary one-turn speed integral. -/
theorem curveELength_orbit_toReal (hbar coupling R : ℝ) (hR : 0 < R) :
    (ConeSpeed.curveELength hbar coupling (orbit R)).toReal = 2 * Real.pi * R := by
  rw [curveELength_orbit hbar coupling R hR, ENNReal.toReal_ofReal (by positivity)]

/-- The actual nonvanishing clock orbit regarded as a punctured-cone curve. -/
def orbitPoint (hbar coupling R : ℝ) (hR : 0 < R) (t : ℝ) :
    ConeManifold.Point hbar coupling :=
  ⟨orbit R t, orbit_ne_zero R hR t⟩

/-- The lifted clock orbit is an actual C1 manifold curve on its full period. -/
theorem contMDiffOn_orbitPoint (hbar coupling R : ℝ) (hR : 0 < R) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (orbitPoint hbar coupling R hR) (Icc 0 1) := by
  apply ConeManifold.contMDiffOn_curve_of_contDiffOn_value
  exact (contDiff_orbit R 1).contDiffOn

/-- Mathlib's actual manifold path length of the clock orbit is the same
one-turn length computed from its source tensor derivative. -/
theorem pathELength_orbitPoint (hbar coupling R : ℝ) (hR : 0 < R) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (orbitPoint hbar coupling R hR) 0 1 =
      ENNReal.ofReal (2 * Real.pi * R) := by
  rw [ConeManifold.pathELength_eq_integral]
  change ConeSpeed.curveELength hbar coupling (orbit R) = _
  exact curveELength_orbit hbar coupling R hR

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]

/-- Every point of the clock orbit is at the exact source radial distance
from the unique completed tip. -/
theorem dist_orbitPoint_tip (R : ℝ) (hR : 0 < R) (t : ℝ) :
    dist (orbitPoint hbar coupling R hR t : ConeCompletion.Completed hbar coupling)
      (ConeCompletion.tip hbar coupling) = ConeRadial.radialScale hbar coupling * R := by
  rw [ConeRadialCompletion.dist_coe_tip]
  exact congrArg (ConeRadial.radialScale hbar coupling * ·) (norm_orbit R hR.le t)

/-- The whole actual clock orbit lies on the corresponding intrinsic metric sphere. -/
theorem orbitPoint_mem_sphere_tip (R : ℝ) (hR : 0 < R) (t : ℝ) :
    (orbitPoint hbar coupling R hR t : ConeCompletion.Completed hbar coupling) ∈
      Metric.sphere (ConeCompletion.tip hbar coupling)
        (ConeRadial.radialScale hbar coupling * R) := by
  rw [Metric.mem_sphere, dist_orbitPoint_tip]

/-- The ratio of this actual one-turn curve length to its intrinsic radial
distance is `2*pi/radialScale`, independent of the chosen positive radius. -/
theorem one_turn_length_div_radius (R : ℝ) (hR : 0 < R) (t : ℝ) :
    (ConeSpeed.curveELength hbar coupling (orbit R)).toReal /
      dist (orbitPoint hbar coupling R hR t : ConeCompletion.Completed hbar coupling)
        (ConeCompletion.tip hbar coupling) =
      2 * Real.pi / ConeRadial.radialScale hbar coupling := by
  rw [curveELength_orbit_toReal hbar coupling R hR, dist_orbitPoint_tip]
  field_simp

/-- Actual one-turn curve length divided by actual tip distance equals the
source cone angle. This does not identify the curve length with Hausdorff
circumference or the metric variation of an arbitrary sphere parameterization. -/
theorem one_turn_length_div_radius_eq_coneAngle (R : ℝ) (hR : 0 < R) (t : ℝ) :
    (ConeSpeed.curveELength hbar coupling (orbit R)).toReal /
      dist (orbitPoint hbar coupling R hR t : ConeCompletion.Completed hbar coupling)
        (ConeCompletion.tip hbar coupling) = coneAngle hbar coupling := by
  rw [one_turn_length_div_radius, ConeRadial.radialScale_eq hbar coupling Fact.out Fact.out,
    coneAngle]
  field_simp

/-- The actual one-turn length/radius ratio equals the Euclidean value
exactly at canonical coupling. -/
theorem one_turn_length_div_radius_eq_two_pi_iff (R : ℝ) (hR : 0 < R) (t : ℝ) :
    (ConeSpeed.curveELength hbar coupling (orbit R)).toReal /
      dist (orbitPoint hbar coupling R hR t : ConeCompletion.Completed hbar coupling)
        (ConeCompletion.tip hbar coupling) = 2 * Real.pi ↔
      coupling = hbar ^ 2 / 4 := by
  rw [one_turn_length_div_radius_eq_coneAngle]
  exact coneAngle_eq_two_pi_iff hbar coupling Fact.out Fact.out

end FoliationQM.ConeCircleLength
