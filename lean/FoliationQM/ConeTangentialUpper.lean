module

public import FoliationQM.ConeIntrinsicMetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A short-arc upper obstruction for the actual intrinsic cone metric

Source: v13 `lem:uniqueness`, necessity of the canonical metric scale.
Actual short physical circle arcs have source speed `|θ|` and length `|θ|`.
The genuine C1 path infimum is therefore at most this arc length. If the
intrinsic distance is a positive constant times every physical Euclidean
chord, the small-angle sine limit forces that constant to be at most one.
No agreement between metric derivatives and tensor speeds is assumed.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ConeTangentialUpper

open PolarDifferential Set MeasureTheory Topology Filter ConeManifold ConeIntrinsicMetric
open scoped ENNReal ContDiff

/-- The actual physical circle arc with angle increment `θ` on `[0,1]`. -/
def arc (θ t : ℝ) : ℂ := phase (θ * t)

/-- Every short arc is smooth on its whole real parameter line. -/
theorem contDiff_arc (θ : ℝ) (n : ℕ∞ω) : ContDiff ℝ n (arc θ) := by
  unfold arc phase
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
    contDiff_const).cexp

/-- A physical circle arc never reaches the missing origin. -/
theorem arc_ne_zero (θ t : ℝ) : arc θ t ≠ 0 := Complex.exp_ne_zero _

/-- The arc starts at physical phase zero. -/
theorem arc_zero (θ : ℝ) : arc θ 0 = phase 0 := by simp [arc]

/-- The arc ends at the prescribed physical phase. -/
theorem arc_one (θ : ℝ) : arc θ 1 = phase θ := by simp [arc]

/-- These are genuine nonvanishing C1 competitors for the intrinsic infimum. -/
theorem admissible_arc (θ : ℝ) :
    PuncturedPlaneDetour.Admissible (phase 0) (phase θ) (arc θ) :=
  ⟨(contDiff_arc θ 1).contDiffOn, arc_zero θ, arc_one θ,
    fun t _ => arc_ne_zero θ t⟩

/-- The actual arc is the source polar field at constant positive density one. -/
theorem arc_eq_polarField (θ : ℝ) :
    arc θ = polarField (fun _ : ℝ => 1) (fun t => θ * t) := by
  funext t
  simp [arc, polarField]

/-- Differentiating the actual source polar field gives constant tangential
speed `|θ|`, independently of the cone's radial coefficient. -/
theorem speed_arc (hbar coupling θ t : ℝ) :
    ConeSpeed.speed hbar coupling (arc θ t) (deriv (arc θ) t) = |θ| := by
  rw [arc_eq_polarField]
  have hΦ : DifferentiableAt ℝ (fun u : ℝ => θ * u) t := by fun_prop
  rw [ConeSpeed.speed_deriv_polarField hbar coupling
    (differentiableAt_const 1) hΦ (by norm_num)]
  simp [ConeSpeed.sourceSpeed, Real.sqrt_sq_eq_abs]

/-- The differentiated actual arc speed is integrable on the closed interval. -/
theorem integrableOn_speed_arc (hbar coupling θ : ℝ) :
    IntegrableOn (fun t => ConeSpeed.speed hbar coupling (arc θ t)
      (deriv (arc θ) t)) (Icc (0 : ℝ) 1) :=
  ConeSpeed.integrableOn_curveSpeed hbar coupling
    (fun _ _ => (contDiff_arc θ 1).contDiffAt) (fun t _ => arc_ne_zero θ t)

/-- The ordinary integral of actual arc speed is its angle magnitude. -/
theorem integral_speed_arc (hbar coupling θ : ℝ) :
    (∫ t in Icc (0 : ℝ) 1, ConeSpeed.speed hbar coupling (arc θ t)
      (deriv (arc θ) t)) = |θ| := by
  simp only [speed_arc]
  simp

/-- The actual extended curve length of the short arc is exactly `|θ|`. -/
theorem curveELength_arc (hbar coupling θ : ℝ) :
    ConeSpeed.curveELength hbar coupling (arc θ) = ENNReal.ofReal |θ| := by
  rw [ConeSpeed.curveELength_eq_integral hbar coupling
    (fun _ _ => (contDiff_arc θ 1).contDiffAt) (fun t _ => arc_ne_zero θ t),
    integral_speed_arc]

/-- The physical unit circle lies in the original punctured cone. -/
def circlePoint (hbar coupling θ : ℝ) : Point hbar coupling :=
  ⟨phase θ, Complex.exp_ne_zero _⟩

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]

/-- The genuine intrinsic distance is bounded by the length of the actual
short arc, with no identification of metric and tensor speeds assumed. -/
theorem dist_circle_le_abs (θ : ℝ) :
    dist (circlePoint hbar coupling 0) (circlePoint hbar coupling θ) ≤ |θ| := by
  have h := ConeManifold.intrinsicEDist_le_curveELength
    (circlePoint hbar coupling 0) (circlePoint hbar coupling θ) (admissible_arc θ)
  rw [curveELength_arc] at h
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [dist_eq_intrinsicDist, intrinsicDist, ENNReal.toReal_ofReal (abs_nonneg θ)]
    using hreal

/-- The imaginary part of a short physical chord bounds its sine magnitude. -/
theorem abs_sin_le_chord (θ : ℝ) : |Real.sin θ| ≤ dist (phase 0) (phase θ) := by
  rw [dist_comm, dist_eq_norm]
  simpa [phase, Complex.exp_ofReal_mul_I_im] using Complex.abs_im_le_norm (phase θ - phase 0)

/-- A positive physical Euclidean chord scale for every genuine intrinsic
distance must be at most one: actual short-arc upper bounds and the derivative
limit of sine establish this necessary constraint. -/
theorem scale_le_one_of_dist_eq (a : ℝ) (ha : 0 < a)
    (hdist : ∀ p q : Point hbar coupling, dist p q = a * dist p.value q.value) : a ≤ 1 := by
  have hsin (θ : ℝ) : a * |Real.sin θ| ≤ |θ| := by
    have hle := mul_le_mul_of_nonneg_left (abs_sin_le_chord θ) ha.le
    have hd := hdist (circlePoint hbar coupling 0) (circlePoint hbar coupling θ)
    change dist (circlePoint hbar coupling 0) (circlePoint hbar coupling θ) =
      a * dist (phase 0) (phase θ) at hd
    rw [← hd] at hle
    exact hle.trans (dist_circle_le_abs hbar coupling θ)
  have ht : Tendsto (fun θ : ℝ => a * |Real.sin θ / θ|) (𝓝[≠] 0) (𝓝 a) := by
    simpa only [abs_one, mul_one] using
      (tendsto_const_nhds.mul Real.tendsto_sin_div_nhdsNE_zero.abs :
        Tendsto (fun θ : ℝ => a * |Real.sin θ / θ|) (𝓝[≠] 0) (𝓝 (a * |(1 : ℝ)|)))
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hne : θ ≠ 0 := hθ
  rw [abs_div, ← mul_div_assoc, div_le_iff₀ (abs_pos.mpr hne), one_mul]
  exact hsin θ

end FoliationQM.ConeTangentialUpper
