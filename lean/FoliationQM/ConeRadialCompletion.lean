module

public import FoliationQM.ConeRadial
public import FoliationQM.ConeCompletion
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exact radial distance and spheres in the genuine cone completion

Sources: v13 `lem:uniqueness` and `eq:cone_angle`. Radial approximants are
actual points of the punctured cone and converge to its already constructed
completion tip. Exact same-ray distances therefore determine distance to the
tip, first on original points and then on the entire completion by density.
Every positive-radius metric sphere is parameterized homeomorphically by the
physical phase circle. No assumption about Euclidean smoothness at the tip is
used in these statements.
-/
@[expose] public section

noncomputable section

namespace FoliationQM.ConeRadialCompletion

open ConeRadial ConeCompletion UniformSpace Filter Topology Set

variable (hbar coupling : ℝ) [Fact (0 < hbar)] [Fact (0 < coupling)]

/-- Positive radial approximants of an original point, with amplitude scaled
by `1/(n+1)` and physical phase unchanged. -/
def radialApproximation (p : ConeManifold.Point hbar coupling) (n : ℕ) :
    ConeManifold.Point hbar coupling where
  value := ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * p.value
  value_ne_zero := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity : 0 < 1 / ((n : ℝ) + 1))))
    p.value_ne_zero

omit [Fact (0 < hbar)] [Fact (0 < coupling)] in
/-- The approximant's actual physical coordinate has its prescribed radius. -/
theorem radialApproximation_value (p : ConeManifold.Point hbar coupling) (n : ℕ) :
    (radialApproximation hbar coupling p n).value =
      ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * p.value := rfl

/-- The positive radial approximants converge to the unique genuine completion tip. -/
theorem radialApproximation_tendsto_tip (p : ConeManifold.Point hbar coupling) :
    Tendsto (fun n : ℕ =>
      (radialApproximation hbar coupling p n : Completed hbar coupling))
      atTop (𝓝 (tip hbar coupling)) := by
  have hs : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hv : Tendsto (fun n => (radialApproximation hbar coupling p n).value)
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [radialApproximation_value, Complex.ofReal_zero, zero_mul] using!
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hs).mul_const p.value
  apply (complexHomeomorph hbar coupling).isEmbedding.tendsto_nhds_iff.mpr
  change Tendsto (fun n => coordinate hbar coupling
    (radialApproximation hbar coupling p n : Completed hbar coupling)) atTop
    (𝓝 (coordinate hbar coupling (tip hbar coupling)))
  simpa only [coordinate_coe, coordinate_tip] using hv

/-- Exact same-ray distances and the radial limit give the exact tip distance
of every original punctured-cone point. -/
theorem dist_coe_tip (p : ConeManifold.Point hbar coupling) :
    dist (p : Completed hbar coupling) (tip hbar coupling) =
      radialScale hbar coupling * ‖p.value‖ := by
  have hs : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hd : Tendsto (fun n : ℕ => dist (p : Completed hbar coupling)
      (radialApproximation hbar coupling p n : Completed hbar coupling)) atTop
      (𝓝 (dist (p : Completed hbar coupling) (tip hbar coupling))) :=
    tendsto_const_nhds.dist (radialApproximation_tendsto_tip hbar coupling p)
  have he (n : ℕ) : dist (p : Completed hbar coupling)
      (radialApproximation hbar coupling p n : Completed hbar coupling) =
        radialScale hbar coupling * |1 - 1 / ((n : ℝ) + 1)| * ‖p.value‖ := by
    rw [Completion.dist_eq]
    exact dist_smul hbar coupling p (radialApproximation hbar coupling p n)
      (1 / ((n : ℝ) + 1)) (by positivity) rfl
  have hr : Tendsto (fun n : ℕ =>
      radialScale hbar coupling * |1 - 1 / ((n : ℝ) + 1)| * ‖p.value‖)
      atTop (𝓝 (radialScale hbar coupling * ‖p.value‖)) := by
    simpa only [sub_zero, abs_one, mul_one] using
      ((tendsto_const_nhds (x := radialScale hbar coupling)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hs).abs).mul_const ‖p.value‖
  simp_rw [he] at hd
  exact tendsto_nhds_unique hd hr

/-- On the entire genuine completion, radial distance is exactly the source
radial scale times physical amplitude. -/
theorem dist_tip (x : Completed hbar coupling) :
    dist x (tip hbar coupling) = radialScale hbar coupling * ‖coordinate hbar coupling x‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (continuous_id.dist continuous_const)
      (continuous_const.mul (coordinate_lipschitz hbar coupling).continuous.norm)
  · intro p
    rw [coordinate_coe]
    exact dist_coe_tip hbar coupling p

/-- A metric sphere about the completed tip is exactly a physical-amplitude
circle of radius `r / radialScale`, for every real radius. -/
theorem mem_sphere_tip_iff (r : ℝ) (x : Completed hbar coupling) :
    x ∈ Metric.sphere (tip hbar coupling) r ↔
      ‖coordinate hbar coupling x‖ = r / radialScale hbar coupling := by
  rw [Metric.mem_sphere, dist_tip,
    eq_div_iff (ne_of_gt (radialScale_pos hbar coupling Fact.out Fact.out))]
  rw [mul_comm (radialScale hbar coupling)]

/-- The closed metric ball is exactly the corresponding closed physical-amplitude disk. -/
theorem mem_closedBall_tip_iff (r : ℝ) (x : Completed hbar coupling) :
    x ∈ Metric.closedBall (tip hbar coupling) r ↔
      ‖coordinate hbar coupling x‖ ≤ r / radialScale hbar coupling := by
  rw [Metric.mem_closedBall, dist_tip,
    le_div_iff₀ (radialScale_pos hbar coupling Fact.out Fact.out)]
  rw [mul_comm (radialScale hbar coupling)]

/-- The open metric ball is exactly the corresponding open physical-amplitude disk. -/
theorem mem_ball_tip_iff (r : ℝ) (x : Completed hbar coupling) :
    x ∈ Metric.ball (tip hbar coupling) r ↔
      ‖coordinate hbar coupling x‖ < r / radialScale hbar coupling := by
  rw [Metric.mem_ball, dist_tip,
    lt_div_iff₀ (radialScale_pos hbar coupling Fact.out Fact.out)]
  rw [mul_comm (radialScale hbar coupling)]

/-- Every point on a tip-centered metric sphere has the exact physical density
determined by its intrinsic radius. -/
theorem density_of_mem_sphere {r : ℝ} {x : Completed hbar coupling}
    (hx : x ∈ Metric.sphere (tip hbar coupling) r) :
    density hbar coupling x = (r / radialScale hbar coupling) ^ 2 := by
  rw [density_eq_norm_sq, (mem_sphere_tip_iff hbar coupling r x).1 hx]

/-- Each positive-radius metric sphere is homeomorphic to the physical phase
circle, via scaling in the proved completed coordinate homeomorphism. -/
def sphereHomeomorph (r : ℝ) (hr : 0 < r) :
    Circle ≃ₜ Metric.sphere (tip hbar coupling) r := by
  let a := r / radialScale hbar coupling
  have ha : 0 < a := div_pos hr (radialScale_pos hbar coupling Fact.out Fact.out)
  let h : ℂ ≃ₜ Completed hbar coupling :=
    (Homeomorph.smulOfNeZero a ha.ne' : ℂ ≃ₜ ℂ).trans
      (complexHomeomorph hbar coupling).symm
  change (Metric.sphere (0 : ℂ) 1) ≃ₜ Metric.sphere (tip hbar coupling) r
  refine h.subtype (fun z => ?_)
  rw [mem_sphere_zero_iff_norm, mem_sphere_tip_iff]
  change ‖z‖ = 1 ↔ ‖coordinate hbar coupling (h z)‖ = a
  have hz : coordinate hbar coupling (h z) = a • z :=
    (complexHomeomorph hbar coupling).apply_symm_apply _
  rw [hz]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  constructor
  · intro hz
    rw [hz, mul_one]
  · intro hz
    apply mul_left_cancel₀ ha.ne'
    simpa only [mul_one] using hz

/-- The metric-sphere parameterization keeps the actual physical phase and
has amplitude equal to intrinsic radius divided by the source radial scale. -/
theorem sphereHomeomorph_coordinate (r : ℝ) (hr : 0 < r) (q : Circle) :
    coordinate hbar coupling (sphereHomeomorph hbar coupling r hr q) =
      (r / radialScale hbar coupling) • (q : ℂ) := by
  change (complexHomeomorph hbar coupling)
      ((complexHomeomorph hbar coupling).symm
        ((r / radialScale hbar coupling) • (q : ℂ))) = _
  exact (complexHomeomorph hbar coupling).apply_symm_apply _

end FoliationQM.ConeRadialCompletion
