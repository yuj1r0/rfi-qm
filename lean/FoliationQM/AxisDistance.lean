module

public import FoliationQM.DistanceCutoffEnergy
public import FoliationQM.AxisymmetricReduction

/-!
# The radial variable of the vortex core as the distance to the nodal axis

Source: v13 `thm:wallstrom` Part(b), "`R(r) = c_n r^{|n|}(1 + O(r²))` as
`r = dist_h(x, 𝒩) → 0`", component kind B. For the nodal axis
`𝒩 = {x₂ = x₃ = 0}` in the four real coordinates and the Euclidean auxiliary
metric, the distance from a point to `𝒩` is `√(x₂² + x₃²)`, the radial
variable of the axisymmetric reduction. Hence the axisymmetric field
`(x₂ + i x₃)ⁿ R(r)/rⁿ` has modulus `|R(dist(x, 𝒩))|` off the axis, and it
solves the transverse equation at a point exactly when `R` solves the radial
equation at the distance of that point from `𝒩`.

This identifies the radial variable with a distance for the flat axis and the
Euclidean metric only. For a general auxiliary metric and a curved nodal
surface the radial equation itself is an assumption of the source ("a
separated axisymmetric vortex core"); no reduction to it is claimed there.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.AxisDistance

open Set Complex RealLorentzFrame DistanceCutoffEnergy ProductTubeCoordinates AxisymmetricReduction

/-- The nodal axis in the four real coordinates. -/
def nodalAxis : Set Covector := {z | z 2 = 0 ∧ z 3 = 0}

/-- The Euclidean distance from a point to a point of the axis. -/
theorem euclideanDist_axis (x : Covector) {z : Covector} (hz : z ∈ nodalAxis) :
    euclideanDist x z = √((x 0 - z 0) ^ 2 + (x 1 - z 1) ^ 2 + (x 2 ^ 2 + x 3 ^ 2)) := by
  rw [euclideanDist, coordinates_apply, WithLp.prod_norm_eq_of_L2]
  simp only [Pi.sub_apply, hz.1, hz.2, sub_zero]
  change √(‖((x 0 - z 0 : ℝ) : ℂ) + ((x 1 - z 1 : ℝ) : ℂ) * I‖ ^ 2 +
    ‖((x 2 : ℝ) : ℂ) + ((x 3 : ℝ) : ℂ) * I‖ ^ 2) = _
  rw [Complex.norm_add_mul_I, Complex.norm_add_mul_I, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]

/-- The Euclidean distance to the nodal axis is the radial variable
`√(x₂² + x₃²)`. -/
theorem distanceTo_axis (x : Covector) :
    distanceTo euclideanDist nodalAxis x = √(x 2 ^ 2 + x 3 ^ 2) := by
  have hbdd : BddBelow (range fun z : nodalAxis => euclideanDist x z) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩
  have hz₀ : (![x 0, x 1, 0, 0] : Covector) ∈ nodalAxis := ⟨rfl, rfl⟩
  have : Nonempty nodalAxis := ⟨⟨_, hz₀⟩⟩
  refine le_antisymm ?_ (le_ciInf fun z => ?_)
  · refine (ciInf_le hbdd ⟨_, hz₀⟩).trans (le_of_eq ?_)
    rw [euclideanDist_axis x hz₀]
    simp
  · rw [euclideanDist_axis x z.property]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x 0 - z.1 0), sq_nonneg (x 1 - z.1 1)])

variable {n : ℕ} {R R' R'' : ℝ → ℝ} {r₀ : ℝ}

/-- Off the axis, the modulus of the axisymmetric field is `|R|` at the
distance to the nodal axis. -/
theorem norm_axisymmetric_dist {x : Covector} (hx : 0 < distanceTo euclideanDist nodalAxis x) :
    ‖axisymmetric n R (x 2) (x 3)‖ = |R (distanceTo euclideanDist nodalAxis x)| := by
  rw [distanceTo_axis] at hx ⊢
  exact norm_axisymmetric hx

/-- The axisymmetric field solves the transverse equation at a point exactly
when `R` solves the radial equation at the distance of the point from the
nodal axis. -/
theorem axisymmetric_solves_iff_dist (hn : n ≠ 0) (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r) {x : Covector}
    (hr : distanceTo euclideanDist nodalAxis x ∈ Ioo 0 r₀) (β : ℝ) :
    deriv (fun u => deriv (fun u' => axisymmetric n R u' (x 3)) u) (x 2) +
        deriv (fun v => deriv (fun v' => axisymmetric n R (x 2) v') v) (x 3) =
      (β : ℂ) * axisymmetric n R (x 2) (x 3) ↔
    radialOperator n R R' R'' (distanceTo euclideanDist nodalAxis x) =
      β * R (distanceTo euclideanDist nodalAxis x) := by
  rw [distanceTo_axis] at hr ⊢
  exact axisymmetric_solves_iff hn hR hR' hr β

end FoliationQM.AxisDistance
