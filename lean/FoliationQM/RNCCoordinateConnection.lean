module

public import FoliationQM.RNCMetricNormalization
public import FoliationQM.LorentzCayleySmooth

/-!
# The Levi-Civita coefficients of the coordinate metric

For the normal coordinates of v13 Lemma 9.1 the connection is calculated
from the actual metric derivative. Lowering the output index recovers the
coordinate Koszul formula. Metric compatibility then turns vanishing of all
connection coefficients into vanishing of the entire first metric jet.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RNCCoordinateConnection

open LorentzMatrixGroup RealLorentzFrame Filter
open scoped Topology Matrix.Norms.Operator ContDiff

variable {g : Covector → Mat4} {x : Covector}

/-- The coordinate direction with a unit value in slot `i`. -/
def axis (i : Fin 4) : Covector := Pi.single i 1

/-- The actual directional derivative of the matrix-valued metric. -/
def dG (g : Covector → Mat4) (x v : Covector) : Mat4 := fderiv ℝ g x v

/-- The lowered coordinate Koszul expression, with the output index first. -/
def lowered (g : Covector → Mat4) (x : Covector) (a b c : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (dG g x (axis b) c a + dG g x (axis c) b a - dG g x (axis a) b c)

/-- The coordinate Christoffel coefficient obtained by raising the output index of the metric Koszul expression. -/
def christoffel (g : Covector → Mat4) (x : Covector) (r b c : Fin 4) : ℝ :=
  (g x)⁻¹.mulVec (fun k => lowered g x k b c) r

/-- The raised Christoffel coefficient is the inverse-metric sum over actual directional derivatives. -/
theorem christoffel_eq_sum (g : Covector → Mat4) (x : Covector) (r b c : Fin 4) :
    christoffel g x r b c = (1 / 2 : ℝ) * ∑ k, (g x)⁻¹ r k *
      (dG g x (axis b) c k + dG g x (axis c) b k - dG g x (axis k) b c) := by
  simp only [christoffel, Matrix.mulVec, dotProduct, lowered, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Lowering with an invertible metric recovers the unraised coordinate Koszul formula. -/
theorem lowered_eq_sum (hu : IsUnit (g x)) (a b c : Fin 4) :
    lowered g x a b c = ∑ r, g x a r * christoffel g x r b c := by
  change _ = (g x).mulVec ((g x)⁻¹.mulVec fun k => lowered g x k b c) a
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((g x).isUnit_iff_isUnit_det.mp hu),
    Matrix.one_mulVec]

/-- A symmetric metric germ has symmetric actual first variation in every direction. -/
theorem dG_isSymm (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (v : Covector) : (dG g x v).IsSymm := by
  ext i j
  let entry (a b : Fin 4) : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap
  have he : (entry j i ∘ g) =ᶠ[𝓝 x] (entry i j ∘ g) :=
    hs.mono fun _ hy => hy.apply i j
  have hv := congrArg (fun L : Covector →L[ℝ] ℝ => L v) he.fderiv_eq
  rw [((entry j i).hasFDerivAt.comp x hg.hasFDerivAt).fderiv,
    ((entry i j).hasFDerivAt.comp x hg.hasFDerivAt).fderiv] at hv
  exact hv

/-- The torsion-free symmetry exchanges the two input indices of the coordinate connection. -/
theorem christoffel_symmetric (hs : ∀ v, (dG g x v).IsSymm) (r b c : Fin 4) :
    christoffel g x r b c = christoffel g x r c b := by
  simp only [christoffel, lowered, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  rw [(hs (axis k)).apply c b, add_comm (dG g x (axis b) c k)]

/-- Metric compatibility recovers a partial metric derivative by adding two lowered coefficients. -/
theorem metric_compatibility (hu : IsUnit (g x)) (hs : ∀ v, (dG g x v).IsSymm) (a b c : Fin 4) :
    dG g x (axis a) b c = (∑ r, g x c r * christoffel g x r a b) +
      ∑ r, g x b r * christoffel g x r a c := by
  rw [← lowered_eq_sum hu, ← lowered_eq_sum hu]
  unfold lowered
  rw [(hs (axis a)).apply b c]
  ring

/-- At a Minkowskian center, a vanishing connection and a symmetric metric germ force the
whole Fréchet derivative of the metric to vanish, including arbitrary input directions. -/
theorem fderiv_eq_zero_of_christoffel_zero (hg : DifferentiableAt ℝ g x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm) (hη : g x = eta)
    (hΓ : ∀ r b c, christoffel g x r b c = 0) : fderiv ℝ g x = 0 := by
  have hu : IsUnit (g x) := (g x).isUnit_iff_isUnit_det.mpr (by simp [hη, eta_det])
  have haxes (a : Fin 4) : fderiv ℝ g x (axis a) = 0 := by
    ext b c
    simpa [dG, hΓ] using metric_compatibility hu (dG_isSymm hg hs) a b c
  ext1 v
  calc
    fderiv ℝ g x v = fderiv ℝ g x (∑ a, v a • axis a) := congrArg _ (pi_eq_sum_univ' v)
    _ = 0 := by simp only [map_sum, map_smul, haxes, smul_zero, Finset.sum_const_zero]
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every coordinate connection coefficient is locally C¹ for a locally C² metric invertible at the point. -/
theorem contDiffAt_christoffel (hg : ContDiffAt ℝ 2 g x) (hu : IsUnit (g x)) (r b c : Fin 4) :
    ContDiffAt ℝ 1 (fun y => christoffel g y r b c) x := by
  let entry (i j : Fin 4) : Mat4 →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have hi : ContDiffAt ℝ 1 (fun y => (g y)⁻¹) x :=
    (LorentzCayleySmooth.contDiffAt_inverse 1 hu).comp x (hg.of_le (by decide))
  have hd (a i j : Fin 4) : ContDiffAt ℝ 1 (fun y => dG g y (axis a) i j) x :=
    (entry i j).contDiff.contDiffAt.comp x
      ((ContinuousLinearMap.apply ℝ Mat4 (axis a)).contDiff.contDiffAt.comp x (hg.fderiv_right (by decide)))
  simp only [christoffel_eq_sum]
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro k _
  exact ((entry r k).contDiff.contDiffAt.comp x hi).mul (((hd b c k).add (hd c b k)).sub (hd k b c))

end FoliationQM.RNCCoordinateConnection
