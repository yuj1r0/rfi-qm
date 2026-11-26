module

public import FoliationQM.RNCNormalChart
public import FoliationQM.RNCHalfDensityJet

/-!
# Coordinate curvature of the metric Levi-Civita connection

The sign convention of v13 `lem:rnc_half_density` places the positive
derivative in the third curvature slot and contracts the first and third
slots to obtain Ricci. At the center of a radial normal chart the quadratic
Christoffel terms vanish. The cyclic identity relates the resulting Ricci
components to derivatives of the connection trace.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.RNCCoordinateCurvature

open LorentzMatrixGroup RNCCoordinateConnection RNCNormalChart

/-- The last index specifies the coordinate direction in the Christoffel derivative. -/
def dGamma (g : Covector → Mat4) (x : Covector) (r b c a : Fin 4) : ℝ :=
  fderiv ℝ (fun y => christoffel g y r b c) x (axis a)

/-- The curvature coefficient with the convention of v13. -/
def riemann (g : Covector → Mat4) (x : Covector) (r s a b : Fin 4) : ℝ :=
  dGamma g x r b s a - dGamma g x r a s b +
    ∑ l, (christoffel g x r a l * christoffel g x l b s -
      christoffel g x r b l * christoffel g x l a s)

/-- The contraction of the output index with the first curvature direction. -/
def ricci (g : Covector → Mat4) (x : Covector) : Mat4 :=
  fun s b => ∑ r, riemann g x r s r b

/-- The scalar curvature obtained by contracting Ricci with the inverse metric. -/
def scalar (g : Covector → Mat4) (x : Covector) : ℝ :=
  ∑ i, ∑ j, (g x)⁻¹ i j * ricci g x i j

/-- The derivative in the first direction of the Christoffel trace in the second. -/
def traceGamma (g : Covector → Mat4) (x : Covector) (a b : Fin 4) : ℝ :=
  ∑ i, dGamma g x i b i a

variable {g : Covector → Mat4}

/-- Torsion symmetry persists after differentiating either Christoffel coefficient. -/
theorem dGamma_symmetric (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (r b c a : Fin 4) :
    dGamma g 0 r b c a = dGamma g 0 r c b a :=
  congrArg (fun L : Covector →L[ℝ] ℝ => L (axis a)) (symmetry_germ h hg r b c).fderiv_eq

/-- Only the difference of the Christoffel derivatives contributes at the normal center. -/
theorem riemann_center (h : IsNormal g) (hg : DifferentiableAt ℝ g 0) (r s a b : Fin 4) :
    riemann g 0 r s a b = dGamma g 0 r b s a - dGamma g 0 r a s b := by
  simp [riemann, connection_zero h hg]

/-- The normal-coordinate cyclic identity evaluates the Ricci tensor in terms of
two ordered derivatives of the connection trace. -/
theorem ricci_center (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (a b : Fin 4) :
    ricci g 0 a b = -traceGamma g 0 a b - 2 * traceGamma g 0 b a := by
  have hr (r : Fin 4) :
      riemann g 0 r a r b = -dGamma g 0 r b r a - 2 * dGamma g 0 r a r b := by
    have hc : dGamma g 0 r b a r + dGamma g 0 r a r b + dGamma g 0 r r b a = 0 :=
      connection_cyclic h hg r r b a
    rw [dGamma_symmetric h hg r r b a] at hc
    rw [riemann_center h (hg.differentiableAt (by decide)), dGamma_symmetric h hg r r a b]
    linarith
  simp only [ricci, hr, traceGamma, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]

/-- At the orthonormal center the inverse-metric contraction has signature (+---). -/
theorem scalar_center (h : IsNormal g) :
    scalar g 0 = RNCHalfDensityJet.scalarCurvature (ricci g 0) := by
  rw [scalar, h.metric_center, Matrix.inv_eq_left_inv eta_sq]
  simp [eta, Matrix.diagonal, Fin.sum_univ_succ, RealLorentzFrame.sign,
    RNCHalfDensityJet.scalarCurvature]
  ring

end FoliationQM.RNCCoordinateCurvature
