module

public import FoliationQM.RNCDeterminantDifferential
public import FoliationQM.RNCCriticalComposition
public import FoliationQM.RNCHalfDensityJet
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# The geometric coefficient and the dimension-dependent conformal coefficient

For v13 `rem:dimension_check_xi`, the fourth root of the absolute
determinant contributes a factor of one quarter for every matrix size
and either determinant sign. The normal-coordinate Ricci trace law
contributes the factor −2/3. In general dimension that trace law is an
explicit geometric hypothesis below. Its four-dimensional derivation
from radial geodesics is given in the normal-chart curvature modules.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.RNCDimensionCoupling

open RNCDeterminantDifferential RNCCriticalComposition RNCHalfDensityJet

variable {n : ℕ}

/-- Differentiation of the absolute determinant on either nonsingular component. -/
theorem fderiv_abs_det (G H : Matrix (Fin n) (Fin n) ℝ) (hG : G.det ≠ 0) :
    fderiv ℝ (fun M : Matrix (Fin n) (Fin n) ℝ => |M.det|) G H =
      |G.det| * (G⁻¹ * H).trace := by
  have hd := ((contDiff_det (Fin n) 1).differentiable_one (x := G)).hasFDerivAt
  obtain hn | hp := hG.lt_or_gt
  · calc
      _ = -(fderiv ℝ Matrix.det G H) :=
        congrArg (fun L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ => L H) (hd.abs_of_neg hn).fderiv
      _ = _ := by rw [fderiv_det_apply G H (isUnit_iff_ne_zero.mpr hG), abs_of_neg hn, neg_mul]
  · calc
      _ = fderiv ℝ Matrix.det G H :=
        congrArg (fun L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ => L H) (hd.abs_of_pos hp).fderiv
      _ = _ := by rw [fderiv_det_apply G H (isUnit_iff_ne_zero.mpr hG), abs_of_pos hp]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {g : E → Matrix (Fin n) (Fin n) ℝ} {x : E}

/-- At a critical metric of unit absolute determinant the Hessian of its
actual half-density is one quarter of the inverse-metric trace of its Hessian. -/
theorem determinant_weight_hessian (hg : ContDiffAt ℝ 2 g x)
    (hvol : |(g x).det| = 1) (hcrit : fderiv ℝ g x = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun z => |(g z).det| ^ (1 / 4 : ℝ))) x u v =
      ((g x)⁻¹ * fderiv ℝ (fderiv ℝ g) x u v).trace / 4 := by
  have hn : (g x).det ≠ 0 := by
    intro hz
    simp [hz] at hvol
  let d := fun M : Matrix (Fin n) (Fin n) ℝ => |M.det|
  have hd : ContDiffAt ℝ 2 d (g x) := (contDiff_det (Fin n) 2).contDiffAt.abs hn
  have hz := gradient_comp_critical (hg.differentiableAt (by decide))
    (hd.differentiableAt (by decide)) hcrit
  change fderiv ℝ (fderiv ℝ (fun z => (d ∘ g) z ^ (1 / 4 : ℝ))) x u v = _
  rw [fourth_root_hessian_at_one (hd.comp x hg) hvol hz, hessian_comp_critical hg hd hcrit]
  change fderiv ℝ (fun M : Matrix (Fin n) (Fin n) ℝ => |M.det|) (g x) _ / 4 = _
  rw [fderiv_abs_det _ _ hn, hvol, one_mul]
  rfl

/-- In every dimension the contraction of the differentiated RNC quadratic
half-density model is minus one sixth of the same contraction of Ricci. -/
theorem contracted_model (Q Ric : Matrix (Fin n) (Fin n) ℝ) (hs : Ric.IsSymm) :
    (∑ i, ∑ j, Q i j * fderiv ℝ (fderiv ℝ (weight Ric)) 0 (Pi.single i 1) (Pi.single j 1)) =
      -(∑ i, ∑ j, Q i j * Ric i j) / 6 :=
  contracted_hessian Q Ric (fun i j => (hs.apply i j).symm)

/-- The arbitrary-dimensional RNC metric trace law gives the same coefficient
for the actual determinant weight as for its quadratic half-density model. -/
theorem contracted_determinant_weight {g : Coordinates n → Matrix (Fin n) (Fin n) ℝ}
    (hg : ContDiffAt ℝ 2 g 0) (hvol : |(g 0).det| = 1) (hcrit : fderiv ℝ g 0 = 0)
    (Ric : Matrix (Fin n) (Fin n) ℝ)
    (hRic : ∀ i j, ((g 0)⁻¹ *
      fderiv ℝ (fderiv ℝ g) 0 (Pi.single i 1) (Pi.single j 1)).trace = -(2 / 3 : ℝ) * Ric i j) :
    (∑ i, ∑ j, (g 0)⁻¹ i j * fderiv ℝ (fderiv ℝ (fun z => |(g z).det| ^ (1 / 4 : ℝ)))
        0 (Pi.single i 1) (Pi.single j 1)) = -(∑ i, ∑ j, (g 0)⁻¹ i j * Ric i j) / 6 := by
  have he (i j : Fin n) :
      fderiv ℝ (fderiv ℝ (fun z => |(g z).det| ^ (1 / 4 : ℝ))) 0 (Pi.single i 1)
        (Pi.single j 1) = -(Ric i j) / 6 := by
    rw [determinant_weight_hessian hg hvol hcrit, hRic]
    ring
  simp only [he]
  simp only [div_eq_mul_inv, neg_mul, mul_neg, ← mul_assoc, ← Finset.sum_mul,
    Finset.sum_neg_distrib]

/-- The conformal scalar coupling in spacetime dimension `n ≥ 2`. -/
def conformalCoupling (n : ℕ) : ℝ := (n - 2 : ℝ) / (4 * (n - 1))

/-- Among dimensions at least two the conformal and DeWitt coefficients agree exactly in four. -/
theorem conformal_eq_geometric_iff (n : ℕ) (hn : 2 ≤ n) :
    conformalCoupling n = 1 / 6 ↔ n = 4 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 4 * ((n : ℝ) - 1) ≠ 0 := by linarith
  constructor
  · intro h
    rw [conformalCoupling, div_eq_div_iff hden (by norm_num)] at h
    have he : (n : ℝ) = 4 := by linarith
    exact_mod_cast he
  · rintro rfl
    norm_num [conformalCoupling]

/-- The two-dimensional conformal coefficient vanishes. -/
theorem conformal_two : conformalCoupling 2 = 0 := by norm_num [conformalCoupling]

/-- The three-dimensional conformal coefficient is one eighth. -/
theorem conformal_three : conformalCoupling 3 = 1 / 8 := by norm_num [conformalCoupling]

/-- The four-dimensional conformal coefficient is one sixth. -/
theorem conformal_four : conformalCoupling 4 = 1 / 6 := by norm_num [conformalCoupling]

end FoliationQM.RNCDimensionCoupling
