module

public import FoliationQM.LorentzCoordinates
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Weighted spacelike coercivity

The source dilatation condition in v13 lines 762–773 compares finite
weighted square integrals. The estimate below uses the three-dimensional
Euclidean spatial metric and applies to the full spatial measure or a
restricted laboratory cell.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WeightedOsmoticCoercivity

open MeasureTheory LorentzCoordinates

/-- Euclidean Cauchy–Schwarz for the three actual spatial coordinate components. -/
theorem abs_spatialDot_le (v g : Spatial) :
    |spatialDot v g| ≤ euclideanSpeed v * euclideanSpeed g := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (speedSq_nonneg _), Real.sq_sqrt (speedSq_nonneg _)]
  simpa [spatialDot, speedSq_eq_sum, Fin.sum_univ_three] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v g

variable {α : Type*} [MeasurableSpace α]

/-- Real weighted L² norm computed from the original measure and the density weight. -/
def weightedNorm (μ : Measure α) (r f : α → ℝ) : ℝ := Real.sqrt (∫ x, r x * (f x)^2 ∂μ)

/-- For a nonnegative density the squared weighted norm recovers its square integral. -/
theorem weightedNorm_sq {μ : Measure α} {r : α → ℝ} (hr : ∀ᵐ x ∂μ, 0 ≤ r x)
    (f : α → ℝ) : weightedNorm μ r f ^ 2 = ∫ x, r x * (f x)^2 ∂μ :=
  Real.sq_sqrt (integral_nonneg_of_ae (hr.mono fun x hx => mul_nonneg hx (sq_nonneg (f x))))

variable {μ : Measure α} {c V : ℝ} {r N G D : α → ℝ}

private theorem pointwise_bound (hc : 0 < c) (hV : 0 ≤ V) (hVc : V < c)
    {n g d : ℝ} (hg : 0 ≤ g) (h : c*|n| ≤ V*g+|d|) :
    c*(c-V)*n^2 ≤ V*(c-V)*g^2+d^2 := by
  have hs := (sq_le_sq₀ (mul_nonneg hc.le (abs_nonneg n))
    (add_nonneg (mul_nonneg hV hg) (abs_nonneg d))).mpr h
  rw [mul_pow, sq_abs] at hs
  have hmul := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hVc.le)
  apply (mul_le_mul_iff_right₀ hc).mp
  rw [← sq_abs d]
  nlinarith only [hmul, mul_nonneg hV (sq_nonneg ((c-V)*g-|d|))]

private theorem domination (hc : 0 < c) (hV : 0 ≤ V) (hVc : V < c)
    (hr : ∀ᵐ x ∂μ, 0 ≤ r x) (hG : ∀ᵐ x ∂μ, 0 ≤ G x)
    (hest : ∀ᵐ x ∂μ, c*|N x| ≤ V*G x+|D x|) :
    ∀ᵐ x ∂μ, r x*(N x)^2 ≤ (c*(c-V))⁻¹ * (V*(c-V)*(r x*(G x)^2)+r x*(D x)^2) := by
  filter_upwards [hr, hG, hest] with x hx hg he
  rw [← div_eq_inv_mul, le_div_iff₀ (mul_pos hc (sub_pos.mpr hVc))]
  nlinarith only [mul_le_mul_of_nonneg_left (pointwise_bound hc hV hVc hg he) hx]

/-- The weighted square of the normal derivative is integrable by domination by
the spatial and dilatation squares, independently of the strict dilatation bound. -/
theorem integrable_normal (hc : 0 < c) (hV : 0 ≤ V) (hVc : V < c)
    (hr : ∀ᵐ x ∂μ, 0 ≤ r x) (hG : ∀ᵐ x ∂μ, 0 ≤ G x)
    (hest : ∀ᵐ x ∂μ, c*|N x| ≤ V*G x+|D x|)
    (hm : AEStronglyMeasurable (fun x => r x*(N x)^2) μ)
    (hGI : Integrable (fun x => r x*(G x)^2) μ) (hDI : Integrable (fun x => r x*(D x)^2) μ) :
    Integrable (fun x => r x*(N x)^2) μ :=
  (((hGI.const_mul (V*(c-V))).add hDI).const_mul (c*(c-V))⁻¹).mono_nonneg hm
    (hr.mono fun x hx => mul_nonneg hx (sq_nonneg (N x))) (domination hc hV hVc hr hG hest)

private theorem split_bound {L X Y a b : ℝ} (hl : 0 ≤ L) (h : L ≤ X+Y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : a*b*L^2 ≤ (a+b)*(b*X^2+a*Y^2) := by
  have hs := (sq_le_sq₀ hl (hl.trans h)).mpr h
  nlinarith only [mul_le_mul_of_nonneg_left hs (mul_nonneg ha hb), sq_nonneg (b*X-a*Y)]

/-- Weighted L² triangle estimate with the exact source coefficients. Normal,
spatial and dilatation terms may vanish on arbitrary measurable subsets. -/
theorem norm_estimate (hc : 0 < c) (hV : 0 ≤ V) (hVc : V < c)
    (hr : ∀ᵐ x ∂μ, 0 ≤ r x) (hG : ∀ᵐ x ∂μ, 0 ≤ G x)
    (hest : ∀ᵐ x ∂μ, c*|N x| ≤ V*G x+|D x|)
    (hm : AEStronglyMeasurable (fun x => r x*(N x)^2) μ)
    (hGI : Integrable (fun x => r x*(G x)^2) μ) (hDI : Integrable (fun x => r x*(D x)^2) μ) :
    c*weightedNorm μ r N ≤ V*weightedNorm μ r G+weightedNorm μ r D := by
  have hn := integrable_normal hc hV hVc hr hG hest hm hGI hDI
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let a := V * weightedNorm μ r G + ε/2
  let b := weightedNorm μ r D + ε/2
  have hvg : 0 ≤ V * weightedNorm μ r G := mul_nonneg hV (Real.sqrt_nonneg _)
  have hdn : 0 ≤ weightedNorm μ r D := Real.sqrt_nonneg _
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have he : ∀ᵐ x ∂μ, (a*b*c^2)*(r x*(N x)^2) ≤
      ((a+b)*b*V^2)*(r x*(G x)^2) + ((a+b)*a)*(r x*(D x)^2) := by
    filter_upwards [hr, hest] with x hρ hx
    have hp := split_bound (mul_nonneg hc.le (abs_nonneg (N x))) hx ha.le hb.le
    rw [mul_pow, sq_abs, mul_pow, sq_abs] at hp
    nlinarith only [mul_le_mul_of_nonneg_left hp hρ]
  have hi := integral_mono_ae (hn.const_mul (a*b*c^2))
    ((hGI.const_mul ((a+b)*b*V^2)).add (hDI.const_mul ((a+b)*a))) he
  simp only [Pi.add_apply] at hi
  rw [integral_add (hGI.const_mul _) (hDI.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, ← weightedNorm_sq hr N,
    ← weightedNorm_sq hr G, ← weightedNorm_sq hr D] at hi
  have hG' : V * weightedNorm μ r G ≤ a := by dsimp [a]; linarith
  have hD' : weightedNorm μ r D ≤ b := by dsimp [b]; linarith
  have hs : (c * weightedNorm μ r N)^2 ≤ (a+b)^2 := by
    apply (mul_le_mul_iff_right₀ (mul_pos ha hb)).mp
    nlinarith only [hi, mul_le_mul_of_nonneg_left ((sq_le_sq₀ hvg ha.le).mpr hG')
      (mul_nonneg (add_nonneg ha.le hb.le) hb.le),
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ hdn hb.le).mpr hD')
      (mul_nonneg (add_nonneg ha.le hb.le) ha.le)]
  have h : c*weightedNorm μ r N ≤ a+b := (sq_le_sq₀ (mul_nonneg hc.le (Real.sqrt_nonneg _)) (add_nonneg ha.le hb.le)).mp hs
  dsimp only [a, b] at h
  linarith

/-- The source threshold forces the true weighted integral of the normal square
minus the spatial square to be strictly negative. -/
theorem integral_neg (hc : 0 < c) (hV : 0 ≤ V) (hVc : V < c)
    (hr : ∀ᵐ x ∂μ, 0 ≤ r x) (hG : ∀ᵐ x ∂μ, 0 ≤ G x)
    (hest : ∀ᵐ x ∂μ, c*|N x| ≤ V*G x+|D x|)
    (hm : AEStronglyMeasurable (fun x => r x*(N x)^2) μ)
    (hGI : Integrable (fun x => r x*(G x)^2) μ) (hDI : Integrable (fun x => r x*(D x)^2) μ)
    (hgap : weightedNorm μ r D < (c-V)*weightedNorm μ r G) :
    (∫ x, r x*((N x)^2-(G x)^2) ∂μ) < 0 := by
  have hn := integrable_normal hc hV hVc hr hG hest hm hGI hDI
  have he := norm_estimate hc hV hVc hr hG hest hm hGI hDI
  have hlt : weightedNorm μ r N < weightedNorm μ r G := by
    apply (mul_lt_mul_iff_right₀ hc).mp
    nlinarith only [he, hgap]
  simp_rw [mul_sub]
  rw [integral_sub hn hGI, sub_neg, ← weightedNorm_sq hr N, ← weightedNorm_sq hr G]
  exact (sq_lt_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mpr hlt

end FoliationQM.WeightedOsmoticCoercivity
