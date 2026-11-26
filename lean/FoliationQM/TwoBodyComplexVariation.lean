module

public import FoliationQM.TwoBodyActions
public import FoliationQM.TwoBodySchrodingerResidual

/-!
# Compact first variation of the two-particle Schrödinger action

The actual relative action along a real affine line of complex waves is a
quadratic polynomial. Integration by parts transfers the test derivatives
in its linear coefficient onto the wave, yielding the real pairing with
twice the Schrödinger residual in v13 `eq:2p_schrodinger`.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyComplexVariation

open MeasureTheory TwoBodyCoordinates TwoBodyActionDensity TwoBodyActions TwoBodySchrodingerResidual
open scoped BigOperators ComplexConjugate

/-- A real variation parameter multiplying an arbitrary complex test wave. -/
def variation (s : ℝ) (ψ η : Point → ℂ) (p : Point) : ℂ := ψ p + (s : ℂ) * η p

private abbrev weight (h m₁ m₂ : ℝ) (j : Index) : ℝ := h^2 / (2 * mass m₁ m₂ j)

/-- The linear coefficient in the pointwise density change, before integration by parts. -/
def linearDensity (h m₁ m₂ : ℝ) (V : Point → ℝ) (ψ η : Point → ℂ) (p : Point) : ℝ :=
  h * (star (Dt η p) * ψ p).im - h * (star (η p) * Dt ψ p).im -
    (∑ j, 2 * (h^2 / (2 * mass m₁ m₂ j)) * (star (D (axis j) η p) * D (axis j) ψ p).re) -
    2 * (V p * (star (η p) * ψ p).re)

private theorem D_variation (s : ℝ) {ψ η : Point → ℂ} {p : Point} (v : Point)
    (hψ : DifferentiableAt ℝ ψ p) (hη : DifferentiableAt ℝ η p) :
    D v (variation s ψ η) p = D v ψ p + (s : ℂ) * D v η p := by
  have hd := hψ.hasFDerivAt.add (hη.hasFDerivAt.const_mul (s : ℂ))
  change HasFDerivAt (variation s ψ η) _ p at hd
  rw [D, hd.fderiv]
  rfl

private theorem norm_line (s : ℝ) (z w : ℂ) :
    ‖z + (s : ℂ) * w‖ ^ 2 = ‖z‖ ^ 2 + s * (2 * (star w * z).re) + s^2 * ‖w‖^2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem time_line (s : ℝ) (z w t u : ℂ) :
    (star (z + (s : ℂ) * w) * (t + (s : ℂ) * u)).im = (star z * t).im +
      s * ((star w * t).im - (star u * z).im) + s ^ 2 * (star w * u).im := by
  simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.add_im, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The exact pointwise action change has just a linear and a quadratic term. -/
theorem density_expansion (h m₁ m₂ : ℝ) (V : Point → ℝ) {ψ η : Point → ℂ} {p : Point}
    (hψ : DifferentiableAt ℝ ψ p) (hη : DifferentiableAt ℝ η p) (s : ℝ) :
    complexL h m₁ m₂ V (variation s ψ η) p - complexL h m₁ m₂ V ψ p =
      s * linearDensity h m₁ m₂ V ψ η p + s^2 * complexL h m₁ m₂ V η p := by
  have hk :
      (∑ j, weight h m₁ m₂ j * ‖D (axis j) (variation s ψ η) p‖^2) =
      (∑ j, weight h m₁ m₂ j * ‖D (axis j) ψ p‖^2) +
      s * (∑ j, 2 * weight h m₁ m₂ j * (star (D (axis j) η p) * D (axis j) ψ p).re) +
      s^2 * ∑ j, weight h m₁ m₂ j * ‖D (axis j) η p‖^2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [D_variation s _ hψ hη, norm_line]
    ring
  unfold complexL linearDensity Dt
  rw [hk, D_variation s _ hψ hη]
  unfold variation
  rw [time_line, norm_line]
  ring

private theorem continuous_D {f : Point → ℂ} (hf : ContDiff ℝ 1 f) (v : Point) :
    Continuous (D v f) := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

private theorem contDiff_D {f : Point → ℂ} (hf : ContDiff ℝ 2 f) (v : Point) :
    ContDiff ℝ 1 (D v f) := (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

private theorem pair_int {f g : Point → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hc : HasCompactSupport f) : Integrable (fun p => star (f p) * g p) := by
  have hs : HasCompactSupport (fun p => star (f p)) := hc.comp_left (star_zero ℂ)
  exact (hf.star.mul hg).integrable_of_hasCompactSupport hs.mul_right

private theorem potential_int {V : Point → ℝ} {ψ η : Point → ℂ}
    (hV : Continuous V) (hψ : Continuous ψ) (hη : Continuous η) (hc : HasCompactSupport η) :
    Integrable (fun p => V p * (star (η p) * ψ p).re) := by
  have hs : HasCompactSupport (fun p => star (η p)) := hc.comp_left (star_zero ℂ)
  have hp : HasCompactSupport (fun p => star (η p) * ψ p) := hs.mul_right
  have hre : HasCompactSupport (fun p => (star (η p) * ψ p).re) := hp.comp_left Complex.zero_re
  exact (hV.mul (Complex.continuous_re.comp (hη.star.mul hψ))).integrable_of_hasCompactSupport
    hre.mul_left

private theorem pair_parts {η g : Point → ℂ} (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hg : ContDiff ℝ 1 g) (v : Point) :
    (∫ p, star (D v η p) * g p) = -(∫ p, star (η p) * D v g p) := by
  let := TwoBodyPolarContinuity.volume_isAddHaarMeasure
  have hconj (p : Point) : fderiv ℝ (fun q => star (η q)) p v = star (D v η p) :=
    ActionDensity.fderiv_conj_apply (hη.differentiable (by norm_num) p) v
  have hi : Integrable (fun p => fderiv ℝ (fun q => star (η q)) p v * g p) := by
    simp_rw [hconj]
    exact pair_int (continuous_D hη v) hg.continuous (hc.fderiv_apply ℝ v)
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi
    (pair_int hη.continuous (continuous_D hg v) hc)
    (pair_int hη.continuous hg.continuous hc)
    (fun p _ => (Complex.conjCLE.toContinuousLinearMap.contDiff.comp hη).differentiable (by norm_num) p)
    (fun p _ => hg.differentiable (by norm_num) p)
  simp_rw [hconj] at he
  exact (neg_neg _).symm.trans (congrArg Neg.neg he.symm)

/-- The linear pointwise variation is absolutely integrable even for a wave
whose absolute action over spacetime is infinite. -/
theorem integrable_linear (h m₁ m₂ : ℝ) {V : Point → ℝ} {ψ η : Point → ℂ} (hV : Continuous V)
    (hψ : ContDiff ℝ 1 ψ) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    Integrable (linearDensity h m₁ m₂ V ψ η) := by
  have ht := (pair_int (continuous_D hη timeAxis) hψ.continuous
    (hc.fderiv_apply ℝ timeAxis)).im.const_mul h
  have hs := (pair_int hη.continuous (continuous_D hψ timeAxis) hc).im.const_mul h
  have hk := integrable_finsetSum Finset.univ fun j _ => (pair_int (continuous_D hη (axis j))
    (continuous_D hψ (axis j)) (hc.fderiv_apply ℝ (axis j))).re.const_mul (2 * weight h m₁ m₂ j)
  exact (((ht.sub hs).sub hk).sub ((potential_int hV hψ.continuous hη.continuous hc).const_mul 2))

/-- The quadratic coefficient of a compact test is absolutely integrable. -/
theorem integrable_quadratic (h m₁ m₂ : ℝ) {V : Point → ℝ} {η : Point → ℂ}
    (hV : Continuous V) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    Integrable (complexL h m₁ m₂ V η) := by
  have hcont : Continuous (complexL h m₁ m₂ V η) := by
    have ht := (continuous_const (y := -h)).mul (Complex.continuous_im.comp
      (hη.continuous.star.mul (continuous_D hη timeAxis)))
    exact (ht.sub (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_D hη (axis j)).norm.pow 2))).sub
        (hV.mul (hη.continuous.norm.pow 2))
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro' hc (isClosed_tsupport η)
  intro p hp
  have hz (v : Point) : D v η p = 0 := by rw [D, fderiv_of_notMem_tsupport ℝ hp]; rfl
  simp [complexL, hz, image_eq_zero_of_notMem_tsupport hp]

/-- The relative spacetime action of the actual perturbed wave is an exact quadratic polynomial. -/
theorem relative_polynomial (h m₁ m₂ : ℝ) {V : Point → ℝ} {ψ η : Point → ℂ}
    (hV : Continuous V) (hψ : ContDiff ℝ 1 ψ) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (s : ℝ) : relative (complexL h m₁ m₂ V ψ) (complexL h m₁ m₂ V (variation s ψ η)) =
      s * (∫ p, linearDensity h m₁ m₂ V ψ η p) + s^2 * ∫ p, complexL h m₁ m₂ V η p := by
  unfold relative
  simp_rw [fun p => density_expansion h m₁ m₂ V (hψ.differentiable (by norm_num) p)
    (hη.differentiable (by norm_num) p) s]
  rw [integral_add ((integrable_linear h m₁ m₂ hV hψ hη hc).const_mul s)
    ((integrable_quadratic h m₁ m₂ hV hη hc).const_mul (s^2)), integral_const_mul, integral_const_mul]

/-- Every finite relative variation has an integrable density change. -/
theorem integrable_difference (h m₁ m₂ : ℝ) {V : Point → ℝ} {ψ η : Point → ℂ}
    (hV : Continuous V) (hψ : ContDiff ℝ 1 ψ) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (s : ℝ) : Integrable (fun p => complexL h m₁ m₂ V (variation s ψ η) p -
      complexL h m₁ m₂ V ψ p) := by
  simp_rw [fun p => density_expansion h m₁ m₂ V (hψ.differentiable (by norm_num) p)
    (hη.differentiable (by norm_num) p) s]
  exact ((integrable_linear h m₁ m₂ hV hψ hη hc).const_mul s).add
    ((integrable_quadratic h m₁ m₂ hV hη hc).const_mul (s^2))

private theorem pair_parts_observed (L : ℂ →L[ℝ] ℝ) {η g : Point → ℂ}
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (hg : ContDiff ℝ 1 g) (v : Point) :
    (∫ p, L (star (D v η p) * g p)) = -(∫ p, L (star (η p) * D v g p)) := by
  rw [L.integral_comp_comm (pair_int (continuous_D hη v) hg.continuous (hc.fderiv_apply ℝ v)),
    L.integral_comp_comm (pair_int hη.continuous (continuous_D hg v) hc), pair_parts hη hc hg v,
    map_neg]

private theorem residual_re (h m₁ m₂ : ℝ) (V : Point → ℝ) (ψ η : Point → ℂ) (p : Point) :
    (star (η p) * schrodinger h m₁ m₂ V ψ p).re =
      (-h) * (star (η p) * Dt ψ p).im +
        (∑ j, weight h m₁ m₂ j * (star (η p) * D (axis j) (D (axis j) ψ) p).re) -
        V p * (star (η p) * ψ p).re := by
  have he : star (η p) * schrodinger h m₁ m₂ V ψ p =
      Complex.I * ((h : ℂ) * (star (η p) * Dt ψ p)) +
        (∑ j, ((weight h m₁ m₂ j : ℝ) : ℂ) * (star (η p) * D (axis j) (D (axis j) ψ) p)) -
        (V p : ℂ) * (star (η p) * ψ p) := by
    simp only [schrodinger, weight, mul_sub, mul_add, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [he]
  simp only [Complex.add_re, Complex.sub_re, Complex.I_mul_re, Complex.im_ofReal_mul,
    Complex.re_sum, Complex.re_ofReal_mul, neg_mul]

/-- Compact integration by parts transfers every first derivative of the test
onto the background wave and gives the real variational pairing. -/
theorem linear_green (h m₁ m₂ : ℝ) {V : Point → ℝ} {ψ η : Point → ℂ} (hV : Continuous V)
    (hψ : ContDiff ℝ 2 ψ) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    (∫ p, linearDensity h m₁ m₂ V ψ η p) =
      2 * ∫ p, (star (η p) * schrodinger h m₁ m₂ V ψ p).re := by
  have hψ₁ : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  let u := fun p => (star (Dt η p) * ψ p).im
  let w := fun p => (star (η p) * Dt ψ p).im
  let a := fun j p => (star (D (axis j) η p) * D (axis j) ψ p).re
  let b := fun j p => (star (η p) * D (axis j) (D (axis j) ψ) p).re
  let c := fun p => V p * (star (η p) * ψ p).re
  let k := weight h m₁ m₂
  have iu : Integrable u :=
    (pair_int (continuous_D hη timeAxis) hψ.continuous (hc.fderiv_apply ℝ timeAxis)).im
  have iw : Integrable w := (pair_int hη.continuous (continuous_D hψ₁ timeAxis) hc).im
  have ia (j) : Integrable (a j) := (pair_int (continuous_D hη (axis j))
    (continuous_D hψ₁ (axis j)) (hc.fderiv_apply ℝ (axis j))).re
  have ib (j) : Integrable (b j) := (pair_int hη.continuous
    (continuous_D (contDiff_D hψ (axis j)) (axis j)) hc).re
  have ic : Integrable c := potential_int hV hψ.continuous hη.continuous hc
  have hu : (∫ p, u p) = -(∫ p, w p) := pair_parts_observed Complex.imCLM hη hc hψ₁ timeAxis
  have hk (j) : (∫ p, a j p) = -(∫ p, b j p) :=
    pair_parts_observed Complex.reCLM hη hc (contDiff_D hψ (axis j)) (axis j)
  have iA := integrable_finsetSum Finset.univ fun j _ => (ia j).const_mul (2 * k j)
  have iB := integrable_finsetSum Finset.univ fun j _ => (ib j).const_mul (k j)
  have lhs : (∫ p, linearDensity h m₁ m₂ V ψ η p) =
      h * (∫ p, u p) - h * (∫ p, w p) - (∑ j, 2 * k j * ∫ p, a j p) - 2 * ∫ p, c p := by
    change (∫ p, (h * u p - h * w p - (∑ j, 2 * k j * a j p)) - 2 * c p) = _
    have iT : Integrable (fun p => h * u p - h * w p) := (iu.const_mul h).sub (iw.const_mul h)
    have iK : Integrable (fun p => h * u p - h * w p - ∑ j, 2*k j*a j p) := iT.sub iA
    rw [integral_sub iK (ic.const_mul 2), integral_sub iT iA,
      integral_sub (iu.const_mul h) (iw.const_mul h),
      integral_finsetSum _ (fun j _ => (ia j).const_mul (2 * k j))]
    simp only [integral_const_mul]
  have rhs : (∫ p, (star (η p) * schrodinger h m₁ m₂ V ψ p).re) =
      (-h) * (∫ p, w p) + (∑ j, k j * ∫ p, b j p) - ∫ p, c p := by
    simp_rw [residual_re]
    change (∫ p, ((-h) * w p + (∑ j, k j * b j p)) - c p) = _
    have iK : Integrable (fun p => (-h)*w p + ∑ j, k j*b j p) := (iw.const_mul (-h)).add iB
    rw [integral_sub iK ic, integral_add (iw.const_mul (-h)) iB,
      integral_finsetSum _ (fun j _ => (ib j).const_mul (k j))]
    simp only [integral_const_mul]
  have hs : (∑ j, 2 * k j * ∫ p, a j p) = -(2 * ∑ j, k j * ∫ p, b j p) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hk j]
    ring
  rw [lhs, rhs, hu, hs]
  ring

/-- The derivative of the actual relative action in an arbitrary compact
complex direction equals twice its real pairing with the Schrödinger residual. -/
theorem first_variation (h m₁ m₂ : ℝ) {V : Point → ℝ} {ψ η : Point → ℂ} (hV : Continuous V)
    (hψ : ContDiff ℝ 2 ψ) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    HasDerivAt (fun s => relative (complexL h m₁ m₂ V ψ) (complexL h m₁ m₂ V (variation s ψ η)))
      (2 * ∫ p, (star (η p) * schrodinger h m₁ m₂ V ψ p).re) 0 := by
  rw [funext (relative_polynomial h m₁ m₂ hV (hψ.of_le (by norm_num)) hη hc)]
  have he := ((hasDerivAt_id (0 : ℝ)).mul_const (∫ p, linearDensity h m₁ m₂ V ψ η p)).fun_add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (∫ p, complexL h m₁ m₂ V η p))
  rw [← linear_green h m₁ m₂ hV hψ hη hc]
  simpa using he

/-- If the background action density is integrable, the absolute quadratic
action has the same derivative on the compact variation line. -/
theorem first_variation_absolute (h m₁ m₂ : ℝ) {V : Point → ℝ} {ψ η : Point → ℂ}
    (hV : Continuous V) (hψ : ContDiff ℝ 2 ψ) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hi : Integrable (complexL h m₁ m₂ V ψ)) :
    HasDerivAt (fun s => quadraticAction h m₁ m₂ V (variation s ψ η))
      (2 * ∫ p, (star (η p) * schrodinger h m₁ m₂ V ψ p).re) 0 := by
  have he (s : ℝ) : quadraticAction h m₁ m₂ V (variation s ψ η) =
      relative (complexL h m₁ m₂ V ψ) (complexL h m₁ m₂ V (variation s ψ η)) +
        quadraticAction h m₁ m₂ V ψ := by
    have hd := integrable_difference h m₁ m₂ hV (hψ.of_le (by norm_num)) hη hc s
    have hs : Integrable (complexL h m₁ m₂ V (variation s ψ η)) := by
      apply (hd.add hi).congr
      exact .of_forall fun p => sub_add_cancel _ _
    rw [relative_eq_sub hi hs]
    unfold quadraticAction
    ring
  rw [funext he]
  exact (first_variation h m₁ m₂ hV hψ hη hc).add_const _

end FoliationQM.TwoBodyComplexVariation
