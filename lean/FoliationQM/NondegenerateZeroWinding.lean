module

public import FoliationQM.TransverseZeroWinding

/-!
# Winding of a field at a non-degenerate transverse zero

Source: v13 `thm:wallstrom` Part(b), "near a generic non-degenerate smooth
transverse zero (`|A| ≠ |B|` in `ψ_⊥ = A z + B z̄ + O(|z|²)`), the winding is
`n = ±1`", component kinds B and C. Two closed curves in the plane, one of
which stays strictly closer to the other than the other is to the origin,
have the same winding integral `∮ dc/c`. A continuously differentiable field
on a disc with `|ψ(z) - (A z + B z̄)| ≤ C |z|²` and `|A| ≠ |B|` therefore does
not vanish on the punctured disc of radius `||A| - |B|| / C`, and on every
circle of smaller radius its winding integral equals that of its linear part:
`2πi` when `|A| > |B|` and `-2πi` when `|A| < |B|`. Its modulus on the circle
of radius `r` is the anisotropic profile `r |A e^{iθ} + B e^{-iθ}|` up to
`C r²`.

The field is a function of the transverse complex coordinate alone; the
dependence on the coordinates along the nodal surface is not treated, and the
radial ordinary differential equation of the axisymmetric case is not
addressed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.NondegenerateZeroWinding

open Complex MeasureTheory TransverseZeroWinding
open scoped Real ComplexConjugate

/-- Two closed curves, the second strictly closer to the first than the first
is to the origin, have the same winding integral. -/
theorem winding_eq_of_close {c₁ c₂ c₁' c₂' : ℝ → ℂ} {a b : ℝ}
    (h₁ : ∀ θ, HasDerivAt c₁ (c₁' θ) θ) (h₂ : ∀ θ, HasDerivAt c₂ (c₂' θ) θ)
    (hc₁ : Continuous c₁') (hc₂ : Continuous c₂')
    (hclose : ∀ θ, ‖c₂ θ - c₁ θ‖ < ‖c₁ θ‖) (hp₁ : c₁ b = c₁ a) (hp₂ : c₂ b = c₂ a) :
    (∫ θ in a..b, c₂' θ / c₂ θ) = ∫ θ in a..b, c₁' θ / c₁ θ := by
  have hne₁ : ∀ θ, c₁ θ ≠ 0 := fun θ h => by
    have h' := hclose θ
    rw [h, norm_zero] at h'
    exact absurd h' (not_lt.mpr (norm_nonneg _))
  have hne₂ : ∀ θ, c₂ θ ≠ 0 := fun θ h => by
    have h' := hclose θ
    rw [h, zero_sub, norm_neg] at h'
    exact lt_irrefl _ h'
  have hcont₁ : Continuous c₁ := continuous_iff_continuousAt.mpr fun θ => (h₁ θ).continuousAt
  have hcont₂ : Continuous c₂ := continuous_iff_continuousAt.mpr fun θ => (h₂ θ).continuousAt
  have hslit : ∀ θ, c₂ θ / c₁ θ ∈ slitPlane := by
    intro θ
    have e : c₂ θ / c₁ θ - 1 = (c₂ θ - c₁ θ) / c₁ θ := by
      field_simp [hne₁ θ]
    have hn : ‖c₂ θ / c₁ θ - 1‖ < 1 := by
      rw [e, norm_div, div_lt_one (norm_pos_iff.mpr (hne₁ θ))]
      exact hclose θ
    have hre := (abs_lt.mp ((abs_re_le_norm _).trans_lt hn)).1
    rw [sub_re, one_re] at hre
    exact mem_slitPlane_iff.mpr (Or.inl (by linarith))
  have hlog : ∀ θ, HasDerivAt (fun θ => log (c₂ θ / c₁ θ))
      (c₂' θ / c₂ θ - c₁' θ / c₁ θ) θ := by
    intro θ
    have hd := ((h₂ θ).fun_div (h₁ θ) (hne₁ θ)).clog_real (hslit θ)
    refine hd.congr_deriv ?_
    have := hne₁ θ
    have := hne₂ θ
    field_simp
  have hint₁ : Continuous fun θ => c₁' θ / c₁ θ := hc₁.div hcont₁ hne₁
  have hint₂ : Continuous fun θ => c₂' θ / c₂ θ := hc₂.div hcont₂ hne₂
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hlog θ)
    ((hint₂.sub hint₁).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub (hint₂.intervalIntegrable a b)
    (hint₁.intervalIntegrable a b), hp₁, hp₂, sub_self] at hftc
  exact sub_eq_zero.mp hftc

/-- The circle of radius `r` about the zero. -/
def circle (r θ : ℝ) : ℂ := r * exp (θ * I)

/-- The circle of radius `r` has modulus `r`. -/
theorem norm_circle {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖circle r θ‖ = r := by
  rw [circle, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, norm_exp_ofReal_mul_I,
    mul_one]

/-- The velocity of the circle. -/
theorem hasDerivAt_circle (r θ : ℝ) :
    HasDerivAt (circle r) (r * (exp (θ * I) * I)) θ := by
  have h := ((hasDerivAt_id' θ).ofReal_comp.mul_const I).cexp.const_mul (r : ℂ)
  refine h.congr_deriv ?_
  simp

/-- The circle is closed. -/
theorem circle_two_pi (r : ℝ) : circle r (2 * π) = circle r 0 := by
  simp only [circle]
  push_cast
  rw [exp_two_pi_mul_I]
  simp

/-- The derivative of the unit-circle value of the linear part. -/
theorem hasDerivAt_loop (A B : ℂ) (θ : ℝ) :
    HasDerivAt (loop A B) (I * (A * exp (θ * I) - B * exp (-(θ * I)))) θ := by
  have h1 := ((hasDerivAt_id' θ).ofReal_comp.mul_const I).cexp.const_mul A
  have h2 := ((hasDerivAt_id' θ).ofReal_comp.mul_const I).neg.cexp.const_mul B
  refine (h1.add h2).congr_deriv ?_
  simp only [ofReal_one, one_mul, Pi.neg_apply]
  ring

/-- The unit-circle value of the linear part is closed. -/
theorem loop_two_pi (A B : ℂ) : loop A B (2 * π) = loop A B 0 := by
  simp only [loop]
  push_cast
  rw [exp_neg, exp_two_pi_mul_I]
  simp

variable {ψ : ℂ → ℂ} {A B : ℂ} {C ρ r : ℝ}

/-- A field with non-degenerate linear part and quadratic remainder does not
vanish on a punctured disc: the zero is isolated. -/
theorem ne_zero_of_remainder
    (hrem : ∀ z, ‖z‖ < ρ → ‖ψ z - linearZero A B z‖ ≤ C * ‖z‖ ^ 2) {z : ℂ} (hz : z ≠ 0)
    (hzρ : ‖z‖ < ρ) (hsmall : C * ‖z‖ < |‖A‖ - ‖B‖|) : ψ z ≠ 0 := by
  intro h0
  have h1 := hrem z hzρ
  rw [h0, zero_sub, norm_neg] at h1
  have h2 := (norm_linearZero_bounds A B z).1
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  nlinarith

/-- The anisotropic core profile of the field: its modulus on the circle of
radius `r` is `r |A e^{iθ} + B e^{-iθ}|` up to `C r²`. -/
theorem core_profile
    (hrem : ∀ z, ‖z‖ < ρ → ‖ψ z - linearZero A B z‖ ≤ C * ‖z‖ ^ 2) (hr : 0 ≤ r) (hrρ : r < ρ)
    (θ : ℝ) : |‖ψ (circle r θ)‖ - r * ‖loop A B θ‖| ≤ C * r ^ 2 := by
  have h := hrem (circle r θ) (by rw [norm_circle hr]; exact hrρ)
  rw [norm_circle hr] at h
  have e : r * ‖loop A B θ‖ = ‖linearZero A B (circle r θ)‖ :=
    (norm_linearZero_polar A B hr θ).symm
  rw [e]
  exact (abs_norm_sub_norm_le _ _).trans h

/-- On a small circle the winding integral of the field equals that of its
linear part. -/
theorem winding_eq_loop (hψ : ContDiffOn ℝ 1 ψ (Metric.ball 0 ρ))
    (hrem : ∀ z, ‖z‖ < ρ → ‖ψ z - linearZero A B z‖ ≤ C * ‖z‖ ^ 2)
    (hr : 0 < r) (hrρ : r < ρ) (hsmall : C * r < |‖A‖ - ‖B‖|) :
    (∫ θ in (0 : ℝ)..(2 * π),
        deriv (fun θ : ℝ => ψ (circle r θ)) θ / ψ (circle r θ)) =
      ∫ θ in (0 : ℝ)..(2 * π), deriv (loop A B) θ / loop A B θ := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hmem (θ : ℝ) : circle r θ ∈ Metric.ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff, norm_circle hr.le]
    exact hrρ
  have hat (θ : ℝ) : ContDiffAt ℝ 1 ψ (circle r θ) :=
    hψ.contDiffAt (Metric.isOpen_ball.mem_nhds (hmem θ))
  have hcirc : Continuous (circle r) :=
    continuous_iff_continuousAt.mpr fun θ => (hasDerivAt_circle r θ).continuousAt
  have h₂ (θ : ℝ) : HasDerivAt (fun θ : ℝ => ψ (circle r θ))
      (fderiv ℝ ψ (circle r θ) (r * (exp (θ * I) * I))) θ :=
    ((hat θ).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circle r θ)
  have h₁ (θ : ℝ) : HasDerivAt (fun θ : ℝ => (r : ℂ) * loop A B θ)
      (r * (I * (A * exp (θ * I) - B * exp (-(θ * I))))) θ :=
    (hasDerivAt_loop A B θ).const_mul (r : ℂ)
  have hexp : Continuous fun θ : ℝ => exp ((θ : ℂ) * I) :=
    continuous_exp.comp (continuous_ofReal.mul continuous_const)
  have hexp' : Continuous fun θ : ℝ => exp (-((θ : ℂ) * I)) :=
    continuous_exp.comp (continuous_ofReal.mul continuous_const).neg
  have hc₁ : Continuous fun θ : ℝ => (r : ℂ) * (I * (A * exp (θ * I) - B * exp (-(θ * I)))) :=
    continuous_const.mul (continuous_const.mul
      ((continuous_const.mul hexp).sub (continuous_const.mul hexp')))
  have hfd : Continuous fun θ : ℝ => fderiv ℝ ψ (circle r θ) :=
    continuous_iff_continuousAt.mpr fun θ =>
      ContinuousAt.comp (g := fderiv ℝ ψ)
        ((hat θ).fderiv_right (m := 0) (by norm_num)).continuousAt hcirc.continuousAt
  have hc₂ : Continuous fun θ : ℝ => fderiv ℝ ψ (circle r θ) (r * (exp (θ * I) * I)) :=
    hfd.clm_apply (continuous_const.mul (hexp.mul continuous_const))
  have hclose (θ : ℝ) : ‖ψ (circle r θ) - (r : ℂ) * loop A B θ‖ < ‖(r : ℂ) * loop A B θ‖ := by
    have e : (r : ℂ) * loop A B θ = linearZero A B (circle r θ) := (linearZero_polar A B r θ).symm
    rw [e]
    have h1 := hrem (circle r θ) (by rw [norm_circle hr.le]; exact hrρ)
    have h2 := (norm_linearZero_bounds A B (circle r θ)).1
    rw [norm_circle hr.le] at h1 h2
    nlinarith
  have key := winding_eq_of_close (a := 0) (b := 2 * π) h₁ h₂ hc₁ hc₂ hclose
    (by simp only [loop_two_pi]) (by simp only [circle_two_pi])
  have e₂ : (fun θ : ℝ => deriv (fun θ : ℝ => ψ (circle r θ)) θ / ψ (circle r θ)) =
      fun θ : ℝ => fderiv ℝ ψ (circle r θ) (r * (exp (θ * I) * I)) / ψ (circle r θ) :=
    funext fun θ => by rw [(h₂ θ).deriv]
  have e₁ : (fun θ : ℝ => deriv (loop A B) θ / loop A B θ) =
      fun θ : ℝ => (r : ℂ) * (I * (A * exp (θ * I) - B * exp (-(θ * I)))) /
        ((r : ℂ) * loop A B θ) :=
    funext fun θ => by rw [(hasDerivAt_loop A B θ).deriv, mul_div_mul_left _ _ hr0]
  rw [e₂, e₁]
  exact key

/-- A non-degenerate zero with `|A| > |B|` has winding `+1` on every small
circle: `∮ dψ/ψ = 2πi`. -/
theorem winding_of_lt (hψ : ContDiffOn ℝ 1 ψ (Metric.ball 0 ρ))
    (hrem : ∀ z, ‖z‖ < ρ → ‖ψ z - linearZero A B z‖ ≤ C * ‖z‖ ^ 2)
    (hr : 0 < r) (hrρ : r < ρ) (hsmall : C * r < |‖A‖ - ‖B‖|) (h : ‖B‖ < ‖A‖) :
    (∫ θ in (0 : ℝ)..(2 * π),
        deriv (fun θ : ℝ => ψ (circle r θ)) θ / ψ (circle r θ)) = 2 * π * I := by
  rw [winding_eq_loop hψ hrem hr hrρ hsmall, TransverseZeroWinding.winding_of_lt h]

/-- A non-degenerate zero with `|A| < |B|` has winding `-1` on every small
circle: `∮ dψ/ψ = -2πi`. -/
theorem winding_of_gt (hψ : ContDiffOn ℝ 1 ψ (Metric.ball 0 ρ))
    (hrem : ∀ z, ‖z‖ < ρ → ‖ψ z - linearZero A B z‖ ≤ C * ‖z‖ ^ 2)
    (hr : 0 < r) (hrρ : r < ρ) (hsmall : C * r < |‖A‖ - ‖B‖|) (h : ‖A‖ < ‖B‖) :
    (∫ θ in (0 : ℝ)..(2 * π),
        deriv (fun θ : ℝ => ψ (circle r θ)) θ / ψ (circle r θ)) = -(2 * π * I) := by
  rw [winding_eq_loop hψ hrem hr hrρ hsmall, TransverseZeroWinding.winding_of_gt h]

end FoliationQM.NondegenerateZeroWinding
