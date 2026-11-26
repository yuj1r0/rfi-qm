module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Winding of a non-degenerate transverse zero at leading order

Source: v13 `thm:wallstrom` Part(b), "near a generic non-degenerate smooth
transverse zero (`|A| ≠ |B|` in `ψ_⊥ = A z + B z̄ + O(|z|²)`), the winding is
`n = ±1` with anisotropic core profile `r |A e^{iθ} + B e^{-iθ}|`", component
kinds A and C. For the linear part `A z + B z̄` the modulus on the circle of
radius `r` is exactly `r |A e^{iθ} + B e^{-iθ}|`, it is comparable to `|z|`
and vanishes only at `z = 0` when `|A| ≠ |B|`, and its winding integral
`∮ dψ/ψ` around the unit circle is `2πi` when `|A| > |B|` and `-2πi` when
`|A| < |B|`.

Only the linear part is treated. The `O(|z|²)` remainder of an actual field
and the radial ordinary differential equation of the axisymmetric case are
not addressed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TransverseZeroWinding

open Complex MeasureTheory
open scoped Real ComplexConjugate

/-- The linear part of a field at a transverse zero. -/
def linearZero (A B z : ℂ) : ℂ := A * z + B * conj z

/-- The linear part on the unit circle, as a function of the angle. -/
def loop (A B : ℂ) (θ : ℝ) : ℂ := A * exp (θ * I) + B * exp (-(θ * I))

/-- On the circle of radius `r` the linear part is `r` times its unit-circle value. -/
theorem linearZero_polar (A B : ℂ) (r θ : ℝ) :
    linearZero A B (r * exp (θ * I)) = r * loop A B θ := by
  have hc : conj (exp (θ * I)) = exp (-(θ * I)) := by
    rw [← Complex.exp_conj]
    simp
  simp only [linearZero, loop, map_mul, Complex.conj_ofReal, hc]
  ring

/-- The anisotropic core profile `r |A e^{iθ} + B e^{-iθ}|`. -/
theorem norm_linearZero_polar (A B : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖linearZero A B (r * exp (θ * I))‖ = r * ‖loop A B θ‖ := by
  rw [linearZero_polar, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]

/-- The linear part is comparable to the distance from the zero. -/
theorem norm_linearZero_bounds (A B z : ℂ) :
    |‖A‖ - ‖B‖| * ‖z‖ ≤ ‖linearZero A B z‖ ∧ ‖linearZero A B z‖ ≤ (‖A‖ + ‖B‖) * ‖z‖ := by
  have h1 : ‖A * z‖ = ‖A‖ * ‖z‖ := norm_mul _ _
  have h2 : ‖B * conj z‖ = ‖B‖ * ‖z‖ := by rw [norm_mul, RCLike.norm_conj]
  constructor
  · have h := abs_norm_sub_norm_le (A * z) (-(B * conj z))
    rw [norm_neg, h1, h2, sub_neg_eq_add] at h
    calc |‖A‖ - ‖B‖| * ‖z‖ = |‖A‖ * ‖z‖ - ‖B‖ * ‖z‖| := by
          rw [← sub_mul, abs_mul, abs_of_nonneg (norm_nonneg z)]
      _ ≤ _ := h
  · calc ‖linearZero A B z‖ ≤ ‖A * z‖ + ‖B * conj z‖ := norm_add_le _ _
      _ = (‖A‖ + ‖B‖) * ‖z‖ := by rw [h1, h2]; ring

/-- A non-degenerate linear part vanishes only at the zero itself. -/
theorem linearZero_eq_zero_iff {A B : ℂ} (h : ‖A‖ ≠ ‖B‖) (z : ℂ) :
    linearZero A B z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have hb := (norm_linearZero_bounds A B z).1
    rw [hz, norm_zero] at hb
    have hpos : 0 < |‖A‖ - ‖B‖| := abs_pos.mpr (sub_ne_zero.mpr h)
    have hz0 : ‖z‖ ≤ 0 := by
      by_contra hc
      have := mul_pos hpos (not_le.mp hc)
      linarith
    exact norm_le_zero_iff.mp hz0
  · rintro rfl
    simp [linearZero]

private theorem winding_aux {P Q : ℂ} (h : ‖Q‖ < ‖P‖) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (∫ θ in (0 : ℝ)..(2 * π),
      deriv (fun θ : ℝ => P * exp ((θ : ℂ) * (ε * I)) + Q * exp ((θ : ℂ) * (-(ε * I)))) θ /
        (P * exp ((θ : ℂ) * (ε * I)) + Q * exp ((θ : ℂ) * (-(ε * I))))) = 2 * π * ε * I := by
  have hP : P ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg Q) h)
  set c : ℂ := Q / P with hc
  have hcn : ‖c‖ < 1 := by
    rw [hc, norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hP)).mpr h
  let u : ℝ → ℂ := fun θ => c * exp ((θ : ℂ) * (-2 * ε * I))
  have hexp (θ : ℝ) (s : ℂ) : HasDerivAt (fun θ : ℝ => exp ((θ : ℂ) * s))
      (exp ((θ : ℂ) * s) * s) θ :=
    (((hasDerivAt_id' θ).ofReal_comp.mul_const s).congr_deriv (by simp)).cexp
  have hu (θ : ℝ) : HasDerivAt u (c * (exp ((θ : ℂ) * (-2 * ε * I)) * (-2 * ε * I))) θ :=
    (hexp θ _).const_mul c
  have hunorm (θ : ℝ) : ‖u θ‖ = ‖c‖ := by
    have : (θ : ℂ) * (-2 * ε * I) = ((-2 * ε * θ : ℝ) : ℂ) * I := by push_cast; ring
    simp only [u, norm_mul, this, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hne (θ : ℝ) : 1 + u θ ≠ 0 := by
    intro h0
    have h1 : u θ = -1 := eq_neg_of_add_eq_zero_right h0
    have h2 := hunorm θ
    rw [h1, norm_neg, norm_one] at h2
    linarith
  have hslit (θ : ℝ) : 1 + u θ ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    left
    have h1 : -‖u θ‖ ≤ (u θ).re := (abs_le.mp (Complex.abs_re_le_norm (u θ))).1
    rw [hunorm θ] at h1
    simp only [Complex.add_re, Complex.one_re]
    linarith
  let G : ℝ → ℂ := fun θ => log (1 + u θ)
  let G' : ℝ → ℂ := fun θ =>
    c * (exp ((θ : ℂ) * (-2 * ε * I)) * (-2 * ε * I)) / (1 + u θ)
  have hG (θ : ℝ) : HasDerivAt G (G' θ) θ := ((hu θ).const_add 1).clog_real (hslit θ)
  have hucont : Continuous u :=
    continuous_const.mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const))
  have hG'cont : Continuous G' :=
    (continuous_const.mul ((Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const)).div
      (continuous_const.add hucont) hne
  have hGint : (∫ θ in (0 : ℝ)..(2 * π), G' θ) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hG θ)
      (hG'cont.intervalIntegrable _ _)]
    have hper : u (2 * π) = u 0 := by
      have h4 : ((2 * π : ℝ) : ℂ) * (-2 * ε * I) = ((-2 * ε : ℝ) : ℂ) * (2 * π * I) := by
        push_cast; ring
      have hint : ∃ n : ℤ, ((-2 * ε : ℝ) : ℂ) = n := by
        rcases hε with rfl | rfl
        · exact ⟨-2, by push_cast; ring⟩
        · exact ⟨2, by push_cast; ring⟩
      obtain ⟨n, hn⟩ := hint
      simp only [u]
      rw [h4, hn, exp_int_mul_two_pi_mul_I]
      simp
    simp only [G, hper, sub_self]
  have hpoint (θ : ℝ) :
      deriv (fun θ : ℝ => P * exp ((θ : ℂ) * (ε * I)) + Q * exp ((θ : ℂ) * (-(ε * I)))) θ /
        (P * exp ((θ : ℂ) * (ε * I)) + Q * exp ((θ : ℂ) * (-(ε * I)))) = ε * I + G' θ := by
    have hd : HasDerivAt
        (fun θ : ℝ => P * exp ((θ : ℂ) * (ε * I)) + Q * exp ((θ : ℂ) * (-(ε * I))))
        (P * (exp ((θ : ℂ) * (ε * I)) * (ε * I)) +
          Q * (exp ((θ : ℂ) * (-(ε * I))) * (-(ε * I)))) θ :=
      ((hexp θ _).const_mul P).add ((hexp θ _).const_mul Q)
    rw [hd.deriv]
    have hQ : Q = P * c := by rw [hc, mul_div_cancel₀ _ hP]
    have hsplit : exp ((θ : ℂ) * (-(ε * I))) =
        exp ((θ : ℂ) * (ε * I)) * exp ((θ : ℂ) * (-2 * ε * I)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have he : exp ((θ : ℂ) * (ε * I)) ≠ 0 := Complex.exp_ne_zero _
    have hden : P * exp ((θ : ℂ) * (ε * I)) + Q * exp ((θ : ℂ) * (-(ε * I))) =
        P * exp ((θ : ℂ) * (ε * I)) * (1 + u θ) := by
      simp only [u]
      rw [hQ, hsplit]
      ring
    rw [hden]
    simp only [G', u]
    rw [hQ, hsplit]
    have h1 := hne θ
    simp only [u] at h1
    generalize exp ((θ : ℂ) * (ε * I)) = E1 at he ⊢
    generalize exp ((θ : ℂ) * (-2 * ε * I)) = E2 at h1 ⊢
    field_simp
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpoint θ),
    intervalIntegral.integral_add intervalIntegrable_const (hG'cont.intervalIntegrable _ _),
    hGint, intervalIntegral.integral_const]
  simp only [sub_zero, add_zero, Complex.real_smul]
  push_cast
  ring

/-- The unit-circle value written with real-scaled exponents. -/
theorem loop_eq (A B : ℂ) :
    loop A B = fun θ : ℝ => A * exp ((θ : ℂ) * ((1 : ℝ) * I)) +
      B * exp ((θ : ℂ) * (-((1 : ℝ) * I))) := by
  funext θ
  simp [loop]

/-- A non-degenerate zero with `|A| > |B|` has winding `+1`: `∮ dψ/ψ = 2πi`. -/
theorem winding_of_lt {A B : ℂ} (h : ‖B‖ < ‖A‖) :
    (∫ θ in (0 : ℝ)..(2 * π), deriv (loop A B) θ / loop A B θ) = 2 * π * I := by
  have h1 := winding_aux h (ε := 1) (Or.inl rfl)
  rw [loop_eq]
  simpa using h1

/-- A non-degenerate zero with `|A| < |B|` has winding `-1`: `∮ dψ/ψ = -2πi`. -/
theorem winding_of_gt {A B : ℂ} (h : ‖A‖ < ‖B‖) :
    (∫ θ in (0 : ℝ)..(2 * π), deriv (loop A B) θ / loop A B θ) = -(2 * π * I) := by
  have h1 := winding_aux h (ε := -1) (Or.inr rfl)
  have hfun : loop A B = fun θ : ℝ => B * exp ((θ : ℂ) * (((-1 : ℝ) : ℂ) * I)) +
      A * exp ((θ : ℂ) * (-(((-1 : ℝ) : ℂ) * I))) := by
    funext θ
    simp only [loop]
    push_cast
    ring_nf
  rw [hfun]
  simpa using h1

end FoliationQM.TransverseZeroWinding
