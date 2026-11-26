module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Explicit degenerate vortex solutions of the Klein–Gordon equation

Source: v13 `thm:wallstrom` Part(b), the explicit solutions
`ψ_n(x, y, t) = (x + iy)^n [r² cos t + 2(n + 1) t sin t]` in units
`c = m = ħ = 1`, component kinds A and B. Each solves
`(∂_t² - ∂_x² - ∂_y² + 1) ψ_n = 0`. For `|t| < π/2` it is a positive real
multiple of `(x + iy)^n` off the axis `r = 0`, so it vanishes exactly on the
axis and winds `n` times around it, while at `t = 0` its modulus is `r^(n+2)`.

The second derivatives are ordinary iterated derivatives in each variable with
the other two fixed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DegenerateVortexSolution

open Complex

/-- The real time-dependent factor `r² cos t + 2(n + 1) t sin t`. -/
def factor (n : ℕ) (t x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) * Real.cos t + 2 * (n + 1) * t * Real.sin t

/-- The degenerate vortex field `ψ_n`. -/
def vortex (n : ℕ) (t x y : ℝ) : ℂ :=
  ((x : ℂ) + y * I) ^ n * (factor n t x y : ℂ)

private theorem hasDerivAt_pow_mul {a b b' : ℝ → ℂ} {a' : ℂ} (k : ℕ)
    (ha : ∀ u, HasDerivAt a a' u) (hb : ∀ u, HasDerivAt b (b' u) u) (u : ℝ) :
    HasDerivAt (fun u => a u ^ k * b u)
      (k * a u ^ (k - 1) * a' * b u + a u ^ k * b' u) u :=
  ((ha u).pow k).mul (hb u)

private theorem deriv2_pow_mul {a b b' b'' : ℝ → ℂ} {a' : ℂ} (n : ℕ)
    (ha : ∀ u, HasDerivAt a a' u) (hb : ∀ u, HasDerivAt b (b' u) u)
    (hb' : ∀ u, HasDerivAt b' (b'' u) u) (u : ℝ) :
    deriv (fun v => deriv (fun s => a s ^ n * b s) v) u =
      (n - 1 : ℕ) * a u ^ (n - 1 - 1) * a' * (n * a' * b u) + a u ^ (n - 1) * (n * a' * b' u) +
        (n * a u ^ (n - 1) * a' * b' u + a u ^ n * b'' u) := by
  have h1 : (fun v => deriv (fun s => a s ^ n * b s) v) = fun v =>
      a v ^ (n - 1) * (n * a' * b v) + a v ^ n * b' v := by
    funext v
    rw [(hasDerivAt_pow_mul n ha hb v).deriv]
    ring
  rw [h1]
  exact ((hasDerivAt_pow_mul (n - 1) ha (fun v => (hb v).const_mul (n * a')) u).add
    (hasDerivAt_pow_mul n ha hb' u)).deriv

private theorem hasDerivAt_quadratic (a b c u : ℝ) :
    HasDerivAt (fun u : ℝ => (u ^ 2 + a) * b + c) (2 * u * b) u := by
  have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
  exact (((h1.add_const a).mul_const b).add_const c).congr_deriv (by ring)

private theorem hasDerivAt_linear (b u : ℝ) :
    HasDerivAt (fun u : ℝ => 2 * u * b) (2 * b) u :=
  (((hasDerivAt_id' u).const_mul 2).mul_const b).congr_deriv (by ring)

/-- The degenerate vortex fields solve the Klein–Gordon equation with unit
constants in two space dimensions. -/
theorem vortex_solves (n : ℕ) (t x y : ℝ) :
    deriv (fun s => deriv (fun s' => vortex n s' x y) s) t -
      deriv (fun u => deriv (fun u' => vortex n t u' y) u) x -
      deriv (fun u => deriv (fun u' => vortex n t x u') u) y + vortex n t x y = 0 := by
  have hA (s : ℝ) : HasDerivAt (fun s => factor n s x y)
      (-(x ^ 2 + y ^ 2) * Real.sin s + 2 * (n + 1) * (Real.sin s + s * Real.cos s)) s :=
    (((Real.hasDerivAt_cos s).const_mul (x ^ 2 + y ^ 2)).add
      (((hasDerivAt_id' s).const_mul (2 * ((n : ℝ) + 1))).mul
        (Real.hasDerivAt_sin s))).congr_deriv (by ring)
  have hA' (s : ℝ) : HasDerivAt
      (fun s => -(x ^ 2 + y ^ 2) * Real.sin s + 2 * (n + 1) * (Real.sin s + s * Real.cos s))
      (-(x ^ 2 + y ^ 2) * Real.cos s +
        2 * (n + 1) * (2 * Real.cos s - s * Real.sin s)) s :=
    (((Real.hasDerivAt_sin s).const_mul (-(x ^ 2 + y ^ 2))).add
      (((Real.hasDerivAt_sin s).add
        ((hasDerivAt_id' s).mul (Real.hasDerivAt_cos s))).const_mul
          (2 * ((n : ℝ) + 1)))).congr_deriv (by ring)
  have ht : deriv (fun s => deriv (fun s' => vortex n s' x y) s) t =
      ((x : ℂ) + y * I) ^ n * ((-(x ^ 2 + y ^ 2) * Real.cos t +
        2 * (n + 1) * (2 * Real.cos t - t * Real.sin t) : ℝ) : ℂ) := by
    have h1 : (fun s => deriv (fun s' => vortex n s' x y) s) = fun s =>
        ((x : ℂ) + y * I) ^ n * ((-(x ^ 2 + y ^ 2) * Real.sin s +
          2 * (n + 1) * (Real.sin s + s * Real.cos s) : ℝ) : ℂ) := by
      funext s
      exact ((hA s).ofReal_comp.const_mul _).deriv
    rw [h1]
    exact ((hA' t).ofReal_comp.const_mul _).deriv
  have hx := deriv2_pow_mul (a := fun u : ℝ => (u : ℂ) + y * I) (a' := 1)
    (b := fun u : ℝ => (factor n t u y : ℂ)) (b' := fun u : ℝ => ((2 * u * Real.cos t : ℝ) : ℂ))
    (b'' := fun _ => ((2 * Real.cos t : ℝ) : ℂ)) n
    (fun u => ((hasDerivAt_id' u).ofReal_comp.add_const _).congr_deriv (by simp))
    (fun u => (hasDerivAt_quadratic (y ^ 2) (Real.cos t)
      (2 * ((n : ℝ) + 1) * t * Real.sin t) u).ofReal_comp)
    (fun u => (hasDerivAt_linear (Real.cos t) u).ofReal_comp) x
  have hfy : (fun u : ℝ => factor n t x u) = fun u : ℝ =>
      (u ^ 2 + x ^ 2) * Real.cos t + 2 * ((n : ℝ) + 1) * t * Real.sin t := by
    funext u
    simp only [factor]
    ring
  have hy := deriv2_pow_mul (a := fun u : ℝ => (x : ℂ) + u * I) (a' := I)
    (b := fun u : ℝ => (factor n t x u : ℂ)) (b' := fun u : ℝ => ((2 * u * Real.cos t : ℝ) : ℂ))
    (b'' := fun _ => ((2 * Real.cos t : ℝ) : ℂ)) n
    (fun u => (((hasDerivAt_id' u).ofReal_comp.mul_const I).const_add (x : ℂ)).congr_deriv
      (by simp))
    (fun u => by
      have h := hasDerivAt_quadratic (x ^ 2) (Real.cos t)
        (2 * ((n : ℝ) + 1) * t * Real.sin t) u
      rw [← hfy] at h
      exact h.ofReal_comp)
    (fun u => (hasDerivAt_linear (Real.cos t) u).ofReal_comp) y
  have hz : (n : ℂ) * ((x : ℂ) + y * I) ^ (n - 1) * ((x : ℂ) + y * I) =
      n * ((x : ℂ) + y * I) ^ n := by
    cases n with
    | zero => simp
    | succ k => simp [pow_succ, mul_assoc]
  simp only [vortex] at ht hx hy ⊢
  rw [ht, hx, hy]
  simp only [factor]
  generalize Real.cos t = c
  generalize Real.sin t = s
  push_cast
  linear_combination (-(4 * (c : ℂ))) * hz -
    (((n - 1 : ℕ) : ℂ) * ((x : ℂ) + y * I) ^ (n - 1 - 1) * n *
      (((x : ℂ) ^ 2 + (y : ℂ) ^ 2) * c + 2 * ((n : ℂ) + 1) * t * s)) * I_sq

/-- Away from the axis and for `|t| < π/2` the real factor is positive. -/
theorem factor_pos (n : ℕ) {t x y : ℝ} (ht : |t| < Real.pi / 2) (hxy : ¬ (x = 0 ∧ y = 0)) :
    0 < factor n t x y := by
  obtain ⟨h1, h2⟩ := abs_lt.mp ht
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩
  have hr : 0 < x ^ 2 + y ^ 2 := by
    by_contra h
    have hx0 : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    exact hxy ⟨hx0, hy0⟩
  have hts : 0 ≤ t * Real.sin t := by
    rcases le_total 0 t with h | h
    · exact mul_nonneg h (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [Real.pi_pos]))
    · exact mul_nonneg_of_nonpos_of_nonpos h
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith [Real.pi_pos]))
  have hn : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by positivity
  have h3 : 0 ≤ 2 * ((n : ℝ) + 1) * t * Real.sin t := by
    rw [mul_assoc]
    exact mul_nonneg hn hts
  unfold factor
  have h4 := mul_pos hr hcos
  linarith

/-- For `|t| < π/2` and winding `n ≥ 1` the field vanishes exactly on the axis. -/
theorem vortex_eq_zero_iff {n : ℕ} (hn : n ≠ 0) {t x y : ℝ} (ht : |t| < Real.pi / 2) :
    vortex n t x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    by_contra hxy
    have hf : (factor n t x y : ℂ) ≠ 0 := by
      exact_mod_cast (factor_pos n ht hxy).ne'
    have hz : ((x : ℂ) + y * I) ^ n = 0 := (mul_eq_zero.mp h).resolve_right hf
    have hz' : (x : ℂ) + y * I = 0 := (pow_eq_zero_iff hn).mp hz
    have hre := congrArg Complex.re hz'
    have him := congrArg Complex.im hz'
    simp at hre him
    exact hxy ⟨hre, him⟩
  · rintro ⟨rfl, rfl⟩
    simp [vortex, hn]

/-- At `t = 0` the modulus is `r^(n+2)`. -/
theorem norm_vortex_zero (n : ℕ) (x y : ℝ) :
    ‖vortex n 0 x y‖ = Real.sqrt (x ^ 2 + y ^ 2) ^ (n + 2) := by
  have hr : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hf : factor n 0 x y = x ^ 2 + y ^ 2 := by simp [factor]
  rw [vortex, hf, norm_mul, norm_pow, Complex.norm_add_mul_I, Complex.norm_real,
    Real.norm_of_nonneg hr, pow_add, Real.sq_sqrt hr]

end FoliationQM.DegenerateVortexSolution
