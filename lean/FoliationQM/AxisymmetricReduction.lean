module

public import FoliationQM.RadialCoreAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Reduction of an axisymmetric vortex core to the radial equation

Source: v13 `thm:wallstrom` Part(b), "near a separated axisymmetric vortex
core (`∂_θ R = 0`) of winding `n` governed by a radial equation
`R'' + r⁻¹ R' - n² r⁻² R = b(r) R`", component kinds B and C. In the
transverse plane with coordinates `(x, y)`, let `r = √(x² + y²)`, which is the
Euclidean distance to the axis, and let the field be
`ψ = R(r) e^{inθ} = (x + iy)^n R(r) / r^n` for a positive winding `n`. Away
from the axis its transverse Laplacian is

`∂_x² ψ + ∂_y² ψ = e^{inθ} (R'' + r⁻¹ R' - n² r⁻² R)`,

so `ψ` solves `(∂_x² + ∂_y²) ψ = b(r) ψ` at a point exactly when `R` solves
the radial equation at its radius, and `|ψ| = |R(r)|`.

The second derivatives are iterated partial derivatives in each variable
with the other fixed. The Laplacian is the flat one of the transverse plane;
a general auxiliary metric, the longitudinal terms and a negative winding
(the complex conjugate field) are not treated.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.AxisymmetricReduction

open Complex Filter Set RadialCoreAsymptotics
open scoped Topology

/-- The field `(x + iy)^n F(x² + y²)`. -/
def field (n : ℕ) (F : ℝ → ℝ) (x y : ℝ) : ℂ :=
  ((x : ℂ) + y * I) ^ n * ((F (x ^ 2 + y ^ 2) : ℝ) : ℂ)

private theorem deriv2_pow_mul {a b b' : ℝ → ℂ} {a' b'' : ℂ} (n : ℕ) {u : ℝ}
    (ha : ∀ v, HasDerivAt a a' v) (hb : ∀ᶠ v in 𝓝 u, HasDerivAt b (b' v) v)
    (hb' : HasDerivAt b' b'' u) :
    deriv (fun v => deriv (fun v' => a v' ^ n * b v') v) u =
      (n * (((n - 1 : ℕ) : ℂ) * a u ^ (n - 1 - 1) * a') * a') * b u +
        (n * a u ^ (n - 1) * a') * b' u + ((n * a u ^ (n - 1) * a') * b' u + a u ^ n * b'') := by
  have h1 : (fun v => deriv (fun v' => a v' ^ n * b v') v) =ᶠ[𝓝 u]
      fun v => (n * a v ^ (n - 1) * a') * b v + a v ^ n * b' v := by
    filter_upwards [hb] with v hv
    exact (((ha v).fun_pow n).mul hv).deriv
  rw [h1.deriv_eq]
  have hbu : HasDerivAt b (b' u) u := hb.self_of_nhds
  have hpow : HasDerivAt (fun v => a v ^ n) (n * a u ^ (n - 1) * a') u := (ha u).fun_pow n
  have hpow1 : HasDerivAt (fun v => (n : ℂ) * a v ^ (n - 1) * a')
      (n * (((n - 1 : ℕ) : ℂ) * a u ^ (n - 1 - 1) * a') * a') u :=
    ((((ha u).fun_pow (n - 1)).const_mul (n : ℂ)).mul_const a')
  exact ((hpow1.mul hbu).add (hpow.mul hb')).deriv

private theorem pow_pred_mul (n : ℕ) (z : ℂ) : (n : ℂ) * z ^ (n - 1) * z = n * z ^ n := by
  cases n with
  | zero => simp
  | succ k => simp [pow_succ, mul_assoc]

/-- The transverse Laplacian of `(x + iy)^n F(x² + y²)` is
`(x + iy)^n (4 s F'' + 4 (n + 1) F')` at `s = x² + y²`. -/
theorem laplacian_field {F F' : ℝ → ℝ} {F'' : ℝ} (n : ℕ) (x y : ℝ)
    (hF : ∀ᶠ σ in 𝓝 (x ^ 2 + y ^ 2), HasDerivAt F (F' σ) σ)
    (hF' : HasDerivAt F' F'' (x ^ 2 + y ^ 2)) :
    deriv (fun u => deriv (fun u' => field n F u' y) u) x +
        deriv (fun v => deriv (fun v' => field n F x v') v) y =
      ((x : ℂ) + y * I) ^ n *
        ((4 * (x ^ 2 + y ^ 2) * F'' + 4 * (n + 1) * F' (x ^ 2 + y ^ 2) : ℝ) : ℂ) := by
  -- the x direction
  have hpx (v : ℝ) : HasDerivAt (fun u : ℝ => u ^ 2 + y ^ 2) (2 * v) v := by
    simpa using (hasDerivAt_pow 2 v).add_const (y ^ 2)
  have hax (v : ℝ) : HasDerivAt (fun u : ℝ => (u : ℂ) + y * I) 1 v :=
    ((hasDerivAt_id' v).ofReal_comp.add_const _).congr_deriv (by simp)
  have hbx : ∀ᶠ v in 𝓝 x, HasDerivAt (fun u : ℝ => ((F (u ^ 2 + y ^ 2) : ℝ) : ℂ))
      ((F' (v ^ 2 + y ^ 2) * (2 * v) : ℝ) : ℂ) v := by
    have ht : Tendsto (fun u : ℝ => u ^ 2 + y ^ 2) (𝓝 x) (𝓝 (x ^ 2 + y ^ 2)) :=
      (hpx x).continuousAt
    filter_upwards [ht.eventually hF] with v hv
    exact (hv.comp v (hpx v)).ofReal_comp
  have hbx' : HasDerivAt (fun v : ℝ => ((F' (v ^ 2 + y ^ 2) * (2 * v) : ℝ) : ℂ))
      ((F'' * (2 * x) * (2 * x) + F' (x ^ 2 + y ^ 2) * 2 : ℝ) : ℂ) x :=
    ((hF'.comp x (hpx x)).mul ((hasDerivAt_id' x).const_mul 2)).ofReal_comp.congr_deriv
      (by simp)
  have hX := deriv2_pow_mul n hax hbx hbx'
  -- the y direction
  have hpy (v : ℝ) : HasDerivAt (fun u : ℝ => x ^ 2 + u ^ 2) (2 * v) v := by
    simpa using (hasDerivAt_pow 2 v).const_add (x ^ 2)
  have hay (v : ℝ) : HasDerivAt (fun u : ℝ => (x : ℂ) + u * I) I v :=
    (((hasDerivAt_id' v).ofReal_comp.mul_const I).const_add _).congr_deriv (by simp)
  have hby : ∀ᶠ v in 𝓝 y, HasDerivAt (fun u : ℝ => ((F (x ^ 2 + u ^ 2) : ℝ) : ℂ))
      ((F' (x ^ 2 + v ^ 2) * (2 * v) : ℝ) : ℂ) v := by
    have ht : Tendsto (fun u : ℝ => x ^ 2 + u ^ 2) (𝓝 y) (𝓝 (x ^ 2 + y ^ 2)) :=
      (hpy y).continuousAt
    filter_upwards [ht.eventually hF] with v hv
    exact (hv.comp v (hpy v)).ofReal_comp
  have hby' : HasDerivAt (fun v : ℝ => ((F' (x ^ 2 + v ^ 2) * (2 * v) : ℝ) : ℂ))
      ((F'' * (2 * y) * (2 * y) + F' (x ^ 2 + y ^ 2) * 2 : ℝ) : ℂ) y :=
    ((hF'.comp y (hpy y)).mul ((hasDerivAt_id' y).const_mul 2)).ofReal_comp.congr_deriv
      (by simp)
  have hY := deriv2_pow_mul n hay hby hby'
  simp only [field]
  rw [hX, hY]
  have hz := pow_pred_mul n ((x : ℂ) + y * I)
  push_cast
  linear_combination ((n : ℂ) * ((n - 1 : ℕ) : ℂ) * ((x : ℂ) + y * I) ^ (n - 1 - 1) *
    (F (x ^ 2 + y ^ 2) : ℂ)) * I_sq + 4 * (F' (x ^ 2 + y ^ 2) : ℂ) * hz

variable {n : ℕ} {R R' R'' : ℝ → ℝ} {r₀ : ℝ}

/-- The radial operator `R'' + r⁻¹ R' - n² r⁻² R`. -/
def radialOperator (n : ℕ) (R R' R'' : ℝ → ℝ) (r : ℝ) : ℝ :=
  R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r

/-- With no equation assumed, the flux `r^{n+1} R' - n r^n R` has derivative
`r^{n+1}` times the radial operator. -/
theorem hasDerivAt_flux_operator (hn : n ≠ 0) {r : ℝ} (hr : r ≠ 0)
    (hR : HasDerivAt R (R' r) r) (hR' : HasDerivAt R' (R'' r) r) :
    HasDerivAt (flux n R R') (r ^ (n + 1) * radialOperator n R R' R'' r) r := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 := (hasDerivAt_pow (k + 1 + 1) r).mul hR'
  have h2 := ((hasDerivAt_pow (k + 1) r).const_mul ((k + 1 : ℕ) : ℝ)).mul hR
  refine (h1.sub h2).congr_deriv ?_
  simp only [Nat.add_sub_cancel, radialOperator]
  push_cast
  field_simp
  ring

/-- The profile `R(√s) / (√s)^n` as a function of `s = r²`. -/
def profile (n : ℕ) (R : ℝ → ℝ) (s : ℝ) : ℝ := R (√s) / (√s) ^ n

/-- The derivative of the profile in `s = r²`. -/
theorem hasDerivAt_profile (hn : n ≠ 0) {s : ℝ} (hs : 0 < s)
    (hR : HasDerivAt R (R' (√s)) (√s)) :
    HasDerivAt (profile n R) (flux n R R' (√s) / (2 * s ^ (n + 1))) s := by
  have hρ : 0 < √s := Real.sqrt_pos.mpr hs
  have h := (hasDerivAt_ratio hn hρ hR).comp s (Real.hasDerivAt_sqrt hs.ne')
  refine h.congr_deriv ?_
  have e : s ^ (n + 1) = (√s) ^ (2 * n + 1) * √s := by
    conv_lhs => rw [← Real.sq_sqrt hs.le]
    ring
  rw [e]
  field_simp

/-- The second derivative of the profile in `s = r²`, in terms of the radial
operator. -/
theorem hasDerivAt_profile_deriv (hn : n ≠ 0) {s : ℝ} (hs : 0 < s)
    (hR : HasDerivAt R (R' (√s)) (√s)) (hR' : HasDerivAt R' (R'' (√s)) (√s)) :
    HasDerivAt (fun σ => flux n R R' (√σ) / (2 * σ ^ (n + 1)))
      (radialOperator n R R' R'' (√s) / (4 * s * (√s) ^ n) -
        (n + 1) * (flux n R R' (√s) / (2 * s ^ (n + 1))) / s) s := by
  have hρ : 0 < √s := Real.sqrt_pos.mpr hs
  have hfl := (hasDerivAt_flux_operator hn hρ.ne' hR hR').comp s (Real.hasDerivAt_sqrt hs.ne')
  have hden : HasDerivAt (fun σ : ℝ => 2 * σ ^ (n + 1)) (2 * ((n + 1 : ℕ) * s ^ n)) s := by
    simpa using (hasDerivAt_pow (n + 1) s).const_mul 2
  have h := hfl.fun_div hden (by positivity)
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = √s := ⟨_, rfl⟩
  have hs2 : s = ρ ^ 2 := by rw [hρdef, Real.sq_sqrt hs.le]
  rw [← hρdef] at hρ ⊢
  rw [hs2]
  push_cast
  field_simp
  ring

/-- The axisymmetric field `R(r) e^{inθ} = (x + iy)^n R(r) / r^n`. -/
def axisymmetric (n : ℕ) (R : ℝ → ℝ) (x y : ℝ) : ℂ := field n (profile n R) x y

/-- The radius `√(x² + y²)` is the Euclidean distance to the axis. -/
theorem radius_eq_norm (x y : ℝ) : √(x ^ 2 + y ^ 2) = ‖(x : ℂ) + y * I‖ :=
  (Complex.norm_add_mul_I x y).symm

/-- The transverse Laplacian of the axisymmetric field is `e^{inθ}` times the
radial operator applied to `R`. -/
theorem laplacian_axisymmetric (hn : n ≠ 0) (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r) {x y : ℝ}
    (hr : √(x ^ 2 + y ^ 2) ∈ Ioo 0 r₀) :
    deriv (fun u => deriv (fun u' => axisymmetric n R u' y) u) x +
        deriv (fun v => deriv (fun v' => axisymmetric n R x v') v) y =
      ((x : ℂ) + y * I) ^ n / (((√(x ^ 2 + y ^ 2)) ^ n : ℝ) : ℂ) *
        ((radialOperator n R R' R'' (√(x ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
  have hs : 0 < x ^ 2 + y ^ 2 := Real.sqrt_pos.mp hr.1
  have hev : ∀ᶠ σ in 𝓝 (x ^ 2 + y ^ 2),
      HasDerivAt (profile n R) (flux n R R' (√σ) / (2 * σ ^ (n + 1))) σ := by
    have hc : ContinuousAt Real.sqrt (x ^ 2 + y ^ 2) := Real.continuous_sqrt.continuousAt
    filter_upwards [hc.eventually_mem (isOpen_Ioo.mem_nhds hr), lt_mem_nhds hs] with σ hσ hσpos
    exact hasDerivAt_profile hn hσpos (hR _ hσ)
  have h2 := hasDerivAt_profile_deriv hn hs (hR _ hr) (hR' _ hr)
  have h := laplacian_field n x y hev h2
  simp only [axisymmetric]
  rw [h]
  have hρ : 0 < √(x ^ 2 + y ^ 2) := hr.1
  have e : 4 * (x ^ 2 + y ^ 2) * (radialOperator n R R' R'' (√(x ^ 2 + y ^ 2)) /
        (4 * (x ^ 2 + y ^ 2) * (√(x ^ 2 + y ^ 2)) ^ n) -
        (n + 1) * (flux n R R' (√(x ^ 2 + y ^ 2)) / (2 * (x ^ 2 + y ^ 2) ^ (n + 1))) /
          (x ^ 2 + y ^ 2)) +
      4 * (n + 1) * (flux n R R' (√(x ^ 2 + y ^ 2)) / (2 * (x ^ 2 + y ^ 2) ^ (n + 1))) =
      radialOperator n R R' R'' (√(x ^ 2 + y ^ 2)) / (√(x ^ 2 + y ^ 2)) ^ n := by
    field_simp
    ring
  rw [e]
  push_cast
  ring

/-- The modulus of the axisymmetric field is `|R(r)|`. -/
theorem norm_axisymmetric {x y : ℝ} (hr : 0 < √(x ^ 2 + y ^ 2)) :
    ‖axisymmetric n R x y‖ = |R (√(x ^ 2 + y ^ 2))| := by
  have hpow : 0 < (√(x ^ 2 + y ^ 2)) ^ n := pow_pos hr n
  simp only [axisymmetric, field, profile, norm_mul, norm_pow, Complex.norm_add_mul_I,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hpow]
  field_simp

/-- The axisymmetric field solves `(∂_x² + ∂_y²) ψ = b ψ` at a point off the
axis exactly when `R` solves the radial equation at its radius. -/
theorem axisymmetric_solves_iff (hn : n ≠ 0) (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r) {x y : ℝ}
    (hr : √(x ^ 2 + y ^ 2) ∈ Ioo 0 r₀) (β : ℝ) :
    deriv (fun u => deriv (fun u' => axisymmetric n R u' y) u) x +
        deriv (fun v => deriv (fun v' => axisymmetric n R x v') v) y =
      (β : ℂ) * axisymmetric n R x y ↔
    radialOperator n R R' R'' (√(x ^ 2 + y ^ 2)) = β * R (√(x ^ 2 + y ^ 2)) := by
  have hρ : 0 < √(x ^ 2 + y ^ 2) := hr.1
  have hz : (x : ℂ) + y * I ≠ 0 := by
    rw [← norm_pos_iff, Complex.norm_add_mul_I]
    exact hρ
  have hρc : (((√(x ^ 2 + y ^ 2)) ^ n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_pos hρ n).ne'
  have hc : ((x : ℂ) + y * I) ^ n / (((√(x ^ 2 + y ^ 2)) ^ n : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero (pow_ne_zero n hz) hρc
  have hψ : axisymmetric n R x y = ((x : ℂ) + y * I) ^ n / (((√(x ^ 2 + y ^ 2)) ^ n : ℝ) : ℂ) *
      ((R (√(x ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
    simp only [axisymmetric, field, profile]
    push_cast
    ring
  rw [laplacian_axisymmetric hn hR hR' hr, hψ]
  constructor
  · intro h
    have h1 : ((x : ℂ) + y * I) ^ n / (((√(x ^ 2 + y ^ 2)) ^ n : ℝ) : ℂ) *
        ((radialOperator n R R' R'' (√(x ^ 2 + y ^ 2)) : ℝ) : ℂ) =
        ((x : ℂ) + y * I) ^ n / (((√(x ^ 2 + y ^ 2)) ^ n : ℝ) : ℂ) *
          ((β * R (√(x ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
      rw [h]
      push_cast
      ring
    exact_mod_cast mul_left_cancel₀ hc h1
  · intro h
    rw [h]
    push_cast
    ring

end FoliationQM.AxisymmetricReduction
