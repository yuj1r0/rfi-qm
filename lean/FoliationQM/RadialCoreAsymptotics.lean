module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Radial asymptotics of an axisymmetric vortex core

Source: v13 `thm:wallstrom` Part(b), "near a separated axisymmetric vortex
core of winding `n ≠ 0` governed by a radial equation
`R'' + r⁻¹ R' - n² r⁻² R = b(r) R` with bounded sufficiently regular
lower-order coefficient `b(r)`, the nontrivial finite-energy radial branch
obeys `R(r) = c_n r^{|n|} (1 + O(r²))`", component kinds B and C. Let `R` solve
the radial equation on `(0, r₀)` with `|b| ≤ B`, and suppose `R` is on the
regular branch in the sense `|R(r)| ≤ W r^n` there, with `n ≥ 1` the absolute
winding. Then there is a constant `c` with

`|R(r) - c r^n| ≤ B W / (4 (n + 1)) · r^{n+2}` on `(0, r₀)`,

and if `R = O(r^{n+2})`, that is if `c = 0`, then `R` vanishes identically on
`(0, r₁)` whenever `B r₁² < 4 (n + 1)`. A nontrivial regular solution
therefore has `c ≠ 0` and `R(r) = c r^n (1 + O(r²))`.

The proof uses the flux `u = r^{n+1} R' - n r^n R = r^{2n+1} (R / r^n)'`, whose
derivative is `r^{n+1} b R`. The regular-branch bound `|R| ≤ W r^n` is the
hypothesis; that the finite-energy branch satisfies it (exclusion of the
`r^{-n}` branch) is not proved here. The radial variable is a real parameter;
its identification with a metric distance to the nodal surface is not
addressed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RadialCoreAsymptotics

open Set Filter
open scoped Topology NNReal

private theorem monotoneOn_Ioo {r₀ : ℝ} {F F' : ℝ → ℝ}
    (hF : ∀ r ∈ Ioo 0 r₀, HasDerivAt F (F' r) r) (hpos : ∀ r ∈ Ioo 0 r₀, 0 ≤ F' r) :
    MonotoneOn F (Ioo 0 r₀) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 r₀)
    (fun r hr => (hF r hr).continuousAt.continuousWithinAt) (fun r hr => ?_) (fun r hr => ?_)
  · rw [interior_Ioo] at hr
    exact (hF r hr).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo] at hr
    rw [(hF r hr).deriv]
    exact hpos r hr

/-- A function whose derivative is dominated by the derivative of a second
function varies by at most the variation of the second. -/
theorem abs_sub_le_of_deriv_le {r₀ : ℝ} {f f' φ φ' : ℝ → ℝ}
    (hf : ∀ r ∈ Ioo 0 r₀, HasDerivAt f (f' r) r) (hφ : ∀ r ∈ Ioo 0 r₀, HasDerivAt φ (φ' r) r)
    (hle : ∀ r ∈ Ioo 0 r₀, |f' r| ≤ φ' r) {s r : ℝ} (hs : s ∈ Ioo 0 r₀) (hr : r ∈ Ioo 0 r₀)
    (hsr : s ≤ r) : |f r - f s| ≤ φ r - φ s := by
  have h1 := monotoneOn_Ioo (F := fun x => φ x - f x) (F' := fun x => φ' x - f' x)
    (fun x hx => (hφ x hx).sub (hf x hx))
    (fun x hx => by have := (abs_le.mp (hle x hx)).2; linarith) hs hr hsr
  have h2 := monotoneOn_Ioo (F := fun x => φ x + f x) (F' := fun x => φ' x + f' x)
    (fun x hx => (hφ x hx).add (hf x hx))
    (fun x hx => by have := (abs_le.mp (hle x hx)).1; linarith) hs hr hsr
  simp only at h1 h2
  rw [abs_le]
  constructor <;> linarith

variable {n : ℕ} {R R' R'' b : ℝ → ℝ} {r₀ B W : ℝ}

/-- The flux `r^{n+1} R' - n r^n R = r^{2n+1} (R / r^n)'` of the radial
equation. -/
def flux (n : ℕ) (R R' : ℝ → ℝ) (r : ℝ) : ℝ := r ^ (n + 1) * R' r - n * r ^ n * R r

/-- Along a solution of the radial equation the flux has derivative
`r^{n+1} b R`. -/
theorem hasDerivAt_flux (hn : n ≠ 0) (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hode : ∀ r ∈ Ioo 0 r₀,
      R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r = b r * R r)
    {r : ℝ} (hr : r ∈ Ioo 0 r₀) :
    HasDerivAt (flux n R R') (r ^ (n + 1) * (b r * R r)) r := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hr0 : r ≠ 0 := hr.1.ne'
  have h1 := (hasDerivAt_pow (k + 1 + 1) r).mul (hR' r hr)
  have h2 := ((hasDerivAt_pow (k + 1) r).const_mul ((k + 1 : ℕ) : ℝ)).mul (hR r hr)
  have e := hode r hr
  refine (h1.sub h2).congr_deriv ?_
  rw [← e]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- The derivative of `R / r^n` is the flux divided by `r^{2n+1}`. -/
theorem hasDerivAt_ratio (hn : n ≠ 0) {r : ℝ} (hr : 0 < r) (hR : HasDerivAt R (R' r) r) :
    HasDerivAt (fun x => R x / x ^ n) (flux n R R' r / r ^ (2 * n + 1)) r := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine (hR.fun_div (hasDerivAt_pow (k + 1) r) (pow_ne_zero _ hr.ne')).congr_deriv ?_
  simp only [flux, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- Radial core asymptotics: a regular-branch solution of the radial equation
is `c r^n` up to an error `B W / (4 (n + 1)) r^{n+2}`. -/
theorem core_asymptotics (hn : n ≠ 0) (hr₀ : 0 < r₀)
    (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hode : ∀ r ∈ Ioo 0 r₀,
      R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r = b r * R r)
    (hb : ∀ r ∈ Ioo 0 r₀, |b r| ≤ B) (hW : ∀ r ∈ Ioo 0 r₀, |R r| ≤ W * r ^ n) :
    ∃ c : ℝ, ∀ r ∈ Ioo 0 r₀, |R r - c * r ^ n| ≤ B * W / (4 * (n + 1)) * r ^ (n + 2) := by
  have hmid : r₀ / 2 ∈ Ioo 0 r₀ := ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb _ hmid)
  have hW0 : 0 ≤ W :=
    nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hW _ hmid)) (pow_pos hmid.1 n)
  -- the flux and its variation
  have hu : ∀ r ∈ Ioo 0 r₀, HasDerivAt (flux n R R') (r ^ (n + 1) * (b r * R r)) r :=
    fun r hr => hasDerivAt_flux hn hR hR' hode hr
  obtain ⟨K₂, hK₂def⟩ : ∃ K₂ : ℝ, K₂ = B * W / (2 * (n + 1)) := ⟨_, rfl⟩
  have hK₂ : 0 ≤ K₂ := by rw [hK₂def]; positivity
  have hφ₂ : ∀ r ∈ Ioo 0 r₀,
      HasDerivAt (fun x : ℝ => K₂ * x ^ (2 * n + 1 + 1)) (B * W * r ^ (2 * n + 1)) r := by
    intro r hr
    refine ((hasDerivAt_pow (2 * n + 1 + 1) r).const_mul K₂).congr_deriv ?_
    simp only [Nat.add_sub_cancel, hK₂def]
    push_cast
    field_simp
    ring
  have hle₂ : ∀ r ∈ Ioo 0 r₀, |r ^ (n + 1) * (b r * R r)| ≤ B * W * r ^ (2 * n + 1) := by
    intro r hr
    have hrp : 0 < r := hr.1
    rw [abs_mul, abs_mul, abs_of_pos (pow_pos hrp _)]
    calc r ^ (n + 1) * (|b r| * |R r|) ≤ r ^ (n + 1) * (B * (W * r ^ n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hb r hr) (hW r hr) (abs_nonneg _) hB)
            (pow_pos hrp _).le
      _ = B * W * r ^ (2 * n + 1) := by ring
  have hvar₂ : ∀ s ∈ Ioo 0 r₀, ∀ r ∈ Ioo 0 r₀, s ≤ r →
      |flux n R R' r - flux n R R' s| ≤
        K₂ * r ^ (2 * n + 1 + 1) - K₂ * s ^ (2 * n + 1 + 1) :=
    fun s hs r hr hsr => abs_sub_le_of_deriv_le hu hφ₂ hle₂ hs hr hsr
  -- the ratio and mean-value points where the flux is small
  have hw : ∀ r ∈ Ioo 0 r₀,
      HasDerivAt (fun x => R x / x ^ n) (flux n R R' r / r ^ (2 * n + 1)) r :=
    fun r hr => hasDerivAt_ratio hn hr.1 (hR r hr)
  have hwb : ∀ r ∈ Ioo 0 r₀, |R r / r ^ n| ≤ W := by
    intro r hr
    rw [abs_div, abs_of_pos (pow_pos hr.1 n), div_le_iff₀ (pow_pos hr.1 n)]
    exact hW r hr
  have hξ : ∀ s ∈ Ioo 0 r₀, ∃ ξ ∈ Ioo (s / 2) s, |flux n R R' ξ| ≤ 4 * W * s ^ (2 * n) := by
    intro s hs
    have hsp : 0 < s := hs.1
    have hs2 : s / 2 ∈ Ioo 0 r₀ := ⟨by linarith, by linarith [hs.2]⟩
    have hsub : Icc (s / 2) s ⊆ Ioo 0 r₀ := fun x hx =>
      ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 hs.2⟩
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun x => R x / x ^ n)
      (fun r => flux n R R' r / r ^ (2 * n + 1)) (by linarith : s / 2 < s)
      (fun x hx => (hw x (hsub hx)).continuousAt.continuousWithinAt)
      (fun x hx => hw x (hsub ⟨hx.1.le, hx.2.le⟩))
    refine ⟨ξ, hξ, ?_⟩
    have hξp : 0 < ξ := (hsub ⟨hξ.1.le, hξ.2.le⟩).1
    have hd : |R s / s ^ n - R (s / 2) / (s / 2) ^ n| ≤ 2 * W := by
      have h1 := abs_sub (R s / s ^ n) (R (s / 2) / (s / 2) ^ n)
      linarith [hwb s hs, hwb (s / 2) hs2]
    have h1 : |flux n R R' ξ / ξ ^ (2 * n + 1)| ≤ 4 * W / s := by
      rw [hslope, abs_div, abs_of_pos (by linarith : (0 : ℝ) < s - s / 2),
        div_le_div_iff₀ (by linarith) hsp]
      calc |R s / s ^ n - R (s / 2) / (s / 2) ^ n| * s ≤ 2 * W * s :=
            mul_le_mul_of_nonneg_right hd hsp.le
        _ = 4 * W * (s - s / 2) := by ring
    have hpow : ξ ^ (2 * n + 1) ≤ s ^ (2 * n + 1) := pow_le_pow_left₀ hξp.le hξ.2.le _
    have h2 : |flux n R R' ξ| = |flux n R R' ξ / ξ ^ (2 * n + 1)| * ξ ^ (2 * n + 1) := by
      rw [abs_div, abs_of_pos (pow_pos hξp _), div_mul_cancel₀ _ (pow_pos hξp _).ne']
    rw [h2]
    calc |flux n R R' ξ / ξ ^ (2 * n + 1)| * ξ ^ (2 * n + 1) ≤ 4 * W / s * s ^ (2 * n + 1) :=
          mul_le_mul h1 hpow (pow_pos hξp _).le (by positivity)
      _ = 4 * W * s ^ (2 * n) := by
          field_simp
          ring
  -- the flux bound
  have hflux : ∀ r ∈ Ioo 0 r₀, |flux n R R' r| ≤ K₂ * r ^ (2 * n + 1 + 1) := by
    intro r hr
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        |flux n R R' r| ≤ 4 * W * s ^ (2 * n) + K₂ * r ^ (2 * n + 1 + 1) := by
      filter_upwards [Ioo_mem_nhdsGT hr.1] with s hs
      have hsI : s ∈ Ioo 0 r₀ := ⟨hs.1, hs.2.trans hr.2⟩
      obtain ⟨ξ, hξm, hξb⟩ := hξ s hsI
      have hξp : 0 < ξ := by linarith [hξm.1, hs.1]
      have hξI : ξ ∈ Ioo 0 r₀ := ⟨hξp, hξm.2.trans hsI.2⟩
      have hv := hvar₂ ξ hξI r hr (hξm.2.trans hs.2).le
      have hK : 0 ≤ K₂ * ξ ^ (2 * n + 1 + 1) := by positivity
      have habs := abs_sub_abs_le_abs_sub (flux n R R' r) (flux n R R' ξ)
      linarith
    have ht : Tendsto (fun s : ℝ => 4 * W * s ^ (2 * n) + K₂ * r ^ (2 * n + 1 + 1))
        (𝓝[>] 0) (𝓝 (K₂ * r ^ (2 * n + 1 + 1))) := by
      have hc : Continuous fun s : ℝ => 4 * W * s ^ (2 * n) + K₂ * r ^ (2 * n + 1 + 1) := by
        fun_prop
      have h0 := hc.tendsto 0
      have hz : (0 : ℝ) ^ (2 * n) = 0 := zero_pow (by omega)
      simp only [hz, mul_zero, zero_add] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto ht hev
  -- the ratio varies quadratically
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = B * W / (4 * (n + 1)) := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  have hφ : ∀ r ∈ Ioo 0 r₀, HasDerivAt (fun x : ℝ => K * x ^ 2) (2 * K * r) r := by
    intro r hr
    refine ((hasDerivAt_pow 2 r).const_mul K).congr_deriv ?_
    norm_num
    ring
  have hle : ∀ r ∈ Ioo 0 r₀, |flux n R R' r / r ^ (2 * n + 1)| ≤ 2 * K * r := by
    intro r hr
    rw [abs_div, abs_of_pos (pow_pos hr.1 _), div_le_iff₀ (pow_pos hr.1 _)]
    calc |flux n R R' r| ≤ K₂ * r ^ (2 * n + 1 + 1) := hflux r hr
      _ = 2 * K * r * r ^ (2 * n + 1) := by
          rw [hK₂def, hKdef]
          field_simp
          ring
  have hvar : ∀ s ∈ Ioo 0 r₀, ∀ r ∈ Ioo 0 r₀, s ≤ r →
      |R r / r ^ n - R s / s ^ n| ≤ K * r ^ 2 - K * s ^ 2 :=
    fun s hs r hr hsr => abs_sub_le_of_deriv_le hw hφ hle hs hr hsr
  -- Lipschitz extension to the core and the limit coefficient
  have hLip : LipschitzOnWith (Real.toNNReal (2 * K * r₀)) (fun x => R x / x ^ n)
      (Ioo 0 r₀) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    rcases le_total y x with h | h
    · have h1 := hvar y hy x hx h
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      nlinarith [mul_nonneg (mul_nonneg hK (sub_nonneg.mpr h))
        (by linarith [hx.2, hy.2] : (0 : ℝ) ≤ 2 * r₀ - (x + y))]
    · have h1 := hvar x hx y hy h
      rw [abs_sub_comm (R x / x ^ n), abs_sub_comm x, abs_of_nonneg (sub_nonneg.mpr h)]
      nlinarith [mul_nonneg (mul_nonneg hK (sub_nonneg.mpr h))
        (by linarith [hx.2, hy.2] : (0 : ℝ) ≤ 2 * r₀ - (y + x))]
  obtain ⟨g, hg, hgeq⟩ := hLip.extend_real
  refine ⟨g 0, fun r hr => ?_⟩
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), |R r / r ^ n - g s| ≤ K * r ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT hr.1] with s hs
    have hsI : s ∈ Ioo 0 r₀ := ⟨hs.1, hs.2.trans hr.2⟩
    have h1 := hvar s hsI r hr hs.2.le
    have h2 : g s = R s / s ^ n := (hgeq hsI).symm
    have h3 : 0 ≤ K * s ^ 2 := by positivity
    rw [h2]
    linarith
  have ht : Tendsto (fun s => |R r / r ^ n - g s|) (𝓝[>] 0) (𝓝 |R r / r ^ n - g 0|) :=
    ((continuous_const.sub hg.continuous).abs.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := le_of_tendsto ht hev
  have hrn : 0 < r ^ n := pow_pos hr.1 n
  have e : R r - g 0 * r ^ n = (R r / r ^ n - g 0) * r ^ n := by
    field_simp
  rw [e, abs_mul, abs_of_pos hrn]
  calc |R r / r ^ n - g 0| * r ^ n ≤ K * r ^ 2 * r ^ n :=
        mul_le_mul_of_nonneg_right hlim hrn.le
    _ = B * W / (4 * (n + 1)) * r ^ (n + 2) := by
        rw [hKdef]
        ring

/-- A regular-branch solution whose leading coefficient vanishes, in the sense
`R = O(r^{n+2})`, vanishes identically near the core. Hence a nontrivial
regular solution has a nonzero leading coefficient. -/
theorem eq_zero_of_coeff_zero (hn : n ≠ 0) {r₁ C₀ : ℝ} (hr₁ : 0 < r₁)
    (hR : ∀ r ∈ Ioo 0 r₁, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₁, HasDerivAt R' (R'' r) r)
    (hode : ∀ r ∈ Ioo 0 r₁,
      R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r = b r * R r)
    (hb : ∀ r ∈ Ioo 0 r₁, |b r| ≤ B) (hW : ∀ r ∈ Ioo 0 r₁, |R r| ≤ W * r ^ n)
    (hzero : ∀ r ∈ Ioo 0 r₁, |R r| ≤ C₀ * r ^ (n + 2))
    (hsmall : B * r₁ ^ 2 < 4 * (n + 1)) :
    ∀ r ∈ Ioo 0 r₁, R r = 0 := by
  have hmid : r₁ / 2 ∈ Ioo 0 r₁ := ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb _ hmid)
  have hW0 : 0 ≤ W :=
    nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hW _ hmid)) (pow_pos hmid.1 n)
  have hn1 : (0 : ℝ) < 4 * (n + 1) := by positivity
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = B * r₁ ^ 2 / (4 * (n + 1)) := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hθ1 : θ < 1 := by rw [hθdef, div_lt_one hn1]; exact hsmall
  have hstep : ∀ j : ℕ, ∀ r ∈ Ioo 0 r₁, |R r| ≤ θ ^ j * W * r ^ n := by
    intro j
    induction j with
    | zero =>
      intro r hr
      simpa using hW r hr
    | succ j ih =>
      obtain ⟨c, hc⟩ := core_asymptotics hn hr₁ hR hR' hode hb ih
      have hc0 : c = 0 := by
        by_contra hne
        have hcpos : 0 < |c| := abs_pos.mpr hne
        obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = B * (θ ^ j * W) / (4 * (n + 1)) + C₀ := ⟨_, rfl⟩
        have hbound : ∀ r ∈ Ioo 0 r₁, |c| ≤ D * r ^ 2 := by
          intro r hr
          have hrn : 0 < r ^ n := pow_pos hr.1 n
          have h1 := hc r hr
          have h2 := hzero r hr
          have h3 : |c * r ^ n| ≤ |R r - c * r ^ n| + |R r| := by
            have h4 := abs_sub (R r) (R r - c * r ^ n)
            rw [show R r - (R r - c * r ^ n) = c * r ^ n by ring] at h4
            linarith
          rw [abs_mul, abs_of_pos hrn] at h3
          have h5 : |c| * r ^ n ≤ D * r ^ 2 * r ^ n := by
            calc |c| * r ^ n ≤ B * (θ ^ j * W) / (4 * (n + 1)) * r ^ (n + 2) +
                  C₀ * r ^ (n + 2) := by linarith
              _ = D * r ^ 2 * r ^ n := by
                  rw [hDdef]
                  ring
          exact le_of_mul_le_mul_right h5 hrn
        have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), |c| ≤ D * s ^ 2 := by
          filter_upwards [Ioo_mem_nhdsGT hr₁] with s hs
          exact hbound s hs
        have ht : Tendsto (fun s : ℝ => D * s ^ 2) (𝓝[>] 0) (𝓝 0) := by
          have hcont : Continuous fun s : ℝ => D * s ^ 2 := by fun_prop
          have h0 := hcont.tendsto 0
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h0
          exact h0.mono_left nhdsWithin_le_nhds
        exact absurd (ge_of_tendsto ht hev) (not_le.mpr hcpos)
      intro r hr
      have hrp : 0 < r := hr.1
      have h1 := hc r hr
      rw [hc0, zero_mul, sub_zero] at h1
      have hr2 : r ^ 2 ≤ r₁ ^ 2 := pow_le_pow_left₀ hrp.le hr.2.le 2
      calc |R r| ≤ B * (θ ^ j * W) / (4 * (n + 1)) * r ^ (n + 2) := h1
        _ = θ ^ j * W * (B * r ^ 2 / (4 * (n + 1))) * r ^ n := by ring
        _ ≤ θ ^ j * W * θ * r ^ n := by
            have h6 : B * r ^ 2 / (4 * (n + 1)) ≤ θ := by
              rw [hθdef]
              exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 hB) hn1.le
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h6 (by positivity)) (pow_pos hrp n).le
        _ = θ ^ (j + 1) * W * r ^ n := by ring
  intro r hr
  have ht : Tendsto (fun j : ℕ => θ ^ j * W * r ^ n) atTop (𝓝 (0 * W * r ^ n)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const W).mul_const (r ^ n)
  rw [zero_mul, zero_mul] at ht
  have h := ge_of_tendsto' ht fun j => hstep j r hr
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

end FoliationQM.RadialCoreAsymptotics
