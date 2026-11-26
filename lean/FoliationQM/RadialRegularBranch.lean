module

public import FoliationQM.RadialFiniteEnergy

/-!
# The finite-energy radial branch is the regular branch

Source: v13 `thm:wallstrom` Part(b), "the nontrivial finite-energy radial
branch obeys `R(r) = c_n r^{|n|} (1 + O(r²))`", component kinds C and D. Let
`R` solve `R'' + r⁻¹ R' - n² r⁻² R = b R` on `(0, r₀)` with `|b| ≤ B` and
`n ≥ 1`, and let its flux `u = r^{n+1} R' - n r^n R` vanish at the core in
the sense `|u(s)| ≤ Λ s`. A bound `|R| ≤ M r^α` then gives the flux bound
`|u| ≤ B M / (n + α + 2) · r^{n+α+2}`, and through
`(R / r^n)' = u / r^{2n+1}` the improved bound `|R| ≤ M' r^{α+1}` as long as
`α + 1 < n`; at `α = n - 1` the ratio `R / r^n` has bounded derivative, so
`|R| ≤ W r^n`. Starting from the boundedness of a finite-energy solution and
the vanishing of its flux, this gives the regular-branch bound, and with it
the asymptotics `|R - c r^n| ≤ B W / (4 (n + 1)) · r^{n+2}`.

Finite energy is in the form used for the boundedness and flux statements:
the integral of `R'² r + n² R² / r` over every compact subinterval of
`(0, r₀)` is at most a fixed `E`. The radial variable is a real parameter;
its identification with a metric distance to the nodal surface is not
addressed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RadialRegularBranch

open Set Filter RadialCoreAsymptotics RadialFiniteEnergy
open scoped Topology

variable {n : ℕ} {R R' R'' b : ℝ → ℝ} {r₀ B Λ : ℝ}

/-- A power bound on the profile and a flux vanishing at the core give a
power bound on the flux. -/
theorem flux_power_bound (hn : n ≠ 0) (hr₀ : 0 < r₀)
    (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hode : ∀ r ∈ Ioo 0 r₀,
      R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r = b r * R r)
    (hb : ∀ r ∈ Ioo 0 r₀, |b r| ≤ B)
    (hvan : ∀ s ∈ Ioo 0 r₀, |flux n R R' s| ≤ Λ * s) {α : ℕ} {Mα : ℝ}
    (hα : ∀ r ∈ Ioo 0 r₀, |R r| ≤ Mα * r ^ α) :
    ∀ r ∈ Ioo 0 r₀, |flux n R R' r| ≤ B * Mα / (n + α + 2) * r ^ (n + α + 1 + 1) := by
  have hmid : r₀ / 2 ∈ Ioo 0 r₀ := ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb _ hmid)
  have hM0 : 0 ≤ Mα :=
    nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hα _ hmid)) (pow_pos hmid.1 α)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = B * Mα / (n + α + 2) := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  rw [← hKdef]
  have hu : ∀ r ∈ Ioo 0 r₀, HasDerivAt (flux n R R') (r ^ (n + 1) * (b r * R r)) r :=
    fun r hr => hasDerivAt_flux hn hR hR' hode hr
  have hφ : ∀ r ∈ Ioo 0 r₀, HasDerivAt (fun x : ℝ => K * x ^ (n + α + 1 + 1))
      (B * Mα * r ^ (n + α + 1)) r := by
    intro r hr
    refine ((hasDerivAt_pow (n + α + 1 + 1) r).const_mul K).congr_deriv ?_
    simp only [Nat.add_sub_cancel, hKdef]
    push_cast
    field_simp
    ring
  have hle : ∀ r ∈ Ioo 0 r₀, |r ^ (n + 1) * (b r * R r)| ≤ B * Mα * r ^ (n + α + 1) := by
    intro r hr
    have hrp : 0 < r := hr.1
    rw [abs_mul, abs_mul, abs_of_pos (pow_pos hrp _)]
    calc r ^ (n + 1) * (|b r| * |R r|) ≤ r ^ (n + 1) * (B * (Mα * r ^ α)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hb r hr) (hα r hr) (abs_nonneg _) hB)
            (pow_pos hrp _).le
      _ = B * Mα * r ^ (n + α + 1) := by ring
  intro r hr
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      |flux n R R' r| ≤ Λ * s + K * r ^ (n + α + 1 + 1) := by
    filter_upwards [Ioo_mem_nhdsGT hr.1] with s hs
    have hsI : s ∈ Ioo 0 r₀ := ⟨hs.1, hs.2.trans hr.2⟩
    have hv := abs_sub_le_of_deriv_le hu hφ hle hsI hr hs.2.le
    have h1 := hvan s hsI
    have h2 : 0 ≤ K * s ^ (n + α + 1 + 1) := mul_nonneg hK (pow_pos hs.1 _).le
    have h3 := abs_sub_abs_le_abs_sub (flux n R R' r) (flux n R R' s)
    linarith
  have ht : Tendsto (fun s : ℝ => Λ * s + K * r ^ (n + α + 1 + 1)) (𝓝[>] 0)
      (𝓝 (K * r ^ (n + α + 1 + 1))) := by
    have hc : Continuous fun s : ℝ => Λ * s + K * r ^ (n + α + 1 + 1) := by fun_prop
    have h0 := hc.tendsto 0
    simp only [mul_zero, zero_add] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht hev

/-- One step of the bootstrap: a bound `|R| ≤ M r^α` with `α + 1 < n` improves
to a bound with exponent `α + 1`. -/
theorem bound_step (hn : n ≠ 0) (hr₀ : 0 < r₀)
    (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hode : ∀ r ∈ Ioo 0 r₀,
      R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r = b r * R r)
    (hb : ∀ r ∈ Ioo 0 r₀, |b r| ≤ B)
    (hvan : ∀ s ∈ Ioo 0 r₀, |flux n R R' s| ≤ Λ * s) {α : ℕ} {Mα : ℝ} (hlt : α + 1 < n)
    (hα : ∀ r ∈ Ioo 0 r₀, |R r| ≤ Mα * r ^ α) :
    ∃ M' : ℝ, ∀ r ∈ Ioo 0 r₀, |R r| ≤ M' * r ^ (α + 1) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
  have hmid : r₀ / 2 ∈ Ioo 0 r₀ := ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb _ hmid)
  have hM0 : 0 ≤ Mα :=
    nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hα _ hmid)) (pow_pos hmid.1 α)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = B * Mα / (n + α + 2) := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  have hfl := flux_power_bound hn hr₀ hR hR' hode hb hvan hα
  rw [← hKdef] at hfl
  have hw : ∀ r ∈ Ioo 0 r₀,
      HasDerivAt (fun x => R x / x ^ n) (flux n R R' r / r ^ (2 * n + 1)) r :=
    fun r hr => hasDerivAt_ratio hn hr.1 (hR r hr)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = K * r₀ / (k + 1) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hφ : ∀ r ∈ Ioo 0 r₀, HasDerivAt (fun x : ℝ => -c * (x ^ (k + 1))⁻¹)
      (K * r₀ / r ^ (k + 1 + 1)) r := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    refine (((hasDerivAt_pow (k + 1) r).inv (pow_ne_zero _ hr0)).const_mul (-c)).congr_deriv ?_
    simp only [Nat.add_sub_cancel, hcdef]
    push_cast
    field_simp
    ring
  have hle : ∀ r ∈ Ioo 0 r₀,
      |flux n R R' r / r ^ (2 * n + 1)| ≤ K * r₀ / r ^ (k + 1 + 1) := by
    intro r hr
    have hrp : 0 < r := hr.1
    have e : r ^ (2 * n + 1) = r ^ (n + α + 1 + 1) * r ^ (k + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [abs_div, abs_of_pos (pow_pos hrp _), div_le_div_iff₀ (pow_pos hrp _) (pow_pos hrp _)]
    calc |flux n R R' r| * r ^ (k + 1 + 1)
        ≤ K * r ^ (n + α + 1 + 1) * r ^ (k + 1 + 1) :=
          mul_le_mul_of_nonneg_right (hfl r hr) (pow_pos hrp _).le
      _ = K * r * (r ^ (n + α + 1 + 1) * r ^ (k + 1)) := by ring
      _ ≤ K * r₀ * (r ^ (n + α + 1 + 1) * r ^ (k + 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr.2.le hK) (by positivity)
      _ = K * r₀ * r ^ (2 * n + 1) := by rw [e]
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ℝ, w₀ = |R (r₀ / 2) / (r₀ / 2) ^ n| := ⟨_, rfl⟩
  have hw0 : 0 ≤ w₀ := by rw [hw₀]; exact abs_nonneg _
  have hrest : 0 ≤ w₀ * r₀ ^ (k + 1) + c := by positivity
  refine ⟨w₀ * r₀ ^ (k + 1) + c + 2 * Mα / r₀, fun r hr => ?_⟩
  have hrp : 0 < r := hr.1
  have hpa : 0 < r ^ (α + 1) := pow_pos hrp _
  rcases le_total r (r₀ / 2) with h | h
  · have hv : |R (r₀ / 2) / (r₀ / 2) ^ n - R r / r ^ n| ≤
        -c * ((r₀ / 2) ^ (k + 1))⁻¹ - -c * (r ^ (k + 1))⁻¹ :=
      abs_sub_le_of_deriv_le hw hφ hle hr hmid h
    have h1 : |R r / r ^ n| ≤ w₀ + c * (r ^ (k + 1))⁻¹ := by
      have h2 := abs_sub_abs_le_abs_sub (R r / r ^ n) (R (r₀ / 2) / (r₀ / 2) ^ n)
      rw [abs_sub_comm, ← hw₀] at h2
      have h3 : 0 ≤ c * ((r₀ / 2) ^ (k + 1))⁻¹ := by positivity
      linarith
    have hrn : 0 < r ^ n := pow_pos hrp n
    have e : |R r| = |R r / r ^ n| * r ^ n := by
      rw [abs_div, abs_of_pos hrn, div_mul_cancel₀ _ hrn.ne']
    have en : r ^ n = r ^ (α + 1) * r ^ (k + 1) := by
      rw [← pow_add]
      congr 1
    have hpk : r ^ (k + 1) ≤ r₀ ^ (k + 1) := pow_le_pow_left₀ hrp.le hr.2.le _
    rw [e]
    calc |R r / r ^ n| * r ^ n ≤ (w₀ + c * (r ^ (k + 1))⁻¹) * r ^ n :=
          mul_le_mul_of_nonneg_right h1 hrn.le
      _ = (w₀ * r ^ (k + 1) + c) * r ^ (α + 1) := by
          rw [en]
          field_simp
      _ ≤ (w₀ * r₀ ^ (k + 1) + c) * r ^ (α + 1) :=
          mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hpk hw0]) hpa.le
      _ ≤ (w₀ * r₀ ^ (k + 1) + c + 2 * Mα / r₀) * r ^ (α + 1) :=
          mul_le_mul_of_nonneg_right (by linarith [show 0 ≤ 2 * Mα / r₀ by positivity]) hpa.le
  · have h1 := hα r hr
    have h2 : 1 ≤ 2 / r₀ * r := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr₀]
      linarith
    have h3 : 0 ≤ Mα * r ^ α := mul_nonneg hM0 (pow_pos hrp α).le
    calc |R r| ≤ Mα * r ^ α := h1
      _ ≤ Mα * r ^ α * (2 / r₀ * r) := le_mul_of_one_le_right h3 h2
      _ = 2 * Mα / r₀ * r ^ (α + 1) := by
          rw [pow_succ]
          ring
      _ ≤ (w₀ * r₀ ^ (k + 1) + c + 2 * Mα / r₀) * r ^ (α + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) hpa.le

/-- The last step of the bootstrap: a bound `|R| ≤ M r^{n-1}` gives the
regular-branch bound `|R| ≤ W r^n`. -/
theorem bound_final (hn : n ≠ 0) (hr₀ : 0 < r₀)
    (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hode : ∀ r ∈ Ioo 0 r₀,
      R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r = b r * R r)
    (hb : ∀ r ∈ Ioo 0 r₀, |b r| ≤ B)
    (hvan : ∀ s ∈ Ioo 0 r₀, |flux n R R' s| ≤ Λ * s) {Mα : ℝ}
    (hα : ∀ r ∈ Ioo 0 r₀, |R r| ≤ Mα * r ^ (n - 1)) :
    ∃ W : ℝ, ∀ r ∈ Ioo 0 r₀, |R r| ≤ W * r ^ n := by
  have hmid : r₀ / 2 ∈ Ioo 0 r₀ := ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb _ hmid)
  have hM0 : 0 ≤ Mα :=
    nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hα _ hmid)) (pow_pos hmid.1 _)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = B * Mα / (n + (n - 1 : ℕ) + 2) := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  have hfl := flux_power_bound hn hr₀ hR hR' hode hb hvan hα
  rw [← hKdef] at hfl
  have e : n + (n - 1) + 1 + 1 = 2 * n + 1 := by omega
  have hw : ∀ r ∈ Ioo 0 r₀,
      HasDerivAt (fun x => R x / x ^ n) (flux n R R' r / r ^ (2 * n + 1)) r :=
    fun r hr => hasDerivAt_ratio hn hr.1 (hR r hr)
  have hle : ∀ r ∈ Ioo 0 r₀, |flux n R R' r / r ^ (2 * n + 1)| ≤ K := by
    intro r hr
    rw [abs_div, abs_of_pos (pow_pos hr.1 _), div_le_iff₀ (pow_pos hr.1 _)]
    have h := hfl r hr
    rw [e] at h
    exact h
  have hφ : ∀ r ∈ Ioo 0 r₀, HasDerivAt (fun x : ℝ => K * x) K r := fun r _ => by
    simpa using (hasDerivAt_id r).const_mul K
  refine ⟨|R (r₀ / 2) / (r₀ / 2) ^ n| + K * r₀, fun r hr => ?_⟩
  have hrp : 0 < r := hr.1
  have hKr : K * r ≤ K * r₀ := mul_le_mul_of_nonneg_left hr.2.le hK
  have hKm : 0 ≤ K * (r₀ / 2) := by positivity
  have hKr0 : 0 ≤ K * r := mul_nonneg hK hrp.le
  have hKm2 : K * (r₀ / 2) ≤ K * r₀ := mul_le_mul_of_nonneg_left (by linarith) hK
  have hwr : |R r / r ^ n - R (r₀ / 2) / (r₀ / 2) ^ n| ≤ K * r₀ := by
    rcases le_total r (r₀ / 2) with h | h
    · have hv : |R (r₀ / 2) / (r₀ / 2) ^ n - R r / r ^ n| ≤ K * (r₀ / 2) - K * r :=
        abs_sub_le_of_deriv_le hw hφ hle hr hmid h
      rw [abs_sub_comm]
      linarith
    · have hv : |R r / r ^ n - R (r₀ / 2) / (r₀ / 2) ^ n| ≤ K * r - K * (r₀ / 2) :=
        abs_sub_le_of_deriv_le hw hφ hle hmid hr h
      linarith
  have h2 := abs_sub_abs_le_abs_sub (R r / r ^ n) (R (r₀ / 2) / (r₀ / 2) ^ n)
  have hrn : 0 < r ^ n := pow_pos hrp n
  have e2 : |R r| = |R r / r ^ n| * r ^ n := by
    rw [abs_div, abs_of_pos hrn, div_mul_cancel₀ _ hrn.ne']
  rw [e2]
  exact mul_le_mul_of_nonneg_right (by linarith) hrn.le

variable {E : ℝ}

/-- A finite-energy solution of the radial equation is on the regular
branch. -/
theorem regular_of_finite_energy (hn : n ≠ 0) (hr₀ : 0 < r₀)
    (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hode : ∀ r ∈ Ioo 0 r₀,
      R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r = b r * R r)
    (hb : ∀ r ∈ Ioo 0 r₀, |b r| ≤ B)
    (hE : ∀ r s, 0 < r → r ≤ s → s < r₀ → ∫ ρ in r..s, energyDensity n R R' ρ ≤ E) :
    ∃ W : ℝ, ∀ r ∈ Ioo 0 r₀, |R r| ≤ W * r ^ n := by
  have hM := bounded_of_energy hn hr₀ hR hR' hE
  have hvan := flux_le_linear hn hr₀ hR hR' hode hb hE hM
  have hind : ∀ α : ℕ, α + 1 ≤ n → ∃ Mα : ℝ, ∀ r ∈ Ioo 0 r₀, |R r| ≤ Mα * r ^ α := by
    intro α
    induction α with
    | zero =>
      intro _
      exact ⟨_, fun r hr => by simpa using hM r hr⟩
    | succ α ih =>
      intro h
      obtain ⟨Mα, hα⟩ := ih (by omega)
      exact bound_step hn hr₀ hR hR' hode hb hvan (by omega) hα
  obtain ⟨Mα, hα⟩ := hind (n - 1) (by omega)
  exact bound_final hn hr₀ hR hR' hode hb hvan hα

/-- The finite-energy radial branch has the core asymptotics
`|R - c r^n| ≤ B W / (4 (n + 1)) r^{n+2}`. -/
theorem finite_energy_asymptotics (hn : n ≠ 0) (hr₀ : 0 < r₀)
    (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hode : ∀ r ∈ Ioo 0 r₀,
      R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r = b r * R r)
    (hb : ∀ r ∈ Ioo 0 r₀, |b r| ≤ B)
    (hE : ∀ r s, 0 < r → r ≤ s → s < r₀ → ∫ ρ in r..s, energyDensity n R R' ρ ≤ E) :
    ∃ c W : ℝ, ∀ r ∈ Ioo 0 r₀,
      |R r - c * r ^ n| ≤ B * W / (4 * (n + 1)) * r ^ (n + 2) := by
  obtain ⟨W, hW⟩ := regular_of_finite_energy hn hr₀ hR hR' hode hb hE
  obtain ⟨c, hc⟩ := core_asymptotics hn hr₀ hR hR' hode hb hW
  exact ⟨c, W, hc⟩

end FoliationQM.RadialRegularBranch
