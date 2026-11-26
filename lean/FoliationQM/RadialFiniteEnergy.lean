module

public import FoliationQM.RadialCoreAsymptotics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Finite radial energy: boundedness and vanishing flux

Source: v13 `thm:wallstrom` Part(b), "the nontrivial finite-energy radial
branch", component kinds C and D. The radial energy density of an
axisymmetric core of winding `n` is `R'² r + n² R² / r`, the integrand of
`∫ (R'² + n² R²/r²) r dr`. Finite energy is taken in the form that the
integral of this density over every compact subinterval `[r, s]` of
`(0, r₀)` is at most a fixed `E`. For a solution of the radial equation with
`|b| ≤ B` and `n ≥ 1`, finite energy gives

* a bound `|R| ≤ √(R(r₀/2)² + E)` on `(0, r₀)`, and
* a linear bound `|u(s)| ≤ 2 B M r₀^{n+1} s` on the flux
  `u = r^{n+1} R' - n r^n R`, where `M` bounds `|R|`; in particular the flux
  vanishes at the core.

The second statement is what excludes the singular branch `r^{-n}`, whose
flux has a nonzero limit. The regular-branch bound `|R| ≤ W r^n` is derived
from these in a separate module.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RadialFiniteEnergy

open Set Filter MeasureTheory RadialCoreAsymptotics
open scoped Topology

variable {n : ℕ} {R R' R'' b : ℝ → ℝ} {r₀ B E : ℝ}

/-- The radial energy density `R'² r + n² R² / r`. -/
def energyDensity (n : ℕ) (R R' : ℝ → ℝ) (r : ℝ) : ℝ :=
  (R' r) ^ 2 * r + n ^ 2 * (R r) ^ 2 / r

/-- The energy density is nonnegative at positive radius. -/
theorem energyDensity_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ energyDensity n R R' r := by
  unfold energyDensity
  positivity

/-- The energy density of a twice differentiable profile is continuous. -/
theorem continuousOn_energyDensity (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r) :
    ContinuousOn (energyDensity n R R') (Ioo 0 r₀) := by
  have hRc : ContinuousOn R (Ioo 0 r₀) := fun r hr => (hR r hr).continuousAt.continuousWithinAt
  have hR'c : ContinuousOn R' (Ioo 0 r₀) := fun r hr =>
    (hR' r hr).continuousAt.continuousWithinAt
  exact ((hR'c.pow 2).mul continuousOn_id).add
    ((continuousOn_const.mul (hRc.pow 2)).div continuousOn_id fun r hr => hr.1.ne')

/-- The square of the profile varies by at most the energy. -/
theorem sq_sub_sq_le_energy (hn : n ≠ 0) (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hE : ∀ r s, 0 < r → r ≤ s → s < r₀ → ∫ ρ in r..s, energyDensity n R R' ρ ≤ E)
    {r s : ℝ} (hr : r ∈ Ioo 0 r₀) (hs : s ∈ Ioo 0 r₀) (hrs : r ≤ s) :
    |(R s) ^ 2 - (R r) ^ 2| ≤ E := by
  have hc := continuousOn_energyDensity (n := n) hR hR'
  have hint : ∀ c ∈ Ioo 0 r₀, IntervalIntegrable (energyDensity n R R') volume r c := by
    intro c hc'
    refine (hc.mono fun x hx => ?_).intervalIntegrable
    rcases Set.mem_uIcc.mp hx with h | h
    · exact ⟨hr.1.trans_le h.1, h.2.trans_lt hc'.2⟩
    · exact ⟨hc'.1.trans_le h.1, h.2.trans_lt hr.2⟩
  have hφ : ∀ x ∈ Ioo 0 r₀, HasDerivAt (fun y => ∫ ρ in r..y, energyDensity n R R' ρ)
      (energyDensity n R R' x) x := fun x hx =>
    intervalIntegral.integral_hasDerivAt_right (hint x hx)
      (hc.stronglyMeasurableAtFilter isOpen_Ioo x hx) (hc.continuousAt (isOpen_Ioo.mem_nhds hx))
  have hf : ∀ x ∈ Ioo 0 r₀, HasDerivAt (fun y => (R y) ^ 2) (2 * R x * R' x) x := fun x hx =>
    ((hR x hx).pow 2).congr_deriv (by norm_num)
  have hle : ∀ x ∈ Ioo 0 r₀, |2 * R x * R' x| ≤ energyDensity n R R' x := by
    intro x hx
    have hxp : 0 < x := hx.1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have h1 : (R' x) ^ 2 * x + (R x) ^ 2 / x ≤ energyDensity n R R' x := by
      unfold energyDensity
      have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have h : (R x) ^ 2 / x ≤ n ^ 2 * (R x) ^ 2 / x :=
        div_le_div_of_nonneg_right
          (by nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sq_nonneg (R x))]) hxp.le
      linarith
    have hSx : ((R' x) ^ 2 * x + (R x) ^ 2 / x) * x = (R' x * x) ^ 2 + (R x) ^ 2 := by
      field_simp
    have h2 : |2 * R x * R' x| ≤ (R' x) ^ 2 * x + (R x) ^ 2 / x := by
      refine le_of_mul_le_mul_right ?_ hxp
      have e : |2 * R x * R' x| * x = |2 * R x * R' x * x| := by
        rw [abs_mul (2 * R x * R' x) x, abs_of_pos hxp]
      rw [hSx, e, abs_le]
      constructor
      · nlinarith [sq_nonneg (R' x * x + R x)]
      · nlinarith [sq_nonneg (R' x * x - R x)]
    exact h2.trans h1
  have h := abs_sub_le_of_deriv_le hf hφ hle hr hs hrs
  simp only [intervalIntegral.integral_same, sub_zero] at h
  exact h.trans (hE r s hr.1 hrs hs.2)

/-- A finite-energy profile is bounded. -/
theorem bounded_of_energy (hn : n ≠ 0) (hr₀ : 0 < r₀)
    (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hE : ∀ r s, 0 < r → r ≤ s → s < r₀ → ∫ ρ in r..s, energyDensity n R R' ρ ≤ E) :
    ∀ r ∈ Ioo 0 r₀, |R r| ≤ √((R (r₀ / 2)) ^ 2 + E) := by
  intro r hr
  have hmid : r₀ / 2 ∈ Ioo 0 r₀ := ⟨by linarith, by linarith⟩
  refine Real.abs_le_sqrt ?_
  rcases le_total r (r₀ / 2) with h | h
  · have h1 := sq_sub_sq_le_energy hn hR hR' hE hr hmid h
    linarith [(abs_le.mp h1).1]
  · have h1 := sq_sub_sq_le_energy hn hR hR' hE hmid hr h
    linarith [(abs_le.mp h1).2]

/-- The squared flux is controlled by the energy density. -/
theorem flux_sq_le {r : ℝ} (hr : 0 < r) :
    (flux n R R' r) ^ 2 ≤ 2 * r ^ (2 * n + 1) * energyDensity n R R' r := by
  have e1 : flux n R R' r = r ^ n * (r * R' r - n * R r) := by
    simp only [flux]
    ring
  have e2 : 2 * r ^ (2 * n + 1) * energyDensity n R R' r =
      (r ^ n) ^ 2 * (2 * ((r * R' r) ^ 2 + (n * R r) ^ 2)) := by
    simp only [energyDensity]
    field_simp
    ring
  rw [e1, e2, mul_pow]
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (r * R' r + n * R r)])
    (by positivity)

/-- Finite energy forces the flux to vanish linearly at the core. -/
theorem flux_le_linear (hn : n ≠ 0) (hr₀ : 0 < r₀)
    (hR : ∀ r ∈ Ioo 0 r₀, HasDerivAt R (R' r) r)
    (hR' : ∀ r ∈ Ioo 0 r₀, HasDerivAt R' (R'' r) r)
    (hode : ∀ r ∈ Ioo 0 r₀,
      R'' r + r⁻¹ * R' r - (n : ℝ) ^ 2 * (r ^ 2)⁻¹ * R r = b r * R r)
    (hb : ∀ r ∈ Ioo 0 r₀, |b r| ≤ B)
    (hE : ∀ r s, 0 < r → r ≤ s → s < r₀ → ∫ ρ in r..s, energyDensity n R R' ρ ≤ E)
    {M : ℝ} (hM : ∀ r ∈ Ioo 0 r₀, |R r| ≤ M) :
    ∀ s ∈ Ioo 0 r₀, |flux n R R' s| ≤ 2 * (B * M * r₀ ^ (n + 1)) * s := by
  have hmid : r₀ / 2 ∈ Ioo 0 r₀ := ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb _ hmid)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ hmid)
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = B * M * r₀ ^ (n + 1) := ⟨_, rfl⟩
  have hL : 0 ≤ L := by rw [hLdef]; positivity
  rw [← hLdef]
  have hu : ∀ r ∈ Ioo 0 r₀, HasDerivAt (flux n R R') (r ^ (n + 1) * (b r * R r)) r :=
    fun r hr => hasDerivAt_flux hn hR hR' hode hr
  have hφ : ∀ r ∈ Ioo 0 r₀, HasDerivAt (fun x : ℝ => L * x) L r := fun r _ => by
    simpa using (hasDerivAt_id r).const_mul L
  have hle : ∀ r ∈ Ioo 0 r₀, |r ^ (n + 1) * (b r * R r)| ≤ L := by
    intro r hr
    have hrp : 0 < r := hr.1
    rw [abs_mul, abs_mul, abs_of_pos (pow_pos hrp _), hLdef]
    calc r ^ (n + 1) * (|b r| * |R r|) ≤ r₀ ^ (n + 1) * (B * M) :=
          mul_le_mul (pow_le_pow_left₀ hrp.le hr.2.le _)
            (mul_le_mul (hb r hr) (hM r hr) (abs_nonneg _) hB) (by positivity) (by positivity)
      _ = B * M * r₀ ^ (n + 1) := by ring
  intro s hs
  by_contra hcon
  rw [not_le] at hcon
  have hsp : 0 < s := hs.1
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = |flux n R R' s| := ⟨_, rfl⟩
  rw [← hadef] at hcon
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) hcon
  have hlow : ∀ ρ ∈ Ioc 0 s, a / 2 ≤ |flux n R R' ρ| := by
    intro ρ hρ
    have hρI : ρ ∈ Ioo 0 r₀ := ⟨hρ.1, hρ.2.trans_lt hs.2⟩
    have h1 := abs_sub_le_of_deriv_le hu hφ hle hρI hs hρ.2
    have h2 := abs_sub_abs_le_abs_sub (flux n R R' s) (flux n R R' ρ)
    have h3 := mul_nonneg hL hρ.1.le
    rw [← hadef] at h2
    linarith
  have hc := continuousOn_energyDensity (n := n) hR hR'
  have hbound : ∀ ρ₀ ∈ Ioo 0 (s / 2), a ^ 2 ≤ 2 ^ (2 * n + 4) * E * ρ₀ ^ (2 * n) := by
    intro ρ₀ hρ₀
    have hρp : 0 < ρ₀ := hρ₀.1
    have h2ρ : 2 * ρ₀ < s := by linarith [hρ₀.2]
    have hsub : Icc ρ₀ (2 * ρ₀) ⊆ Ioo 0 r₀ := fun x hx =>
      ⟨hρp.trans_le hx.1, (hx.2.trans_lt h2ρ).trans hs.2⟩
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = a ^ 2 / (8 * (2 * ρ₀) ^ (2 * n + 1)) := ⟨_, rfl⟩
    have hpt : ∀ ρ ∈ Icc ρ₀ (2 * ρ₀), c ≤ energyDensity n R R' ρ := by
      intro ρ hρ
      have hρpos : 0 < ρ := hρp.trans_le hρ.1
      have h1 := hlow ρ ⟨hρpos, hρ.2.trans h2ρ.le⟩
      have h2 := flux_sq_le (n := n) (R := R) (R' := R') hρpos
      have h3 : (a / 2) ^ 2 ≤ (flux n R R' ρ) ^ 2 := by
        rw [← sq_abs (flux n R R' ρ)]
        exact pow_le_pow_left₀ (by positivity) h1 2
      have h4 : ρ ^ (2 * n + 1) ≤ (2 * ρ₀) ^ (2 * n + 1) := pow_le_pow_left₀ hρpos.le hρ.2 _
      have he := energyDensity_nonneg (n := n) (R := R) (R' := R') hρpos
      have h5 := mul_le_mul_of_nonneg_right h4 he
      rw [hcdef, div_le_iff₀ (by positivity)]
      nlinarith
    have hint : IntervalIntegrable (energyDensity n R R') volume ρ₀ (2 * ρ₀) :=
      (hc.mono hsub).intervalIntegrable_of_Icc (by linarith)
    have hmono := intervalIntegral.integral_mono_on (by linarith : ρ₀ ≤ 2 * ρ₀)
      (intervalIntegrable_const (c := c)) hint hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hE' := hE ρ₀ (2 * ρ₀) hρp (by linarith) (h2ρ.trans hs.2)
    have h5 : ρ₀ * c ≤ E := by
      have e : 2 * ρ₀ - ρ₀ = ρ₀ := by ring
      rw [e] at hmono
      exact hmono.trans hE'
    have h6 : ρ₀ * c = a ^ 2 / (2 ^ (2 * n + 4) * ρ₀ ^ (2 * n)) := by
      rw [hcdef, mul_pow]
      field_simp
      ring
    rw [h6, div_le_iff₀ (by positivity)] at h5
    calc a ^ 2 ≤ E * (2 ^ (2 * n + 4) * ρ₀ ^ (2 * n)) := h5
      _ = 2 ^ (2 * n + 4) * E * ρ₀ ^ (2 * n) := by ring
  have hev : ∀ᶠ ρ₀ in 𝓝[>] (0 : ℝ), a ^ 2 ≤ 2 ^ (2 * n + 4) * E * ρ₀ ^ (2 * n) := by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < s / 2)] with ρ₀ hρ₀
    exact hbound ρ₀ hρ₀
  have ht : Tendsto (fun ρ₀ : ℝ => 2 ^ (2 * n + 4) * E * ρ₀ ^ (2 * n)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous fun ρ₀ : ℝ => 2 ^ (2 * n + 4) * E * ρ₀ ^ (2 * n) := by fun_prop
    have h0 := hcont.tendsto 0
    have hz : (0 : ℝ) ^ (2 * n) = 0 := zero_pow (by omega)
    simp only [hz, mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hsq := ge_of_tendsto ht hev
  nlinarith

end FoliationQM.RadialFiniteEnergy
