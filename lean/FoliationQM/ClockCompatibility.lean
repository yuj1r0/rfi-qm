module

public import FoliationQM.MasterMetricAndCone
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Physical-clock monodromy and the positive integer coupling family

Source: v13 `rem:topological_hbar_lock`, including its correction that
single-valuedness permits every positive integer winding multiplier.
The phase is the actual complex exponential from Conventions. Compatibility
below concerns all real representatives of a phase, not a choice of one
global real action. Circle-map degree and bijectivity are separate bridges;
the numerical cone-angle statements do not construct a metric completion.
-/
@[expose] public section

namespace FoliationQM.ClockCompatibility

/-- Auxiliary quantum used to linearize a positive Fisher coupling locally. -/
noncomputable def effectiveHbar (lam : ℝ) : ℝ := 2 * Real.sqrt lam

/-- Positive Fisher coupling gives a strictly positive auxiliary quantum. -/
theorem effectiveHbar_pos {lam : ℝ} (hlam : 0 < lam) :
    0 < effectiveHbar lam := by
  unfold effectiveHbar
  positivity

/-- The exponential identifies exactly integer multiples of the physical
phase period; no integer compatibility is assumed. -/
theorem phase_period_iff_integer (r : ℝ) :
    phase (2 * Real.pi * r) = 1 ↔ ∃ k : ℤ, r = (k : ℝ) := by
  have hphase : phase (2 * Real.pi * r) = 1 ↔
      Circle.exp (2 * Real.pi * r) = 1 := by
    simp only [Circle.ext_iff, Circle.coe_exp, Circle.coe_one, phase]
  rw [hphase, Circle.exp_eq_one]
  apply exists_congr
  intro k
  constructor
  · intro h
    nlinarith [Real.pi_pos]
  · intro h
    rw [h]
    ring

/-- Rescaling every representative of a physical phase is well defined
exactly when the multiplier is an integer. -/
theorem phase_respects_physical_lifts_iff_integer (r : ℝ) :
    (∀ x y : ℝ, phase x = phase y → phase (r * x) = phase (r * y)) ↔
      ∃ k : ℤ, r = (k : ℝ) := by
  constructor
  · intro h
    apply (phase_period_iff_integer r).1
    have hp : phase (2 * Real.pi) = phase 0 := by
      simpa only [mul_one, phase, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
        using (phase_period_iff_integer 1).2 ⟨1, by norm_num⟩
    simpa only [mul_zero, phase, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      mul_comm r] using h (2 * Real.pi) 0 hp
  · rintro ⟨k, rfl⟩ x y h
    have hp (t : ℝ) : phase ((k : ℝ) * t) = phase t ^ k := by
      simp only [phase, Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc,
        Complex.exp_int_mul]
    rw [hp, hp, h]

/-- For positive physical and auxiliary quanta, elementary-vortex monodromy
is trivial exactly for a positive natural-number ratio. -/
theorem monodromy_iff_positive_integer (hbar heff : ℝ)
    (hh : 0 < hbar) (he : 0 < heff) :
    phase (2 * Real.pi * (hbar / heff)) = 1 ↔
      ∃ k : ℕ, 0 < k ∧ hbar / heff = (k : ℝ) := by
  rw [phase_period_iff_integer]
  constructor
  · rintro ⟨k, hk⟩
    have hkpos : (0 : ℝ) < (k : ℝ) := hk ▸ div_pos hh he
    have hkint : (0 : ℤ) < k := by exact_mod_cast hkpos
    have hkn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hkint.le
    refine ⟨k.toNat, by exact_mod_cast hkn ▸ hkint, ?_⟩
    rw [hk]
    exact_mod_cast hkn.symm
  · rintro ⟨k, _, hk⟩
    exact ⟨k, by simpa only [Int.cast_natCast] using hk⟩

/-- Every member of the compatible positive-real parameter family has
positive Fisher coupling. Integer membership is required only for monodromy. -/
theorem coupling_family_pos (hbar k : ℝ) (hh : 0 < hbar) (hk : 0 < k) :
    0 < hbar ^ 2 / (4 * k ^ 2) := by positivity

/-- The auxiliary quantum in the compatible family is the physical quantum
divided by its positive multiplier. -/
theorem effectiveHbar_family (hbar k : ℝ) (hh : 0 < hbar) (hk : 0 < k) :
    effectiveHbar (hbar ^ 2 / (4 * k ^ 2)) = hbar / k := by
  unfold effectiveHbar
  rw [show hbar ^ 2 / (4 * k ^ 2) = (hbar / (2 * k)) ^ 2 by ring,
    Real.sqrt_sq (by positivity : 0 ≤ hbar / (2 * k))]
  ring

/-- The actual quantum ratio equals the multiplier in the compatible family. -/
theorem ratio_family (hbar k : ℝ) (hh : 0 < hbar) (hk : 0 < k) :
    hbar / effectiveHbar (hbar ^ 2 / (4 * k ^ 2)) = k := by
  rw [effectiveHbar_family hbar k hh hk]
  field_simp

/-- For positive parameters, a prescribed positive quantum ratio is
equivalent to the corresponding Fisher coupling, with no sign ambiguity. -/
theorem coupling_family_iff_ratio (hbar lam k : ℝ)
    (hh : 0 < hbar) (hlam : 0 < lam) (hk : 0 < k) :
    lam = hbar ^ 2 / (4 * k ^ 2) ↔ hbar / effectiveHbar lam = k := by
  constructor
  · rintro rfl
    exact ratio_family hbar k hh hk
  · intro h
    have he : effectiveHbar lam ≠ 0 := ne_of_gt (effectiveHbar_pos hlam)
    have hs : (Real.sqrt lam) ^ 2 = lam := Real.sq_sqrt hlam.le
    have hm := (div_eq_iff he).1 h
    apply (eq_div_iff (by positivity : (4 * k ^ 2 : ℝ) ≠ 0)).2
    rw [hm]
    unfold effectiveHbar
    nlinarith [sq_nonneg (k * Real.sqrt lam)]

/-- Trivial monodromy for a positive Fisher coupling allows exactly the
positive integer family, rather than selecting its degree-one member. -/
theorem monodromy_iff_coupling_family (hbar lam : ℝ)
    (hh : 0 < hbar) (hlam : 0 < lam) :
    phase (2 * Real.pi * (hbar / effectiveHbar lam)) = 1 ↔
      ∃ k : ℕ, 0 < k ∧ lam = hbar ^ 2 / (4 * (k : ℝ) ^ 2) := by
  rw [monodromy_iff_positive_integer hbar (effectiveHbar lam) hh
    (effectiveHbar_pos hlam)]
  apply exists_congr
  intro k
  constructor
  · rintro ⟨hk, hr⟩
    exact ⟨hk, (coupling_family_iff_ratio hbar lam k hh hlam (by exact_mod_cast hk)).2 hr⟩
  · rintro ⟨hk, hl⟩
    exact ⟨hk, (coupling_family_iff_ratio hbar lam k hh hlam (by exact_mod_cast hk)).1 hl⟩

/-- The additional ratio-one condition selects the canonical coupling. -/
theorem ratio_eq_one_iff_canonical (hbar lam : ℝ)
    (hh : 0 < hbar) (hlam : 0 < lam) :
    hbar / effectiveHbar lam = 1 ↔ lam = hbar ^ 2 / 4 := by
  simpa only [one_pow, mul_one] using
    (coupling_family_iff_ratio hbar lam 1 hh hlam (by norm_num)).symm

/-- Equality of the physical and auxiliary quanta is the same canonical
condition; single-valuedness alone does not imply this equality. -/
theorem effectiveHbar_eq_iff_canonical (hbar lam : ℝ)
    (hh : 0 < hbar) (hlam : 0 < lam) :
    effectiveHbar lam = hbar ↔ lam = hbar ^ 2 / 4 := by
  rw [← ratio_eq_one_iff_canonical hbar lam hh hlam,
    div_eq_one_iff_eq (ne_of_gt (effectiveHbar_pos hlam))]
  exact eq_comm

/-- The numerical cone angle is the physical period multiplied by the
quantum ratio. This is an exact scalar identity, not a completion theorem. -/
theorem coneAngle_eq_ratio (hbar lam : ℝ) :
    MasterMetricAndCone.coneAngle hbar lam =
      2 * Real.pi * (hbar / effectiveHbar lam) := by
  unfold MasterMetricAndCone.coneAngle effectiveHbar
  ring

/-- Every positive integer family member has trivial monodromy and cone
angle `2πk`, with auxiliary quantum `hbar / k`. -/
theorem integer_family_compatible (hbar : ℝ) (k : ℕ)
    (hh : 0 < hbar) (hk : 0 < k) :
    phase (2 * Real.pi *
      (hbar / effectiveHbar (hbar ^ 2 / (4 * (k : ℝ) ^ 2)))) = 1 ∧
    effectiveHbar (hbar ^ 2 / (4 * (k : ℝ) ^ 2)) = hbar / k ∧
    MasterMetricAndCone.coneAngle hbar (hbar ^ 2 / (4 * (k : ℝ) ^ 2)) =
      2 * Real.pi * k := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨?_, effectiveHbar_family hbar k hh hkreal,
    MasterMetricAndCone.coneAngle_family hbar k hh hkreal⟩
  rw [ratio_family hbar k hh hkreal, phase_period_iff_integer]
  exact ⟨k, by simp⟩

/-- Explicit corrected-source counterexample: `hbar²/16` is single-valued,
has auxiliary quantum `hbar/2` and angle `4π`, and is not canonical. -/
theorem degree_two_counterexample (hbar : ℝ) (hh : 0 < hbar) :
    phase (2 * Real.pi * (hbar / effectiveHbar (hbar ^ 2 / 16))) = 1 ∧
    effectiveHbar (hbar ^ 2 / 16) = hbar / 2 ∧
    MasterMetricAndCone.coneAngle hbar (hbar ^ 2 / 16) = 4 * Real.pi ∧
    hbar ^ 2 / 16 ≠ hbar ^ 2 / 4 := by
  have h := integer_family_compatible hbar 2 hh (by norm_num)
  norm_num at h
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · linarith [h.2.2]
  · nlinarith [sq_pos_of_pos hh]

end FoliationQM.ClockCompatibility
