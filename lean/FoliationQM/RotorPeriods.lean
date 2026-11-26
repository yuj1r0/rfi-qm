module

public import FoliationQM.PlaneTetrad
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Exact period sets and least positive periods of the plane rotor and tetrad

Sources: v13 `thm:contact_period` (iii), `eq:rotor_compton_evolution`, and
the fixed-plane specialization of `lem:maurer_cartan`. The rotor parameter
is half the physical tetrad angle. The actual rotor has precisely the integer
multiples of two pi as periods; the actual conjugated tetrad has precisely
the integer multiples of pi. Necessity is detected from actual matrix entries,
not from an assumed fundamental-period statement.

The time parametrization theta = omega * t / 2 has exact period sets for every
nonzero real omega. The least-positive-period theorems require omega > 0
and give respectively 4*pi/omega and 2*pi/omega. These statements concern the
fixed plane and the actual matrix-valued functions; physical frequency
specializations and arbitrary initial frames are established separately.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.RotorPeriods
open DiracMatrices PlaneRotor PlaneTetrad

/-- The actual rotor periods are exactly the integer multiples of two pi in its half-angle parameter. -/
theorem rotor_periodic_iff (T : ℝ) :
    Function.Periodic rotor T ↔ ∃ n : ℤ, T = (n : ℝ) * (2 * Real.pi) := by
  constructor
  · intro h
    have he := congrArg (fun A : Mat => (A 0 0).re) h.eq
    have hc : Real.cos T = 1 := by
      simpa only [rotor_diagonal, Matrix.diagonal_apply_eq, Matrix.cons_val_zero,
        Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_self, sub_zero, Real.cos_zero] using he
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff T).mp hc
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact rotor_periodic.int_mul n

private theorem least_positive_of_periodic_iff {β : Type*} (f : ℝ → β) {P : ℝ}
    (hP : 0 < P)
    (hperiod : ∀ T, Function.Periodic f T ↔ ∃ n : ℤ, T = (n : ℝ) * P) :
    IsLeast {T : ℝ | 0 < T ∧ Function.Periodic f T} P := by
  refine ⟨⟨hP, (hperiod P).mpr ⟨1, by simp⟩⟩, ?_⟩
  intro T hT
  obtain ⟨n, rfl⟩ := (hperiod T).mp hT.2
  have hn : 0 < (n : ℝ) := (mul_pos_iff_of_pos_right hP).mp hT.1
  have hn' : (1 : ℤ) ≤ n := by exact Int.add_one_le_iff.mpr (by exact_mod_cast hn)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn'
  nlinarith

/-- The actual matrix rotor has least positive half-angle period two pi. -/
theorem rotor_least_positive_period :
    IsLeast {T : ℝ | 0 < T ∧ Function.Periodic rotor T} (2 * Real.pi) :=
  least_positive_of_periodic_iff rotor (by positivity) rotor_periodic_iff

/-- A nonzero half-rate reparametrization transfers exactly the periods of any actual real-parameter function. -/
theorem periodic_half_rate_iff {β : Type*} (f : ℝ → β) {omega : ℝ}
    (hω : omega ≠ 0) (T : ℝ) :
    Function.Periodic (fun t : ℝ => f (omega * t / 2)) T ↔
      Function.Periodic f (omega * T / 2) := by
  constructor
  · intro h x
    have he := h (2 * x / omega)
    have hleft : omega * (2 * x / omega + T) / 2 = x + omega * T / 2 := by
      field_simp [hω]
    have hright : omega * (2 * x / omega) / 2 = x := by field_simp [hω]
    simpa only [hleft, hright] using he
  · intro h t
    have he := h (omega * t / 2)
    simpa only [mul_add, add_div] using he

/-- At nonzero tetrad angular rate, the actual time-dependent rotor periods are exactly integer multiples of 4*pi/omega. -/
theorem scaled_rotor_periodic_iff {omega : ℝ} (hω : omega ≠ 0) (T : ℝ) :
    Function.Periodic (fun t : ℝ => rotor (omega * t / 2)) T ↔
      ∃ n : ℤ, T = (n : ℝ) * (4 * Real.pi / omega) := by
  rw [periodic_half_rate_iff rotor hω, rotor_periodic_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have he : T = ((n : ℝ) * (4 * Real.pi)) / omega := by
      apply (eq_div_iff hω).mpr
      nlinarith [hn]
    simpa only [mul_div_assoc] using he
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    field_simp [hω]
    ring

/-- At positive tetrad angular rate, the actual rotor has least positive time period 4*pi/omega. -/
theorem scaled_rotor_least_positive_period {omega : ℝ} (hω : 0 < omega) :
    IsLeast {T : ℝ | 0 < T ∧ Function.Periodic (fun t : ℝ => rotor (omega * t / 2)) T}
      (4 * Real.pi / omega) :=
  least_positive_of_periodic_iff _ (by positivity) (scaled_rotor_periodic_iff hω.ne')

/-- The actual conjugated tetrad periods are exactly the integer multiples of pi in its half-angle parameter. -/
theorem tetrad_periodic_iff (T : ℝ) :
    Function.Periodic tetrad T ↔ ∃ n : ℤ, T = (n : ℝ) * Real.pi := by
  constructor
  · intro h
    have he := congrArg (fun A : Fin 4 → Mat => (A 1 0 3).re) h.eq
    have hc : Real.cos (2 * T) = 1 := by
      simpa [tetrad_one_entry, Complex.exp_re] using he
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (2 * T)).mp hc
    refine ⟨n, ?_⟩
    nlinarith [hn]
  · rintro ⟨n, rfl⟩
    exact tetrad_periodic.int_mul n

/-- The actual conjugated tetrad has least positive half-angle period pi. -/
theorem tetrad_least_positive_period :
    IsLeast {T : ℝ | 0 < T ∧ Function.Periodic tetrad T} Real.pi :=
  least_positive_of_periodic_iff tetrad Real.pi_pos tetrad_periodic_iff

/-- At nonzero tetrad angular rate, the actual time-dependent tetrad periods are exactly integer multiples of 2*pi/omega. -/
theorem scaled_tetrad_periodic_iff {omega : ℝ} (hω : omega ≠ 0) (T : ℝ) :
    Function.Periodic (fun t : ℝ => tetrad (omega * t / 2)) T ↔
      ∃ n : ℤ, T = (n : ℝ) * (2 * Real.pi / omega) := by
  rw [periodic_half_rate_iff tetrad hω, tetrad_periodic_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have he : T = ((n : ℝ) * (2 * Real.pi)) / omega := by
      apply (eq_div_iff hω).mpr
      nlinarith [hn]
    simpa only [mul_div_assoc] using he
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    field_simp [hω]

/-- At positive tetrad angular rate, the actual tetrad has least positive time period 2*pi/omega. -/
theorem scaled_tetrad_least_positive_period {omega : ℝ} (hω : 0 < omega) :
    IsLeast {T : ℝ | 0 < T ∧ Function.Periodic (fun t : ℝ => tetrad (omega * t / 2)) T}
      (2 * Real.pi / omega) :=
  least_positive_of_periodic_iff _ (by positivity) (scaled_tetrad_periodic_iff hω.ne')

end FoliationQM.RotorPeriods
