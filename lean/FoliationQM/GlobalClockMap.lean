module

public import FoliationQM.ClockCompatibility
public import FoliationQM.PhaseCircle
public import FoliationQM.GlobalPhaseField

/-!
# Global clock rescaling, winding and degree-one selection

Source: v13 `rem:topological_hbar_lock`. A clock rescaling must descend to an
actual continuous map of the physical circle. We prove that such a map exists
exactly for the positive integer family, is uniquely the corresponding power
map, and is bijective exactly at canonical coupling. Winding is the actual
Mathlib fundamental-group winding number of the image of one positive turn.
Elementary physical winding is an input, not a derived circulation theorem.
No assertion of smooth metric completion is made.
-/
@[expose] public section

namespace FoliationQM.GlobalClockMap

open ClockCompatibility PhaseCircle

/-- A continuous map of physical phase circles implements a clock ratio if
it agrees with the rescaled exponential on every real representative. -/
def Implements (r : ℝ) (F : C(Circle, Circle)) : Prop :=
  ∀ t : ℝ, F (Circle.exp t) = Circle.exp (r * t)

/-- Integer clock ratios descend to the actual continuous circle power map. -/
theorem power_implements (k : ℕ) : Implements (k : ℝ) (power k) :=
  power_exp k

/-- Agreement on all real phase representatives uniquely determines the global map. -/
theorem implements_unique (r : ℝ) (F G : C(Circle, Circle))
    (hF : Implements r F) (hG : Implements r G) : F = G := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨t, rfl⟩ := Circle.exp_surjective q
  exact (hF t).trans (hG t).symm

/-- An actual global map forces elementary-vortex monodromy to be trivial. -/
theorem implements_monodromy (r : ℝ) (F : C(Circle, Circle)) (hF : Implements r F) :
    phase (2 * Real.pi * r) = 1 := by
  have hFone : F 1 = 1 := by simpa using hF 0
  have he : Circle.exp (r * (2 * Real.pi)) = 1 := by
    have h := (hF (2 * Real.pi)).symm
    rwa [Circle.exp_two_pi, hFone] at h
  have hc := congrArg (fun q : Circle => (q : ℂ)) he
  simpa only [Circle.coe_exp, Circle.coe_one, phase, mul_comm r] using hc

/-- Every global implementation of a compatible integer ratio is the power
map, so the choice of local lift cannot introduce another global map. -/
theorem implements_eq_power (hbar heff : ℝ) (k : ℕ)
    (hratio : hbar / heff = (k : ℝ)) (F : C(Circle, Circle))
    (hF : Implements (hbar / heff) F) : F = power k := by
  apply implements_unique (hbar / heff) F (power k) hF
  rw [hratio]
  exact power_implements k

/-- Positive clock rescaling descends to a continuous global circle map
exactly when the elementary exponential monodromy is trivial. -/
theorem exists_implements_iff_monodromy (hbar heff : ℝ)
    (hh : 0 < hbar) (he : 0 < heff) :
    (∃ F : C(Circle, Circle), Implements (hbar / heff) F) ↔
      phase (2 * Real.pi * (hbar / heff)) = 1 := by
  constructor
  · rintro ⟨F, hF⟩
    exact implements_monodromy _ F hF
  · intro hm
    obtain ⟨k, _, hk⟩ := (monodromy_iff_positive_integer hbar heff hh he).1 hm
    refine ⟨power k, ?_⟩
    rw [hk]
    exact power_implements k

/-- Existence of an actual continuous global clock map permits exactly the
positive-integer Fisher coupling family. -/
theorem exists_globalMap_iff_coupling_family (hbar lam : ℝ)
    (hh : 0 < hbar) (hlam : 0 < lam) :
    (∃ F : C(Circle, Circle), Implements (hbar / effectiveHbar lam) F) ↔
      ∃ k : ℕ, 0 < k ∧ lam = hbar ^ 2 / (4 * (k : ℝ) ^ 2) := by
  rw [exists_implements_iff_monodromy hbar (effectiveHbar lam) hh
    (effectiveHbar_pos hlam), monodromy_iff_coupling_family hbar lam hh hlam]

/-- Requiring a bijective implementation adds exactly the ratio-one condition. -/
theorem exists_bijective_implements_iff_ratio_one (hbar heff : ℝ)
    (hh : 0 < hbar) (he : 0 < heff) :
    (∃ F : C(Circle, Circle), Implements (hbar / heff) F ∧ Function.Bijective F) ↔
      hbar / heff = 1 := by
  constructor
  · rintro ⟨F, hF, hb⟩
    obtain ⟨k, hk, hr⟩ := (monodromy_iff_positive_integer hbar heff hh he).1
      (implements_monodromy _ F hF)
    rw [implements_eq_power hbar heff k hr F hF] at hb
    have hkone := (bijective_power_iff k hk).1 hb
    simpa only [hkone, Nat.cast_one] using hr
  · intro hr
    refine ⟨power 1, ?_, (bijective_power_iff 1 (by norm_num)).2 rfl⟩
    rw [hr]
    simpa only [Nat.cast_one] using power_implements 1

/-- The degree-one/bijective global clock requirement selects canonical
coupling; mere existence of a single-valued global map does not. -/
theorem exists_bijective_globalMap_iff_canonical (hbar lam : ℝ)
    (hh : 0 < hbar) (hlam : 0 < lam) :
    (∃ F : C(Circle, Circle), Implements (hbar / effectiveHbar lam) F ∧
      Function.Bijective F) ↔ lam = hbar ^ 2 / 4 := by
  rw [exists_bijective_implements_iff_ratio_one hbar (effectiveHbar lam) hh
    (effectiveHbar_pos hlam), ratio_eq_one_iff_canonical hbar lam hh hlam]

/-- In the compatible family, genuine winding one of the image generator
selects canonical coupling. The winding number is not defined by the ratio. -/
theorem winding_one_iff_canonical (hbar lam : ℝ) (hh : 0 < hbar) (hlam : 0 < lam)
    (k : ℕ) (hratio : hbar / effectiveHbar lam = (k : ℝ)) :
    AddCircle.windingNumber (.of (.mk (imageGeneratorLoop k))) = 1 ↔
      lam = hbar ^ 2 / 4 := by
  rw [windingNumber_imageGeneratorLoop, ← ratio_eq_one_iff_canonical hbar lam hh hlam,
    hratio]
  constructor <;> intro h <;> exact_mod_cast h

/-- The compatible degree-two map is genuinely a covering with winding two
and is not injective, while keeping the original physical circle fixed. -/
theorem degree_two_global_counterexample (hbar : ℝ) (hh : 0 < hbar) :
    Implements (hbar / effectiveHbar (hbar ^ 2 / 16)) (power 2) ∧
    IsCoveringMap (power 2) ∧
    AddCircle.windingNumber (.of (.mk (imageGeneratorLoop 2))) = 2 ∧
    ¬ Function.Injective (power 2) := by
  have hr : hbar / effectiveHbar (hbar ^ 2 / 16) = (2 : ℝ) := by
    convert ratio_family hbar 2 hh (by norm_num) using 1
    norm_num
  refine ⟨?_, isCoveringMap_power 2 (by norm_num), ?_, ?_⟩
  · rw [hr]
    exact power_implements 2
  · exact windingNumber_imageGeneratorLoop 2
  · rw [injective_power_iff 2 (by norm_num)]
    norm_num

end FoliationQM.GlobalClockMap
