module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import Mathlib.Tactic.Positivity

/-!
# Global power maps on the physical phase circle

Source: v13 `rem:topological_hbar_lock` and `lem:uniqueness`.

These are maps on the actual unit circle and the actual angle quotient
`AddCircle (2 * π)`. The integer of the image of the fundamental loop is
Mathlib's winding number, defined using the fundamental-group isomorphism;
it is not stipulated to be the exponent. The separate question of smooth
metric completion at zero amplitude is not addressed here.
-/

@[expose] public section

namespace FoliationQM.PhaseCircle

/-- One physical angular period is positive, as required by the winding-number API. -/
instance positivePhysicalPeriod : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The continuous power map on the physical unit circle. -/
noncomputable def power (k : ℕ) : C(Circle, Circle) :=
  ⟨fun q => q ^ k, continuous_id.pow k⟩

/-- The power map is the usual group power at each point. -/
theorem power_apply (k : ℕ) (q : Circle) : power k q = q ^ k := rfl

/-- The angular expression of the global power map is the scaled real lift. -/
theorem power_exp (k : ℕ) (t : ℝ) :
    power k (Circle.exp t) = Circle.exp ((k : ℝ) * t) := by
  simp [power]

/-- Positive integer power maps are actual covering maps of the circle. -/
theorem isCoveringMap_power (k : ℕ) (hk : 0 < k) :
    IsCoveringMap (power k) := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  exact (Circle.isQuotientCoveringMap_npow k).isCoveringMap

/-- Every positive power map covers the whole physical circle. -/
theorem surjective_power (k : ℕ) (hk : 0 < k) :
    Function.Surjective (power k) := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  exact (Circle.isQuotientCoveringMap_npow k).surjective

/-- For higher winding, the first nontrivial root gives an explicit collision. -/
theorem power_firstRoot (k : ℕ) (hk : 0 < k) :
    power k (Circle.exp (2 * Real.pi / k)) = 1 := by
  rw [power_exp]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [mul_div_cancel₀ _ hk0, Circle.exp_two_pi]

/-- For exponent greater than one, the explicit colliding root is not the identity. -/
theorem firstRoot_ne_one (k : ℕ) (hk : 1 < k) :
    Circle.exp (2 * Real.pi / k) ≠ 1 := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hp : 0 < 2 * Real.pi := by positivity
  have hroot : 0 < 2 * Real.pi / k := by positivity
  have hlt : 2 * Real.pi / k < 2 * Real.pi := by
    exact (div_lt_self hp hk1)
  intro heq
  have hinj := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
  have hzero : 2 * Real.pi / k = 0 :=
    hinj ⟨hroot.le, hlt⟩ ⟨le_rfl, hp⟩ (by simpa using heq)
  exact hroot.ne' hzero

/-- A positive integer power map is injective exactly at degree one. -/
theorem injective_power_iff (k : ℕ) (hk : 0 < k) :
    Function.Injective (power k) ↔ k = 1 := by
  constructor
  · intro h
    by_contra hk1
    have hgt : 1 < k := by omega
    have heq : power k (Circle.exp (2 * Real.pi / k)) = power k 1 := by
      rw [power_firstRoot k hk, power_apply, one_pow]
    exact firstRoot_ne_one k hgt (h heq)
  · rintro rfl
    intro a b hab
    simpa only [power_apply, pow_one] using hab

/-- A positive integer power map is bijective exactly at degree one. -/
theorem bijective_power_iff (k : ℕ) (hk : 0 < k) :
    Function.Bijective (power k) ↔ k = 1 := by
  rw [Function.Bijective, injective_power_iff k hk]
  exact and_iff_left (surjective_power k hk)

/-- The corresponding continuous map on the quotient of angles by one physical turn. -/
noncomputable def angularPower (k : ℕ) :
    C(AddCircle (2 * Real.pi), AddCircle (2 * Real.pi)) :=
  ⟨fun q => k • q, continuous_id.nsmul k⟩

/-- The quotient-circle power map is multiplication of angles by the exponent. -/
theorem angularPower_apply (k : ℕ) (q : AddCircle (2 * Real.pi)) :
    angularPower k q = k • q := rfl

/-- The angular quotient map and unit-circle power map commute with the standard homeomorphism. -/
theorem homeomorph_angularPower (k : ℕ) (q : AddCircle (2 * Real.pi)) :
    AddCircle.homeomorphCircle' (angularPower k q) =
      power k (AddCircle.homeomorphCircle' q) := by
  induction q using QuotientAddGroup.induction_on
  simp only [angularPower, ContinuousMap.coe_mk, ← AddCircle.coe_nsmul,
    AddCircle.homeomorphCircle'_apply_mk, power_exp, nsmul_eq_mul]

/-- The image of one positive fundamental turn under the actual quotient-circle map. -/
noncomputable def imageGeneratorLoop (k : ℕ) :
    Path (0 : AddCircle (2 * Real.pi)) 0 :=
  ((AddCircle.zsmulLoop (2 * Real.pi) 0 1).map (angularPower k).continuous).cast
    (by simp [angularPower]) (by simp [angularPower])

/-- The image of the fundamental loop is the standard loop winding `k` times. -/
theorem imageGeneratorLoop_eq (k : ℕ) :
    imageGeneratorLoop k = AddCircle.zsmulLoop (2 * Real.pi) 0 (k : ℤ) := by
  ext t
  change k • (AddCircle.zsmulLoop (2 * Real.pi) 0 1 t) =
    AddCircle.zsmulLoop (2 * Real.pi) 0 (k : ℤ) t
  simp [AddCircle.zsmulLoop]

/-- The actual fundamental-group winding number of the image generator is the exponent. -/
theorem windingNumber_imageGeneratorLoop (k : ℕ) :
    AddCircle.windingNumber (.of (.mk (imageGeneratorLoop k))) = (k : ℤ) := by
  rw [imageGeneratorLoop_eq]
  exact AddCircle.windingNumber_zsmulLoop 0 (k : ℤ)

/-- Equivalently, the induced homomorphism on the actual fundamental group sends
the positive generator to the class with winding number `k`. -/
theorem windingNumber_map_generator (k : ℕ) :
    AddCircle.windingNumber
      (FundamentalGroup.mapOfEq (angularPower k)
        (show angularPower k (0 : AddCircle (2 * Real.pi)) = 0 by simp [angularPower])
        (.of (.mk (AddCircle.zsmulLoop (2 * Real.pi) 0 1)))) = (k : ℤ) := by
  rw [FundamentalGroup.mapOfEq_apply]
  change AddCircle.windingNumber (.of (.mk (imageGeneratorLoop k))) = (k : ℤ)
  exact windingNumber_imageGeneratorLoop k

/-- Positive winding is degree one precisely when the global power map is bijective. -/
theorem windingNumber_eq_one_iff_bijective (k : ℕ) (hk : 0 < k) :
    AddCircle.windingNumber (.of (.mk (imageGeneratorLoop k))) = 1 ↔
      Function.Bijective (power k) := by
  rw [windingNumber_imageGeneratorLoop, bijective_power_iff k hk]
  exact_mod_cast (Iff.rfl : k = 1 ↔ k = 1)

end FoliationQM.PhaseCircle
