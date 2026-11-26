module

public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Euclidean rotation rigidity for circle actions

Source: v13 `lem:uniqueness`, supporting the intrinsic completion obstruction.
These are consequences of actual Euclidean isometries, not postulated
linearity or differentiability of an unknown coordinate map. The square of
an origin-preserving plane isometry is a rotation. Every physical circle
element has a square root, so every isometric circle action fixing the origin
acts by complex rotations.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.EuclideanRotationAction

open scoped ComplexConjugate

/-- An actual origin-preserving plane isometry is a rotation or a reflection
followed by a rotation, by Mazur--Ulam and the real-linear classification. -/
theorem rotation_or_reflection (E : ℂ ≃ᵢ ℂ) (hzero : E 0 = 0) :
    ∃ q : Circle, (∀ z, E z = (q : ℂ) * z) ∨
      (∀ z, E z = (q : ℂ) * conj z) := by
  obtain ⟨q, hq | hq⟩ :=
    linear_isometry_complex (E.toRealLinearIsometryEquivOfMapZero hzero)
  · refine ⟨q, Or.inl ?_⟩
    intro z
    exact congrArg (fun f : ℂ ≃ₗᵢ[ℝ] ℂ => f z) hq
  · refine ⟨q, Or.inr ?_⟩
    intro z
    exact congrArg (fun f : ℂ ≃ₗᵢ[ℝ] ℂ => f z) hq

/-- Squaring an origin-preserving plane isometry always gives multiplication
by its value at one; no orientation assumption is needed. -/
theorem square_apply (E : ℂ ≃ᵢ ℂ) (hzero : E 0 = 0) (z : ℂ) :
    E (E z) = E (E 1) * z := by
  obtain ⟨q, hq | hq⟩ := rotation_or_reflection E hzero
  · simp only [hq, mul_one]
    ring
  · simp only [hq, map_mul, map_one, mul_one]
    rw [Complex.conj_conj]
    ring

/-- Every physical phase has a square root within the actual phase circle. -/
theorem exists_square_root (q : Circle) : ∃ r : Circle, r * r = q := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective q
  refine ⟨Circle.exp (t / 2), ?_⟩
  rw [← Circle.exp_add]
  congr 1
  ring

/-- A circle-indexed family of actual origin-preserving isometries satisfying
the group composition law acts by complex rotations. -/
theorem action_apply (T : Circle → ℂ ≃ᵢ ℂ)
    (hzero : ∀ q, T q 0 = 0)
    (hmul : ∀ q r z, T (q * r) z = T q (T r z)) (q : Circle) (z : ℂ) :
    T q z = T q 1 * z := by
  obtain ⟨r, hr⟩ := exists_square_root q
  rw [← hr, hmul, hmul]
  exact square_apply (T r) (hzero r) z

/-- The multiplier of an origin-preserving isometry has unit modulus. -/
theorem norm_action_one (T : Circle → ℂ ≃ᵢ ℂ)
    (hzero : ∀ q, T q 0 = 0) (q : Circle) : ‖T q 1‖ = 1 := by
  have h := (T q).dist_eq 1 0
  simpa only [hzero, dist_zero_right, norm_one] using h

/-- The multipliers form an actual circle homomorphism when the isometries
satisfy the identity and composition laws. -/
def actionCharacter (T : Circle → ℂ ≃ᵢ ℂ)
    (hzero : ∀ q, T q 0 = 0) (hone : ∀ z, T 1 z = z)
    (hmul : ∀ q r z, T (q * r) z = T q (T r z)) : Circle →* Circle where
  toFun q := ⟨T q 1, mem_sphere_zero_iff_norm.mpr (norm_action_one T hzero q)⟩
  map_one' := Subtype.ext (hone 1)
  map_mul' q r := Subtype.ext (by
    change T (q * r) 1 = T q 1 * T r 1
    rw [hmul, action_apply T hzero hmul])

/-- The character value is the actual image of the Euclidean unit vector. -/
theorem actionCharacter_coe (T : Circle → ℂ ≃ᵢ ℂ)
    (hzero : ∀ q, T q 0 = 0) (hone : ∀ z, T 1 z = z)
    (hmul : ∀ q r z, T (q * r) z = T q (T r z)) (q : Circle) :
    (actionCharacter T hzero hone hmul q : ℂ) = T q 1 := rfl

/-- Continuity of the orbit of one gives continuity of the circle character. -/
theorem continuous_actionCharacter (T : Circle → ℂ ≃ᵢ ℂ)
    (hzero : ∀ q, T q 0 = 0) (hone : ∀ z, T 1 z = z)
    (hmul : ∀ q r z, T (q * r) z = T q (T r z))
    (hcont : Continuous (fun q => T q 1)) :
    Continuous (actionCharacter T hzero hone hmul) :=
  hcont.subtype_mk _

/-- Faithfulness of the original isometric action makes its actual character
injective; this is derived using the rotation formula for every point. -/
theorem injective_actionCharacter (T : Circle → ℂ ≃ᵢ ℂ)
    (hzero : ∀ q, T q 0 = 0) (hone : ∀ z, T 1 z = z)
    (hmul : ∀ q r z, T (q * r) z = T q (T r z))
    (hfaithful : ∀ q r, (∀ z, T q z = T r z) → q = r) :
    Function.Injective (actionCharacter T hzero hone hmul) := by
  intro q r h
  apply hfaithful q r
  intro z
  have he : T q 1 = T r 1 := congrArg (fun u : Circle => (u : ℂ)) h
  rw [action_apply T hzero hmul q z, action_apply T hzero hmul r z, he]

end FoliationQM.EuclideanRotationAction
