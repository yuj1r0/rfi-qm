module

public import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.LinearCombination

/-!
# Polarization of the radial normal-coordinate identities

In the derivation of v13 `lem:rnc_half_density`, radial geodesics give
diagonal identities for the connection and its differential. Polarization
recovers the connection's mixed coefficients and the cyclic sum of their
first derivatives. The unbundled lemmas apply to finite coordinate sums.
-/

@[expose] public section
namespace FoliationQM.RNCRadialPolarization

section Additive

variable {E : Type*} [Add E]

/-- A symmetric function additive in two slots vanishes if its diagonal vanishes. -/
theorem bilinear_zero_of_diagonal (B : E → E → ℝ)
    (ha₁ : ∀ u v w, B (u + v) w = B u w + B v w)
    (ha₂ : ∀ u v w, B u (v + w) = B u v + B u w)
    (hsym : ∀ u v, B u v = B v u) (hdiag : ∀ u, B u u = 0) (u v : E) :
    B u v = 0 := by
  have huv := hdiag (u + v)
  simp only [ha₁, ha₂] at huv
  linear_combination (huv - hdiag u - hdiag v + hsym u v) / 2

/-- A function additive in three slots and symmetric in its last two slots
has zero cyclic sum when its diagonal vanishes. -/
theorem cyclic_of_diagonal (T : E → E → E → ℝ)
    (ha₁ : ∀ u v a b, T (u + v) a b = T u a b + T v a b)
    (ha₂ : ∀ a u v b, T a (u + v) b = T a u b + T a v b)
    (ha₃ : ∀ a b u v, T a b (u + v) = T a b u + T a b v)
    (hsym : ∀ a b c, T a b c = T a c b) (hdiag : ∀ u, T u u u = 0) (u v w : E) :
    T u v w + T v w u + T w u v = 0 := by
  have huvw := hdiag (u + v + w)
  have huv := hdiag (u + v)
  have huw := hdiag (u + w)
  have hvw := hdiag (v + w)
  simp only [ha₁, ha₂, ha₃] at huvw huv huw hvw
  linear_combination (huvw - huv - huw - hvw + hdiag u + hdiag v + hdiag w +
    hsym u v w + hsym v w u + hsym w u v) / 2

end Additive

section ContinuousLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A symmetric continuous bilinear form with zero diagonal vanishes. -/
theorem bilinear_eq_zero_of_diagonal (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ u v, B u v = B v u) (hdiag : ∀ u, B u u = 0) :
    B = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact bilinear_zero_of_diagonal (fun a b => B a b)
    (by intros; simp) (by intros; simp) hsym hdiag u v

/-- A continuous trilinear form with symmetric last two slots and zero diagonal
satisfies the cyclic identity for all three directions. -/
theorem cyclic_clm_of_diagonal (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ a b c, T a b c = T a c b) (hdiag : ∀ u, T u u u = 0) (u v w : E) :
    T u v w + T v w u + T w u v = 0 :=
  cyclic_of_diagonal (fun a b c => T a b c)
    (by intros; simp) (by intros; simp) (by intros; simp) hsym hdiag u v w

end ContinuousLinear

end FoliationQM.RNCRadialPolarization
