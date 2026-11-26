module

public import FoliationQM.HilbertFiberObservables
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Finite coherent tests of the reduced kernel

At any finite family of retained positions the kernel forms a positive
semidefinite matrix. The norms of coherent superpositions determine all its
entries, including their imaginary parts, through complex polarization.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.HilbertReducedKernel

open HilbertFiberObservables
open scoped InnerProductSpace BigOperators ComplexOrder

variable {X H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The kernel is bounded by the product of the two fiber norms. -/
theorem norm_kernel_le (F : X → H) (x y : X) :
    ‖kernel F x y‖ ≤ ‖F x‖ * ‖F y‖ := by
  simpa [kernel, mul_comm] using norm_inner_le_norm (𝕜 := ℂ) (F y) (F x)

/-- Every matrix sampled from the kernel is positive semidefinite, including
when the retained positions repeat. -/
theorem sampled_posSemidef {ι : Type*} [Finite ι] (F : X → H) (x : ι → X) :
    (Matrix.of fun i j => kernel F (x i) (x j)).PosSemidef :=
  (Matrix.posSemidef_gram ℂ (F ∘ x)).transpose

/-- Coherent superposition of finitely many fibers at retained positions. -/
def coherent {n : ℕ} (F : X → H) (x : Fin n → X) (a : Fin n → ℂ) : H :=
  ∑ i, a i • F (x i)

/-- All pairings of finite coherent tests are sums of samples of the reduced kernel. -/
theorem inner_coherent {m n : ℕ} (F : X → H) (x : Fin m → X) (y : Fin n → X)
    (a : Fin m → ℂ) (b : Fin n → ℂ) :
    ⟪coherent F x a, coherent F y b⟫_ℂ =
      ∑ i, ∑ j, star (a i) * (b j * kernel F (y j) (x i)) := by
  unfold coherent
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right]
  rfl

/-- A reduced kernel is completely determined by the strengths of all finite
complex coherent tests. In the reverse direction two-position tests suffice. -/
theorem kernel_eq_iff_coherent_norm (F : X → H) (G : X → K) :
    kernel F = kernel G ↔
      ∀ (n : ℕ) (x : Fin n → X) (a : Fin n → ℂ), ‖coherent F x a‖ = ‖coherent G x a‖ := by
  constructor
  · intro h n x a
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (coherent F x a),
      norm_eq_sqrt_re_inner (𝕜 := ℂ) (coherent G x a), inner_coherent, inner_coherent, h]
  · intro h
    funext x y
    have hp (c : ℂ) : ‖F y + c • F x‖ = ‖G y + c • G x‖ := by
      simpa [coherent, Fin.sum_univ_two] using h 2 ![y, x] ![1, c]
    have h₁ := hp 1
    have h₂ := hp (-1)
    have h₃ := hp (-Complex.I)
    simp only [one_smul] at h₁
    simp only [neg_smul, one_smul, ← sub_eq_add_neg] at h₂ h₃
    simp only [kernel, inner_eq_sum_norm_sq_div_four, RCLike.I_to_complex,
      h₁, h₂, h₃, hp Complex.I]

/-- A single remote linear isometry preserves the strength of every coherent test. -/
theorem norm_coherent_isometry (U : H →ₗᵢ[ℂ] K) (F : X → H) {n : ℕ}
    (x : Fin n → X) (a : Fin n → ℂ) :
    ‖coherent (U ∘ F) x a‖ = ‖coherent F x a‖ := by
  exact (kernel_eq_iff_coherent_norm (U ∘ F) F).mp
    (funext₂ fun i j => kernel_isometry U F i j) n x a

end FoliationQM.HilbertReducedKernel
