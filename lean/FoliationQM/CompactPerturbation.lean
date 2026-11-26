module

public import FoliationQM.Conventions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform admissibility of compactly supported perturbations

Source: v13 `thm:kahler`, analytic support for the local polar variation
correspondence. A positive continuous density need not have a positive global
lower bound. Compact support of the perturbation supplies the required uniform
parameter interval, by bounding its ratio to the background. The same argument
keeps relative complex perturbations in the principal logarithm chart at one.
-/
@[expose] public section

namespace FoliationQM.CompactPerturbation

variable {X : Type*} [TopologicalSpace X]

/-- Compact support and continuity give one parameter interval on which every
value of a scalar perturbation is uniformly small. -/
theorem exists_uniform_smul_norm_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : X → E} (hf : Continuous f) (hc : HasCompactSupport f)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x, ‖t • f x‖ < r := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  let K := max C 0 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hCK : C ≤ K := by dsimp [K]; linarith [le_max_left C 0]
  refine ⟨r / K, div_pos hr hK, ?_⟩
  intro t ht x
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |t| * ‖f x‖ ≤ |t| * K :=
      mul_le_mul_of_nonneg_left ((hC x).trans hCK) (abs_nonneg t)
    _ < r := (lt_div_iff₀ hK).mp ht

/-- An arbitrary continuous positive background remains positive under every
sufficiently small scalar multiple of a fixed compactly supported perturbation.
No positive lower bound on the background over the whole domain is assumed. -/
theorem exists_pos_affine {ρ a : X → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (ha : Continuous a) (hc : HasCompactSupport a) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x, 0 < ρ x + t * a x := by
  have hnz : ∀ x, ρ x ≠ 0 := fun x => ne_of_gt (hpos x)
  have hcont : Continuous (fun x => a x / ρ x) := ha.div hρ hnz
  have hsupp : HasCompactSupport (fun x => a x / ρ x) := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using hc.mul_right (f' := fun x => (ρ x)⁻¹)
  obtain ⟨ε, hε, hbound⟩ := exists_uniform_smul_norm_lt hcont hsupp (r := 1) zero_lt_one
  refine ⟨ε, hε, ?_⟩
  intro t ht x
  have hb := hbound t ht x
  simp only [smul_eq_mul, Real.norm_eq_abs] at hb
  have hlow := (abs_lt.mp hb).1
  have hp : 0 < ρ x * (1 + t * (a x / ρ x)) := mul_pos (hpos x) (by linarith)
  have heq : ρ x * (1 + t * (a x / ρ x)) = ρ x + t * a x := by
    field_simp [hnz x]
  rwa [heq] at hp

/-- Relative perturbations of a nowhere-zero continuous complex background are
uniformly small for a sufficiently small real parameter. -/
theorem exists_norm_relative_lt_half {ψ η : X → ℂ} (hψ : Continuous ψ)
    (hnz : ∀ x, ψ x ≠ 0) (hη : Continuous η) (hc : HasCompactSupport η) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x, ‖(t : ℂ) * η x / ψ x‖ < 1 / 2 := by
  have hcont : Continuous (fun x => η x / ψ x) := hη.div hψ hnz
  have hsupp : HasCompactSupport (fun x => η x / ψ x) := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using hc.mul_right (f' := fun x => (ψ x)⁻¹)
  obtain ⟨ε, hε, hbound⟩ := exists_uniform_smul_norm_lt hcont hsupp
    (r := 1 / 2) (by norm_num)
  refine ⟨ε, hε, ?_⟩
  intro t ht x
  simpa only [Complex.real_smul, mul_div_assoc] using hbound t ht x

/-- A fixed compactly supported variation has a uniform interval on which its
relative factor lies in the principal logarithm's slit plane. -/
theorem exists_slitPlane_affine_ratio {ψ η : X → ℂ} (hψ : Continuous ψ)
    (hnz : ∀ x, ψ x ≠ 0) (hη : Continuous η) (hc : HasCompactSupport η) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x, 1 + (t : ℂ) * η x / ψ x ∈ Complex.slitPlane := by
  obtain ⟨ε, hε, hbound⟩ := exists_norm_relative_lt_half hψ hnz hη hc
  refine ⟨ε, hε, ?_⟩
  intro t ht x
  exact Complex.mem_slitPlane_of_norm_lt_one ((hbound t ht x).trans (by norm_num))

/-- Nowhere-zero complex fields stay nowhere zero under a sufficiently small
multiple of a fixed continuous compactly supported variation. -/
theorem exists_ne_zero_affine {ψ η : X → ℂ} (hψ : Continuous ψ)
    (hnz : ∀ x, ψ x ≠ 0) (hη : Continuous η) (hc : HasCompactSupport η) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → ∀ x, ψ x + (t : ℂ) * η x ≠ 0 := by
  obtain ⟨ε, hε, hslit⟩ := exists_slitPlane_affine_ratio hψ hnz hη hc
  refine ⟨ε, hε, ?_⟩
  intro t ht x
  have hp := mul_ne_zero (hnz x) (Complex.slitPlane_ne_zero (hslit t ht x))
  have heq : ψ x * (1 + (t : ℂ) * η x / ψ x) = ψ x + (t : ℂ) * η x := by
    field_simp [hnz x]
  rwa [heq] at hp

end FoliationQM.CompactPerturbation
