module

public import FoliationQM.LatticeMeshDefect
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Sampling smooth amplitudes and phases for the lattice-energy defect

The grid has rectangular weights h and sites xᵢ=i h. A derivative bound on
the sampling interval controls the true forward increment, including the
replicated terminal link. This provides mesh-independent constants for Eq. 10.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeSmoothSampling

open WeightedLatticeHamiltonian LatticeConservation Set Asymptotics Filter

/-- Restriction of a real spatial profile to the equally spaced sites. -/
def sample {n : ℕ} (h : ℝ) (f : ℝ → ℝ) (i : Fin n) : ℝ := f ((i.val : ℝ)*h)

private theorem site_mem {n : ℕ} {h L : ℝ} (hh : 0 < h) (hlen : (n : ℝ)*h ≤ L)
    (i : Fin n) : (i.val : ℝ)*h ∈ Icc 0 L := by
  refine ⟨by positivity, ?_⟩
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast i.isLt.le : (i.val : ℝ) ≤ n) hh.le).trans hlen

private theorem site_spacing {n : ℕ} {h : ℝ} (hh : 0 < h) (i : Fin n) :
    |((nextNode i).val : ℝ)*h - (i.val : ℝ)*h| ≤ h := by
  unfold nextNode
  split_ifs
  · simp [Nat.cast_add, add_mul, abs_of_pos hh]
  · simpa using hh.le

/-- On a grid of rectangular length at most L, a derivative bound on [0,L]
gives the required increment bound at every site. -/
theorem sampled_increment {n : ℕ} {h L A : ℝ} (hh : 0 < h) (hA : 0 ≤ A)
    (hlen : (n : ℝ)*h ≤ L) {f : ℝ → ℝ} (hf : ∀ x ∈ Icc 0 L, DifferentiableAt ℝ f x)
    (hder : ∀ x ∈ Icc 0 L, ‖deriv f x‖ ≤ A) (i : Fin n) :
    |forwardDiff (sample h f) i| ≤ A*h := by
  have hs := (convex_Icc (0 : ℝ) L).norm_image_sub_le_of_norm_deriv_le hf hder
    (site_mem hh hlen i) (site_mem hh hlen (nextNode i))
  simp only [Real.norm_eq_abs] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left (site_spacing hh i) hA)

/-- For C¹ amplitude and phase profiles sampled on uniformly bounded intervals,
the arithmetic excess is O(h²) along a refining mesh with arbitrary site potentials. -/
theorem smooth_family_defect {ι : Type*} (l : Filter ι) (p : MassiveParameters)
    (n : ι → ℕ) (h : ι → ℝ) (R φ : ℝ → ℝ) (V : (k : ι) → Fin (n k) → ℝ)
    {L : ℝ} (hR : ContDiff ℝ 1 R) (hφ : ContDiff ℝ 1 φ)
    (hmesh : ∀ᶠ k in l, 0 < h k ∧ (n k : ℝ)*h k ≤ L) :
    (fun k => arithmetic p (h k) (sample (h k) R) (sample (h k) φ) (V k) -
      geometric p (h k) (sample (h k) R) (sample (h k) φ) (V k))
      =O[l] (fun k => (h k)^2) := by
  obtain ⟨A,hA⟩ := (isCompact_Icc (a := 0) (b := L)).exists_bound_of_continuousOn
    hR.continuous_deriv_one.continuousOn
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := 0) (b := L)).exists_bound_of_continuousOn
    hφ.continuous_deriv_one.continuousOn
  apply LatticeMeshDefect.family_defect_isBigO l p n h _ _ V (le_max_right A 0) (le_max_right B 0)
    (L := L)
  filter_upwards [hmesh] with k hk
  refine ⟨hk.1,hk.2,?_,?_⟩
  · exact sampled_increment hk.1 (le_max_right A 0) hk.2 (fun x _ => hR.differentiable_one x)
      (fun x hx => (hA x hx).trans (le_max_left _ _))
  · exact sampled_increment hk.1 (le_max_right B 0) hk.2 (fun x _ => hφ.differentiable_one x)
      (fun x hx => (hB x hx).trans (le_max_left _ _))

end FoliationQM.LatticeSmoothSampling
