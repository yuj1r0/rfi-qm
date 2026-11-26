module

public import FoliationQM.LatticePolarVariation
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Regularized lattice lag-clock rate

Equation 8 of v13 (lines 215–220) replaces the reciprocal of the signed
amplitude in the kinetic term. The potential acts independently of that
substitution. The smooth reciprocal and its exact fractional error allow
comparison both at a node and on regions bounded away from nodes.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeClockRegularization

open LatticeConservation LatticePolarStencil
open scoped ContDiff

/-- The odd reciprocal used in the source clock equation. -/
def reciprocal (ε r : ℝ) : ℝ := r / (r^2 + ε^2)

/-- Fraction of the unregularized kinetic term lost at amplitude `r`. -/
def defectFraction (ε r : ℝ) : ℝ := ε^2 / (r^2 + ε^2)

/-- The regularized denominator is positive whenever the amplitude or width is nonzero. -/
theorem denominator_pos (ε r : ℝ) (hn : r ≠ 0 ∨ ε ≠ 0) : 0 < r^2 + ε^2 := by
  rcases hn with hr | hε
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hr) (sq_nonneg ε)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg r) (sq_pos_of_ne_zero hε)

/-- For every nonzero width the regularized reciprocal is smooth across zero. -/
theorem reciprocal_smooth (ε : ℝ) (hε : ε ≠ 0) : ContDiff ℝ ∞ (reciprocal ε) :=
  contDiff_id.div ((contDiff_id.pow 2).add contDiff_const)
    (fun r => (denominator_pos ε r (Or.inr hε)).ne')

/-- Crossing the origin reverses the sign of the regularized reciprocal. -/
theorem reciprocal_neg (ε r : ℝ) : reciprocal ε (-r) = -reciprocal ε r := by
  simp [reciprocal, neg_div]

/-- The regularized reciprocal vanishes at a node. -/
theorem reciprocal_at_node (ε : ℝ) : reciprocal ε 0 = 0 := by
  simp [reciprocal]

/-- Zero width gives the ordinary reciprocal at a nonzero amplitude. -/
theorem reciprocal_zero_of_ne (r : ℝ) (hr : r ≠ 0) : reciprocal 0 r = r⁻¹ := by
  simp only [reciprocal, zero_pow (by decide : 2 ≠ 0), add_zero]
  field_simp

/-- The defect fraction lies in the unit interval for every real width and amplitude. -/
theorem defectFraction_mem_unitInterval (ε r : ℝ) :
    0 ≤ defectFraction ε r ∧ defectFraction ε r ≤ 1 := by
  constructor
  · unfold defectFraction
    positivity
  · by_cases hn : r ≠ 0 ∨ ε ≠ 0
    · exact (div_le_one (denominator_pos ε r hn)).2 (le_add_of_nonneg_left (sq_nonneg r))
    · push Not at hn
      simp [defectFraction, hn.1, hn.2]

/-- At a node a nonzero width removes the entire kinetic fraction. -/
theorem defectFraction_at_node (ε : ℝ) (hε : ε ≠ 0) : defectFraction ε 0 = 1 := by
  simp [defectFraction, hε]

/-- The retained and lost kinetic fractions add to unity on the regular domain. -/
theorem mul_reciprocal_add_defectFraction (ε r : ℝ) (hn : r ≠ 0 ∨ ε ≠ 0) :
    r * reciprocal ε r + defectFraction ε r = 1 := by
  unfold reciprocal defectFraction
  field_simp [(denominator_pos ε r hn).ne']

/-- At least `δ` away from zero the fractional loss is at most `ε²/δ²`. -/
theorem defectFraction_le_of_abs_ge (ε r δ : ℝ) (hδ : 0 < δ) (hr : δ ≤ |r|) :
    defectFraction ε r ≤ ε^2 / δ^2 := by
  have hsq : δ^2 ≤ r^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hδ.le hr 2
  exact div_le_div_of_nonneg_left (sq_nonneg ε) (sq_pos_of_pos hδ)
    (le_trans hsq (le_add_of_nonneg_right (sq_nonneg ε)))

/-- Source lag-clock velocity at a site with the replicated Neumann neighbors. -/
def lagRate {n : ℕ} (p : MassiveParameters) (h ε : ℝ) (R φ V : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  reciprocal ε (R i) * (p.ellC^2 / (2*h^2)) * radial R φ i - V i / (p.m*p.c^2)

/-- Expanded form of the rate in Eq. 8, retaining both directed cosine corrections. -/
theorem lagRate_source {n : ℕ} (p : MassiveParameters) (h ε : ℝ)
    (R φ V : Fin n → ℝ) (i : Fin n) :
    lagRate p h ε R φ V i =
      (R i / ((R i)^2 + ε^2)) * (p.ellC^2 / (2*h^2)) *
        ((R (nextNode i) - 2*R i + R (prevNode i)) -
          R (nextNode i) * (1 - Real.cos (φ (nextNode i) - φ i)) -
          R (prevNode i) * (1 - Real.cos (φ i - φ (prevNode i)))) -
        V i / (p.m*p.c^2) := by
  unfold lagRate reciprocal radial
  ring

/-- At zero amplitude the regularized lag rate is the negative normalized potential. -/
theorem lagRate_at_node {n : ℕ} (p : MassiveParameters) (h ε : ℝ)
    (R φ V : Fin n → ℝ) (i : Fin n) (hi : R i = 0) :
    lagRate p h ε R φ V i = -(V i / (p.m*p.c^2)) := by
  simp [lagRate, hi, reciprocal_at_node]

/-- Away from nodes, zero width restores division by the signed amplitude. -/
theorem lagRate_zero_of_ne {n : ℕ} (p : MassiveParameters) (h : ℝ)
    (R φ V : Fin n → ℝ) (i : Fin n) (hi : R i ≠ 0) :
    lagRate p h 0 R φ V i =
      (p.ellC^2 / (2*h^2)) * radial R φ i / R i - V i / (p.m*p.c^2) := by
  rw [lagRate, reciprocal_zero_of_ne _ hi, div_eq_mul_inv _ (R i)]
  ring

/-- Away from nodes, the signed change in clock rate is minus the defect
fraction times the unregularized kinetic contribution. -/
theorem lagRate_sub_unregularized {n : ℕ} (p : MassiveParameters) (h ε : ℝ)
    (R φ V : Fin n → ℝ) (i : Fin n) (hi : R i ≠ 0) :
    lagRate p h ε R φ V i - lagRate p h 0 R φ V i =
      -(defectFraction ε (R i)) * ((p.ellC^2 / (2*h^2)) * radial R φ i / R i) := by
  rw [lagRate_zero_of_ne p h R φ V i hi, lagRate]
  have hc := mul_reciprocal_add_defectFraction ε (R i) (Or.inl hi)
  have hr : reciprocal ε (R i) = (1 - defectFraction ε (R i)) / R i :=
    (eq_div_iff hi).2 (by linarith [mul_comm (R i) (reciprocal ε (R i))])
  rw [hr]
  ring

/-- The magnitude of the rate change off a node is exactly the fractional
loss times the magnitude of the unregularized kinetic contribution. -/
theorem abs_lagRate_sub_unregularized {n : ℕ} (p : MassiveParameters) (h ε : ℝ)
    (R φ V : Fin n → ℝ) (i : Fin n) (hi : R i ≠ 0) :
    |lagRate p h ε R φ V i - lagRate p h 0 R φ V i| =
      defectFraction ε (R i) * |(p.ellC^2 / (2*h^2)) * radial R φ i / R i| := by
  rw [lagRate_sub_unregularized p h ε R φ V i hi, abs_mul, abs_neg,
    abs_of_nonneg (defectFraction_mem_unitInterval ε (R i)).1]

end FoliationQM.LatticeClockRegularization
